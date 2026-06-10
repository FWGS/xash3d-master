use std::{
    io,
    net::SocketAddr,
    time::{Duration, Instant},
};

use xash3d_protocol::{
    game::{GetChallenge, GetPlayers, GetServerInfo, GetServerInfo2},
    server::{
        GetChallengeResponse, GetPlayersResponse, GetServerInfo2Response,
        GetServerInfo2ResponseOld, GetServerInfoResponse, PingResponse,
    },
    Error as ProtocolError,
};

use crate::{
    event::{Event, ServerInfo, ServerPlayers},
    net::Socket,
    observer::SERVER_TIMEOUT,
};

fn is_valid_protocol(protocol: u8) -> bool {
    protocol == xash3d_protocol::PROTOCOL_VERSION
        || protocol == xash3d_protocol::PROTOCOL_VERSION - 1
}

/// Used to select the best info request/response type for a server.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum InfoKind {
    /// `GetServerInfoResponse`.
    Info,
    /// `GetServerInfo2Response` or `GetServerInfo2ResponseOld`.
    TSourceEngineQueryAny,
    /// `GetServerInfo2ResponseOld`.
    TSourceEngineQueryOld,
    /// `GetServerInfo2Response`.
    TSourceEngineQueryNew,
}

#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(u8)]
enum ServerState {
    /// Server protocol version is not known yet.
    ProtocolDetection,
    /// No packets is expected from a server.
    Idle,
    /// Waiting for info from a server.
    WaitingInfo,
}

pub struct Server {
    address: SocketAddr,
    protocol: u8,
    players: bool,
    info_kind: InfoKind,
    state: ServerState,
    request_time: Instant,
    response_time: Instant,
    challenge: Option<u32>,
    wait_players: bool,
    data: Vec<u8>,
}

impl Server {
    pub fn new(address: SocketAddr) -> Self {
        let now = Instant::now();
        Self {
            address,
            protocol: xash3d_protocol::PROTOCOL_VERSION,
            players: false,
            info_kind: InfoKind::Info,
            state: ServerState::ProtocolDetection,
            request_time: now,
            response_time: now,
            wait_players: false,
            challenge: None,
            data: Vec::new(),
        }
    }

    pub fn with_players(mut self, players: bool) -> Self {
        self.players = players;
        self
    }

    pub(crate) fn address(&self) -> &SocketAddr {
        &self.address
    }

    pub(crate) fn protocol(&self) -> u8 {
        self.protocol
    }

    pub(crate) fn set_legacy_protocol(&mut self) {
        self.protocol = xash3d_protocol::PROTOCOL_VERSION - 1;
    }

    pub(crate) fn is_idle(&self) -> bool {
        self.state == ServerState::Idle
    }

    pub(crate) fn is_valid(&self, now: Instant) -> bool {
        now.duration_since(self.response_time) < SERVER_TIMEOUT
    }

    fn set_info_kind(&mut self, info_kind: InfoKind) {
        trace!("{}: switch to {info_kind:?}", self.address);
        self.info_kind = info_kind;
    }

    fn update_response_time(&mut self) {
        self.response_time = Instant::now();
    }

    fn update_raw_info(&mut self, buf: &[u8]) -> bool {
        self.state = ServerState::Idle;
        if self.data == buf {
            return false;
        }
        self.data.clear();
        self.data.extend_from_slice(buf);
        true
    }

    pub(crate) fn ping(&self) -> Duration {
        self.response_time.duration_since(self.request_time)
    }

    fn send(&self, sock: &Socket, data: &[u8]) -> io::Result<()> {
        sock.send_to(data, self.address)?;
        Ok(())
    }

    fn query_info(&mut self, sock: &Socket, buf: &mut [u8]) -> io::Result<()> {
        self.request_time = Instant::now();

        if self.state == ServerState::Idle {
            self.state = ServerState::WaitingInfo;
        }

        let data = if InfoKind::Info == self.info_kind {
            GetServerInfo::new(self.protocol).encode(buf).unwrap()
        } else {
            self.challenge
                .map(GetServerInfo2::with_challenge)
                .unwrap_or_else(GetServerInfo2::new)
                .encode(buf)
                .unwrap()
        };

        self.send(sock, data)
    }

    fn query_players(&mut self, sock: &Socket, buf: &mut [u8]) -> io::Result<()> {
        self.wait_players = true;

        let data = if let Some(req) = self.challenge.and_then(GetPlayers::new) {
            req.encode(buf).unwrap()
        } else {
            GetChallenge::new().encode(buf).unwrap()
        };

        self.send(sock, data)
    }

    pub(crate) fn query(&mut self, sock: &Socket, buf: &mut [u8]) -> io::Result<()> {
        self.query_info(sock, buf)?;
        if self.players {
            self.query_players(sock, buf)?;
        }
        Ok(())
    }

    pub(crate) fn handle_packet<'a>(
        &mut self,
        sock: &Socket,
        data: &'a [u8],
    ) -> io::Result<Option<Event<'a>>> {
        // GoldSrc servers may respond with `PingResponse` to `GetServerInfo` request.
        if PingResponse::decode(data).is_ok() {
            if self.info_kind == InfoKind::Info {
                // This server does not support `info` request. Try `TSource Engine Query` info
                // request type.
                self.info_kind = InfoKind::TSourceEngineQueryAny;
                let mut buf = [0; 512];
                self.query_info(sock, &mut buf)?;
            }
            return Ok(None);
        }

        if let Ok(response) = GetChallengeResponse::decode(data) {
            self.challenge = Some(response.challenge);

            // repeat request
            if self.wait_players {
                let mut buffer = [0; 32];
                self.query_players(sock, &mut buffer)?;
            }

            return Ok(None);
        }

        if data.starts_with(GetServerInfo2Response::HEADER) {
            let Ok(response) = GetServerInfo2Response::decode(data) else {
                return Ok(Some(Event::ServerInvalidPacket(self.address, data)));
            };
            trace!("{}: recv info {response:?}", self.address);

            if !is_valid_protocol(response.protocol) {
                trace!("{}: ignoring info with unsupported protocol", self.address);
                return Ok(None);
            }

            match self.info_kind {
                InfoKind::Info | InfoKind::TSourceEngineQueryAny => {
                    self.set_info_kind(InfoKind::TSourceEngineQueryNew);
                }
                InfoKind::TSourceEngineQueryOld => {
                    // Remember the response to check if changed next time and start ignoring
                    // responses with the old format.
                    self.set_info_kind(InfoKind::TSourceEngineQueryNew);
                    self.update_raw_info(data);
                    return Ok(None);
                }
                InfoKind::TSourceEngineQueryNew => {}
            }

            self.update_response_time();
            let changed = self.update_raw_info(data);
            let info = ServerInfo::from_info2(self.address, self.ping(), changed, response);
            return Ok(Some(Event::ServerInfo(info)));
        }

        if data.starts_with(GetServerInfo2ResponseOld::HEADER) {
            let Ok(response) = GetServerInfo2ResponseOld::decode(data) else {
                return Ok(Some(Event::ServerInvalidPacket(self.address, data)));
            };
            trace!("{}: recv info {response:?}", self.address);

            if !is_valid_protocol(response.protocol) {
                trace!("{}: ignoring info with unsupported protocol", self.address);
                return Ok(None);
            }

            match self.info_kind {
                InfoKind::Info => {
                    self.set_info_kind(InfoKind::TSourceEngineQueryAny);
                }
                InfoKind::TSourceEngineQueryAny => {
                    self.set_info_kind(InfoKind::TSourceEngineQueryOld);
                }
                InfoKind::TSourceEngineQueryNew => {
                    trace!("{}: ignoring old info response", self.address);
                    return Ok(None);
                }
                InfoKind::TSourceEngineQueryOld => {}
            }

            self.update_response_time();
            let changed = self.update_raw_info(data);
            let info = ServerInfo::from_info2_old(self.address, self.ping(), changed, response);
            return Ok(Some(Event::ServerInfo(info)));
        }

        if let Ok(response) = GetPlayersResponse::decode(data) {
            if !self.wait_players {
                // unexpected response
                return Ok(None);
            }

            self.wait_players = false;
            let players = ServerPlayers::new(response);
            return Ok(Some(Event::ServerPlayers(self.address, players)));
        }

        if data.starts_with(GetServerInfoResponse::HEADER) {
            if InfoKind::Info != self.info_kind {
                trace!("{}: ignoring info response", self.address);
                return Ok(None);
            }

            match GetServerInfoResponse::decode(data) {
                Ok(response) => {
                    // Legacy (protocol=48) response does not have `p` (protocol) key.
                    if response.protocol != 0 && !is_valid_protocol(response.protocol) {
                        trace!("{}: ignoring info with unsupported protocol", self.address);
                        return Ok(None);
                    }

                    self.update_response_time();
                    let changed = self.update_raw_info(data);
                    let info = ServerInfo::from_info(self.address, self.ping(), changed, response);
                    return Ok(Some(Event::ServerInfo(info)));
                }
                Err(ProtocolError::InvalidProtocolVersion) => {
                    if self.state == ServerState::ProtocolDetection
                        && self.protocol() == xash3d_protocol::PROTOCOL_VERSION
                    {
                        // try legacy protocol version
                        let mut buffer = [0; 512];
                        self.set_legacy_protocol();
                        self.query(sock, &mut buffer)?;
                        return Ok(None);
                    } else {
                        return Ok(Some(Event::ServerInvalidProtocol(self.address)));
                    }
                }
                Err(_) => {}
            }
        }

        Ok(Some(Event::ServerInvalidPacket(self.address, data)))
    }
}
