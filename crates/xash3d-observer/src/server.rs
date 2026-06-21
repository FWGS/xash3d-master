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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum TSourceEngineQuery {
    /// `GetServerInfo2Response` or `GetServerInfo2ResponseOld`.
    Any,
    /// `GetServerInfo2ResponseOld`.
    Old,
    /// `GetServerInfo2Response`.
    New,
}

/// Used to select the best info request/response type for a server.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum InfoKind {
    /// Query all.
    All,
    /// Query `GetServerInfoResponse`.
    Xash,
    /// Query `GetServerInfo2Response` or `GetServerInfo2ResponseOld`.
    GoldSrc(TSourceEngineQuery),
}

impl InfoKind {
    fn is_xash(&self) -> bool {
        match self {
            InfoKind::All => true,
            InfoKind::Xash => true,
            InfoKind::GoldSrc(_) => false,
        }
    }

    fn is_gold_src(&self) -> bool {
        match self {
            InfoKind::All => true,
            InfoKind::Xash => false,
            InfoKind::GoldSrc(_) => true,
        }
    }
}

impl From<TSourceEngineQuery> for InfoKind {
    fn from(value: TSourceEngineQuery) -> Self {
        Self::GoldSrc(value)
    }
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
            info_kind: InfoKind::All,
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

    fn set_info_kind(&mut self, info_kind: impl Into<InfoKind>) {
        self.info_kind = info_kind.into();
        debug!("{}: set info kind to {:?}", self.address, self.info_kind);
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

        debug!("{}: query info kind {:?}", self.address, self.info_kind);

        if self.info_kind.is_gold_src() {
            let data = self
                .challenge
                .map(GetServerInfo2::with_challenge)
                .unwrap_or_else(GetServerInfo2::new)
                .encode(buf)
                .unwrap();
            self.send(sock, data)?;
        }

        if self.info_kind.is_xash() {
            let data = GetServerInfo::new(self.protocol).encode(buf).unwrap();
            self.send(sock, data)?;
        }

        Ok(())
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
                InfoKind::All | InfoKind::Xash | InfoKind::GoldSrc(TSourceEngineQuery::Any) => {
                    self.set_info_kind(TSourceEngineQuery::New);
                }
                InfoKind::GoldSrc(TSourceEngineQuery::Old) => {
                    // Remember the response to check if changed next time and start ignoring
                    // responses with the old format.
                    self.set_info_kind(TSourceEngineQuery::New);
                    self.update_raw_info(data);
                    return Ok(None);
                }
                InfoKind::GoldSrc(TSourceEngineQuery::New) => {}
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
                InfoKind::All | InfoKind::Xash => {
                    self.set_info_kind(TSourceEngineQuery::Any);
                }
                InfoKind::GoldSrc(kind) => match kind {
                    TSourceEngineQuery::Any => {
                        self.set_info_kind(TSourceEngineQuery::Old);
                    }
                    TSourceEngineQuery::New => {
                        trace!("{}: ignoring GoldSrc old info response", self.address);
                        return Ok(None);
                    }
                    TSourceEngineQuery::Old => {}
                },
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
            match self.info_kind {
                InfoKind::All | InfoKind::Xash => {}
                InfoKind::GoldSrc(_) => {
                    trace!("{}: ignoring Xash info response", self.address);
                    return Ok(None);
                }
            }

            match GetServerInfoResponse::decode(data) {
                Ok(response) => {
                    // Legacy (protocol=48) response does not have `p` (protocol) key.
                    if response.protocol != 0 && !is_valid_protocol(response.protocol) {
                        trace!("{}: ignoring info with unsupported protocol", self.address);
                        return Ok(None);
                    }

                    self.set_info_kind(InfoKind::Xash);
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
