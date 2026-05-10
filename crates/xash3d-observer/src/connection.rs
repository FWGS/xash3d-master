use std::{
    io,
    net::SocketAddr,
    time::{Duration, Instant},
};

use xash3d_protocol::{
    game::{GetChallenge, GetPlayers, GetServerInfo, GetServerInfo2},
    server::{
        GetChallengeResponse, GetPlayersResponse, GetServerInfo2Response,
        GetServerInfo2ResponseOld, GetServerInfoResponse,
    },
    Error as ProtocolError,
};

use crate::{
    event::{Event, ServerInfo, ServerPlayers},
    net::Socket,
    observer::SERVER_TIMEOUT,
};

#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(u8)]
pub enum ConnectionState {
    /// Server protocol version is not known yet.
    ProtocolDetection,
    /// No packets is expected from a server.
    Idle,
    /// Waiting for info from a server.
    WaitingInfo,
}

pub struct Connection {
    address: SocketAddr,
    protocol: u8,
    players: bool,
    state: ConnectionState,
    request_time: Instant,
    response_time: Instant,
    challenge: Option<u32>,
    wait_players: bool,
    data: Vec<u8>,
}

impl Connection {
    pub fn new(address: SocketAddr, players: bool) -> Self {
        let now = Instant::now();
        Self {
            address,
            protocol: xash3d_protocol::PROTOCOL_VERSION,
            players,
            state: ConnectionState::ProtocolDetection,
            request_time: now,
            response_time: now,
            wait_players: false,
            challenge: None,
            data: Vec::new(),
        }
    }

    pub fn protocol(&self) -> u8 {
        self.protocol
    }

    pub fn set_legacy_protocol(&mut self) {
        self.protocol = xash3d_protocol::PROTOCOL_VERSION - 1;
    }

    pub fn state(&self) -> ConnectionState {
        self.state
    }

    pub fn is_valid(&self, now: Instant) -> bool {
        now.duration_since(self.response_time) < SERVER_TIMEOUT
    }

    fn update_response_time(&mut self) {
        self.response_time = Instant::now();
    }

    fn update_raw_info(&mut self, buf: &[u8]) -> bool {
        self.state = ConnectionState::Idle;
        if self.data == buf {
            return false;
        }
        self.data.clear();
        self.data.extend_from_slice(buf);
        true
    }

    pub fn ping(&self) -> Duration {
        self.response_time.duration_since(self.request_time)
    }

    fn send(&self, sock: &Socket, data: &[u8]) -> io::Result<()> {
        sock.send_to(data, self.address)?;
        Ok(())
    }

    fn query_info(&mut self, sock: &Socket, buf: &mut [u8]) -> io::Result<()> {
        self.request_time = Instant::now();

        if self.state == ConnectionState::Idle {
            self.state = ConnectionState::WaitingInfo;
        }

        if true {
            let req = GetServerInfo::new(self.protocol);
            let data = req.encode(buf).unwrap();
            self.send(sock, data)?;
        }

        // TODO: Xash3D engine has bug and will not respond to this query. Enable only for testing.
        if log_enabled!(log::Level::Trace) {
            let req = self
                .challenge
                .map(GetServerInfo2::with_challenge)
                .unwrap_or_else(GetServerInfo2::new);
            let data = req.encode(buf).unwrap();
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

    pub fn query(&mut self, sock: &Socket, buf: &mut [u8]) -> io::Result<()> {
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
            let response = GetServerInfo2Response::decode(data);
            trace!("recv info {} {response:?}", self.address);
            return Ok(None);
        }

        if data.starts_with(GetServerInfo2ResponseOld::HEADER) {
            let response = GetServerInfo2ResponseOld::decode(data);
            trace!("recv info old {} {response:?}", self.address);
            return Ok(None);
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

        match GetServerInfoResponse::decode(data) {
            Ok(response) => {
                self.update_response_time();
                let info = ServerInfo {
                    server: self.address,
                    ping: self.ping(),
                    changed: self.update_raw_info(data),
                    response,
                };
                Ok(Some(Event::ServerInfo(info)))
            }
            Err(ProtocolError::InvalidProtocolVersion) => {
                if self.state() == ConnectionState::ProtocolDetection
                    && self.protocol() == xash3d_protocol::PROTOCOL_VERSION
                {
                    // try legacy protocol version
                    let mut buffer = [0; 512];
                    self.set_legacy_protocol();
                    self.query(sock, &mut buffer)?;
                    Ok(None)
                } else {
                    Ok(Some(Event::ServerInvalidProtocol(self.address)))
                }
            }
            Err(_) => Ok(Some(Event::ServerInvalidPacket(self.address, data))),
        }
    }
}
