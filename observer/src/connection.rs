use std::{
    io,
    net::SocketAddr,
    time::{Duration, Instant},
};

use xash3d_protocol::{
    self as proto,
    server::{GetChallengeResponse, GetPlayersResponse, GetServerInfoResponse},
    Error as ProtocolError,
};

use crate::{
    event::{Event, InternalEvent, ServerInfo, ServerPlayers},
    net::Socket,
    SERVER_TIMEOUT,
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
    challenge: u32,
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
            challenge: u32::MAX,
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

    pub fn request_time(&self) -> Instant {
        self.request_time
    }

    pub fn ping(&self) -> Duration {
        self.response_time.duration_since(self.request_time)
    }

    fn send(&self, sock: &Socket, data: &[u8]) -> io::Result<()> {
        sock.send_to(data, self.address)?;
        Ok(())
    }

    fn query_info(&mut self, sock: &Socket, buf: &mut [u8]) -> io::Result<()> {
        // TODO: send TSource Engine Query
        let packet = proto::game::GetServerInfo {
            protocol: self.protocol,
        };
        let packet = packet.encode(buf).unwrap();
        self.request_time = Instant::now();
        if self.state == ConnectionState::Idle {
            self.state = ConnectionState::WaitingInfo;
        }
        self.send(sock, packet)
    }

    fn query_players(&mut self, sock: &Socket, buf: &mut [u8]) -> io::Result<()> {
        use proto::game::{GetChallenge, GetPlayers};

        self.wait_players = true;

        if let Some(req) = GetPlayers::new(self.challenge) {
            return self.send(sock, req.encode(buf).unwrap());
        }

        let data = GetChallenge::new().encode(buf).unwrap();
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
    ) -> io::Result<Option<InternalEvent<'a>>> {
        if let Ok(response) = GetChallengeResponse::decode(data) {
            self.challenge = response.challenge;

            // repeat request
            if self.wait_players {
                let mut buffer = [0; 32];
                self.query_players(sock, &mut buffer)?;
            }

            return Ok(None);
        }

        if let Ok(response) = GetPlayersResponse::decode(data) {
            if !self.wait_players {
                // unexpected response
                return Ok(None);
            }

            self.wait_players = false;
            let players = ServerPlayers::new(response);
            return Ok(Some(Event::ServerPlayers(self.address, players).into()));
        }

        match GetServerInfoResponse::decode(data) {
            Ok(response) => {
                self.update_response_time();
                let info = ServerInfo {
                    server: self.address,
                    ping: self.ping(),
                    new: self.state() == ConnectionState::ProtocolDetection,
                    changed: self.update_raw_info(data),
                    response,
                };
                Ok(Some(Event::ServerInfo(info).into()))
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
                    Ok(Some(InternalEvent::ServerInvalidProtocol(
                        self.address,
                        self.request_time().elapsed(),
                    )))
                }
            }
            Err(error) => Ok(Some(InternalEvent::ServerInvalidPacket(
                self.address,
                self.request_time().elapsed(),
                data,
                error,
            ))),
        }
    }
}
