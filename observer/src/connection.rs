use std::{
    io,
    net::{SocketAddr, UdpSocket},
    time::{Duration, Instant},
};

use xash3d_protocol as proto;

use crate::SERVER_TIMEOUT;

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

    pub fn update_response_time(&mut self) {
        self.response_time = Instant::now();
    }

    pub fn update_raw_info(&mut self, buf: &[u8]) -> bool {
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

    fn query_info(&mut self, sock: &UdpSocket, buf: &mut [u8]) -> io::Result<()> {
        // TODO: send TSource Engine Query
        let packet = proto::game::GetServerInfo {
            protocol: self.protocol,
        };
        let packet = packet.encode(buf).unwrap();
        self.request_time = Instant::now();
        if self.state == ConnectionState::Idle {
            self.state = ConnectionState::WaitingInfo;
        }
        sock.send_to(packet, self.address)?;
        Ok(())
    }

    fn query_players(&mut self, sock: &UdpSocket, buf: &mut [u8]) -> io::Result<()> {
        let packet = proto::game::GetPlayers.encode(buf).unwrap();
        sock.send_to(packet, self.address)?;
        Ok(())
    }

    pub fn query(&mut self, sock: &UdpSocket, buf: &mut [u8]) -> io::Result<()> {
        self.query_info(sock, buf)?;
        if self.players {
            self.query_players(sock, buf)?;
        }
        Ok(())
    }
}
