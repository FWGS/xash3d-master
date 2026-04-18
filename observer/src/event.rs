use std::{
    net::{SocketAddr, SocketAddrV4, SocketAddrV6},
    time::Duration,
};

use xash3d_protocol::{
    master::{QueryServersResponse, QueryServersResponseIter},
    server::{GetPlayersResponse, GetServerInfoResponse},
    Error as ProtocolError,
};

pub struct ServerList<'a> {
    master: SocketAddr,
    response: QueryServersResponse<&'a [u8]>,
}

impl<'a> ServerList<'a> {
    pub(crate) fn new(master: SocketAddr, response: QueryServersResponse<&'a [u8]>) -> Self {
        Self { master, response }
    }

    pub fn master(&self) -> &SocketAddr {
        &self.master
    }

    pub fn iter(&self) -> ServerIter<'a> {
        if self.master.is_ipv4() {
            ServerIter {
                inner: ServerIterInner::V4(self.response.iter()),
            }
        } else {
            ServerIter {
                inner: ServerIterInner::V6(self.response.iter()),
            }
        }
    }
}

// TODO: move to xash3d-protocol?
enum ServerIterInner<'a> {
    V4(QueryServersResponseIter<'a, SocketAddrV4>),
    V6(QueryServersResponseIter<'a, SocketAddrV6>),
}

pub struct ServerIter<'a> {
    inner: ServerIterInner<'a>,
}

impl<'a> Iterator for ServerIter<'a> {
    type Item = SocketAddr;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            ServerIterInner::V4(iter) => iter.next().map(SocketAddr::V4),
            ServerIterInner::V6(iter) => iter.next().map(SocketAddr::V6),
        }
    }
}

pub struct ServerInfo<'a> {
    pub(crate) server: SocketAddr,
    pub(crate) ping: Duration,
    pub(crate) new: bool,
    pub(crate) changed: bool,
    pub(crate) response: GetServerInfoResponse<&'a [u8]>,
}

impl<'a> ServerInfo<'a> {
    pub fn address(&self) -> &SocketAddr {
        &self.server
    }

    pub fn ping(&self) -> Duration {
        self.ping
    }

    pub fn is_changed(&self) -> bool {
        self.changed
    }

    pub fn protocol(&self) -> u8 {
        self.response.protocol
    }

    pub fn host(&self) -> &'a [u8] {
        self.response.host
    }

    pub fn gamedir(&self) -> &'a [u8] {
        self.response.gamedir
    }

    pub fn map(&self) -> &'a [u8] {
        self.response.map
    }

    pub fn clients_count(&self) -> u8 {
        self.response.numcl
    }

    pub fn clients_max(&self) -> u8 {
        self.response.maxcl
    }

    pub fn is_deathmatch(&self) -> bool {
        self.response.dm
    }

    pub fn is_coop(&self) -> bool {
        self.response.coop
    }

    pub fn has_teams(&self) -> bool {
        self.response.team
    }

    pub fn has_password(&self) -> bool {
        self.response.password
    }

    pub fn is_dedicated(&self) -> bool {
        self.response.dedicated
    }
}

pub use xash3d_protocol::server::PlayerInfo;

pub struct PlayerError(());

pub struct ServerPlayers<'a> {
    response: GetPlayersResponse<&'a [u8]>,
}

impl<'a> ServerPlayers<'a> {
    pub(crate) fn new(response: GetPlayersResponse<&'a [u8]>) -> Self {
        Self { response }
    }

    pub fn len(&self) -> usize {
        self.response.players_count() as usize
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns an iterator over players.
    pub fn iter(&self) -> impl Iterator<Item = Result<PlayerInfo<'a>, PlayerError>> {
        self.response
            .players()
            .map(|i| i.map_err(|_| PlayerError(())))
    }
}

#[non_exhaustive]
pub enum Event<'a> {
    Timeout,
    ServerList(ServerList<'a>),
    ServerInfo(ServerInfo<'a>),
    ServerInfoTimeout(SocketAddr),
    ServerPlayers(SocketAddr, ServerPlayers<'a>),
    ServerRemove(SocketAddr),
    MasterInvalidPacket(SocketAddr, &'a [u8]),
    ServerInvalidProtocol(SocketAddr),
    ServerInvalidPacket(SocketAddr, &'a [u8]),
}

/// Extended events for old API.
pub(crate) enum InternalEvent<'a> {
    Stop,
    Event(Event<'a>),
    MasterInvalidPacket(SocketAddr, &'a [u8], ProtocolError),
    ServerInvalidProtocol(SocketAddr, Duration),
    ServerInvalidPacket(SocketAddr, Duration, &'a [u8], ProtocolError),
}

impl<'a> From<Event<'a>> for InternalEvent<'a> {
    fn from(value: Event<'a>) -> Self {
        Self::Event(value)
    }
}
