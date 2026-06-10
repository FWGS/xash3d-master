use std::{
    net::{SocketAddr, SocketAddrV4, SocketAddrV6},
    time::Duration,
};

use xash3d_protocol::{
    master::{QueryServersResponse, QueryServersResponseIter},
    server::{
        GetPlayersResponse, GetServerInfo2Response, GetServerInfo2ResponseOld,
        GetServerInfoResponse, ServerType,
    },
};

pub struct ServerList<'a> {
    master: SocketAddr,
    response: QueryServersResponse<'a>,
}

impl<'a> ServerList<'a> {
    pub(crate) fn new(master: SocketAddr, response: QueryServersResponse<'a>) -> Self {
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
    pub(crate) changed: bool,
    pub(crate) response: GetServerInfoResponse<'a>,
}

impl<'a> ServerInfo<'a> {
    pub(crate) fn from_info(
        address: SocketAddr,
        ping: Duration,
        changed: bool,
        response: GetServerInfoResponse<'a>,
    ) -> Self {
        Self {
            server: address,
            ping,
            changed,
            response,
        }
    }

    pub(crate) fn from_info2(
        address: SocketAddr,
        ping: Duration,
        changed: bool,
        response: GetServerInfo2Response<'a>,
    ) -> Self {
        Self {
            server: address,
            ping,
            changed,
            response: GetServerInfoResponse {
                gamedir: response.gamedir,
                map: response.map,
                host: response.host,
                protocol: response.protocol,
                numcl: response.players,
                maxcl: response.max_players,
                dm: false,
                team: false,
                coop: false,
                password: response.password,
                dedicated: response.ty == ServerType::Dedicated,
            },
        }
    }

    pub(crate) fn from_info2_old(
        address: SocketAddr,
        ping: Duration,
        changed: bool,
        response: GetServerInfo2ResponseOld<'a>,
    ) -> Self {
        Self {
            server: address,
            ping,
            changed,
            response: GetServerInfoResponse {
                gamedir: response.gamedir,
                map: response.map,
                host: response.host,
                protocol: response.protocol,
                numcl: response.players,
                maxcl: response.max_players,
                dm: false,
                team: false,
                coop: false,
                password: response.password,
                dedicated: response.ty == ServerType::Dedicated,
            },
        }
    }

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
        self.response.host.as_bytes()
    }

    pub fn gamedir(&self) -> &'a [u8] {
        self.response.gamedir.as_bytes()
    }

    pub fn map(&self) -> &'a [u8] {
        self.response.map.as_bytes()
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
    response: GetPlayersResponse<'a>,
}

impl<'a> ServerPlayers<'a> {
    pub(crate) fn new(response: GetPlayersResponse<'a>) -> Self {
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
