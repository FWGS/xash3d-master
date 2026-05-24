#[cfg(test)]
mod tests;

use std::{
    cmp::Eq,
    collections::hash_map,
    fmt::{self, Display},
    hash::Hash,
    io,
    net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6, ToSocketAddrs},
    str::{self, FromStr},
    sync::{Arc, RwLock},
};

use ahash::AHashSet as HashSet;
use blake2b_simd::Params;
use fastrand::Rng;
use mio::net::UdpSocket;
use thiserror::Error;
use xash3d_protocol::{
    admin,
    filter::{Filter, FilterFlags, Version},
    game::{self, QueryServers},
    master::{self, ServerAddress},
    server,
    wrappers::Str,
    Error as ProtocolError,
};

use crate::{
    config::{Config, MasterConfig},
    hash_map::{Timed, TimedHashMap},
    signals::SignalFlags,
    stats::Stats,
    str_arr::StrArr,
};

type ServerInfo = xash3d_protocol::ServerInfo<Box<[u8]>>;

pub trait AddrExt: Sized + Eq + Hash + Display + Copy + ToSocketAddrs + ServerAddress {
    type Ip: Eq + Hash + Display + Copy + FromStr;
    type MtuBuffer: AsMut<[u8]>;

    fn extract(addr: SocketAddr) -> Result<Self, SocketAddr>;
    fn ip(&self) -> &Self::Ip;
    fn wrap(self) -> SocketAddr;
    fn mtu_buffer() -> Self::MtuBuffer;

    // /// Returns an uninitialized buffer with MTU length.
    // #[inline(always)]
    // fn mtu_buffer_uninit() -> Self::MtuBuffer {
    //     let buf = std::mem::MaybeUninit::uninit();
    //     // SAFETY: used only to encode packets
    //     #[allow(unsafe_code)]
    //     unsafe {
    //         buf.assume_init()
    //     }
    // }
}

impl AddrExt for SocketAddrV4 {
    type Ip = Ipv4Addr;
    type MtuBuffer = [u8; 512];

    fn extract(addr: SocketAddr) -> Result<Self, SocketAddr> {
        if let SocketAddr::V4(addr) = addr {
            Ok(addr)
        } else {
            Err(addr)
        }
    }

    fn ip(&self) -> &Self::Ip {
        SocketAddrV4::ip(self)
    }

    fn wrap(self) -> SocketAddr {
        SocketAddr::V4(self)
    }

    #[inline(always)]
    fn mtu_buffer() -> Self::MtuBuffer {
        [0; 512]
    }
}

impl AddrExt for SocketAddrV6 {
    type Ip = Ipv6Addr;
    type MtuBuffer = [u8; 1280];

    fn extract(addr: SocketAddr) -> Result<Self, SocketAddr> {
        if let SocketAddr::V6(addr) = addr {
            Ok(addr)
        } else {
            Err(addr)
        }
    }

    fn ip(&self) -> &Self::Ip {
        SocketAddrV6::ip(self)
    }

    fn wrap(self) -> SocketAddr {
        SocketAddr::V6(self)
    }

    #[inline(always)]
    fn mtu_buffer() -> Self::MtuBuffer {
        [0; 1280]
    }
}

const GAMEDIR_MAX_SIZE: usize = 31;

#[derive(Error, Debug)]
pub enum UdpServerError {
    #[error("Failed to bind server socket: {0}")]
    BindSocket(io::Error),
    #[error(transparent)]
    Protocol(#[from] ProtocolError),
    #[error(transparent)]
    Io(#[from] io::Error),
    #[error("Admin challenge do not exist")]
    AdminChallengeNotFound,
    #[error("Undefined packet")]
    UndefinedPacket,
    #[error("Rate limit game request")]
    GameRateLimit(u32),
    #[error("Admin limit game request")]
    AdminRateLimit,
    #[error("Ip version changed")]
    IpVersion,
}

fn resolve_socket_addr<A>(addr: A, is_ipv4: bool) -> io::Result<Option<SocketAddr>>
where
    A: ToSocketAddrs,
{
    for i in addr.to_socket_addrs()? {
        if i.is_ipv4() == is_ipv4 {
            return Ok(Some(i));
        }
    }
    Ok(None)
}

fn resolve_update_addr(cfg: &MasterConfig, local_addr: SocketAddr) -> SocketAddr {
    if let Some(s) = cfg.client.update_addr.as_deref() {
        let addr = if !s.contains(':') {
            format!("{s}:{}", local_addr.port())
        } else {
            s.to_owned()
        };

        match resolve_socket_addr(&addr, local_addr.is_ipv4()) {
            Ok(Some(x)) => return x,
            Ok(None) => error!("Update address: failed to resolve IP for \"{}\"", addr),
            Err(e) => error!("Update address: {e}"),
        }
    }
    local_addr
}

pub enum UdpServer {
    V4(UdpServerV4),
    V6(UdpServerV6),
}

impl UdpServer {
    pub fn with_address(cfg: Config, addr: impl Into<SocketAddr>) -> Result<Self, UdpServerError> {
        match addr.into() {
            SocketAddr::V4(addr) => UdpServerV4::new(cfg, addr).map(Self::V4),
            SocketAddr::V6(addr) => UdpServerV6::new(cfg, addr).map(Self::V6),
        }
    }

    pub fn new(cfg: Config) -> Result<Self, UdpServerError> {
        let addr = SocketAddr::new(cfg.master.server.ip, cfg.master.server.port);
        Self::with_address(cfg, addr)
    }

    pub fn try_clone(&self) -> Result<Self, UdpServerError> {
        match self {
            Self::V4(inner) => inner.try_clone().map(Self::V4),
            Self::V6(inner) => inner.try_clone().map(Self::V6),
        }
    }

    pub fn socket_mut(&mut self) -> &mut UdpSocket {
        match self {
            Self::V4(inner) => &mut inner.sock,
            Self::V6(inner) => &mut inner.sock,
        }
    }

    #[allow(dead_code)]
    pub fn local_addr(&self) -> io::Result<SocketAddr> {
        match self {
            Self::V4(inner) => inner.local_addr(),
            Self::V6(inner) => inner.local_addr(),
        }
    }

    pub fn update_config(&mut self, cfg: Config) -> Result<(), UdpServerError> {
        match self {
            Self::V4(inner) => inner.update_config(cfg),
            Self::V6(inner) => inner.update_config(cfg),
        }
    }

    pub fn run(&mut self) -> Result<(), UdpServerError> {
        match self {
            Self::V4(inner) => inner.run(),
            Self::V6(inner) => inner.run(),
        }
    }
}

fn bind(addr: SocketAddr) -> Result<UdpSocket, UdpServerError> {
    fn f(addr: SocketAddr) -> io::Result<UdpSocket> {
        let domain = socket2::Domain::for_address(addr);
        let ty = socket2::Type::DGRAM;
        let protocol = socket2::Protocol::UDP;
        let sock = socket2::Socket::new(domain, ty, Some(protocol))?;
        sock.set_nonblocking(true)?;
        #[cfg(not(windows))]
        sock.set_reuse_port(true)?;
        #[cfg(windows)]
        sock.set_reuse_address(true)?;
        sock.bind(&addr.into())?;
        Ok(UdpSocket::from_std(sock.into()))
    }
    f(addr).map_err(UdpServerError::BindSocket)
}

pub type UdpServerV4 = UdpServerGeneric<SocketAddrV4>;
pub type UdpServerV6 = UdpServerGeneric<SocketAddrV6>;

struct UdpServerState<Addr: AddrExt> {
    update_addr: RwLock<SocketAddr>,

    blocklist: RwLock<HashSet<Addr::Ip>>,

    challenges: RwLock<TimedHashMap<Addr, u32>>,
    servers: RwLock<TimedHashMap<Addr, ServerInfo>>,

    admin_challenges: RwLock<TimedHashMap<Addr::Ip, (u32, u32)>>,
    // rate limit if hash is invalid
    admin_limit: RwLock<TimedHashMap<Addr::Ip, ()>>,

    client_rate_limit: RwLock<TimedHashMap<Addr::Ip, u32>>,
    update_gamedir: RwLock<TimedHashMap<Addr, StrArr<GAMEDIR_MAX_SIZE>>>,
}

impl<Addr: AddrExt> UdpServerState<Addr> {
    fn new(cfg: &Config, addr: &Addr) -> Self {
        let update_addr = resolve_update_addr(&cfg.master, addr.wrap());
        let timeout = &cfg.master.server.timeout;
        Self {
            update_addr: RwLock::new(update_addr),
            blocklist: Default::default(),
            challenges: RwLock::new(TimedHashMap::new(timeout.challenge)),
            servers: RwLock::new(TimedHashMap::new(timeout.server)),
            admin_challenges: RwLock::new(TimedHashMap::new(timeout.challenge)),
            admin_limit: RwLock::new(TimedHashMap::new(timeout.admin)),
            update_gamedir: RwLock::new(TimedHashMap::new(5)),
            client_rate_limit: RwLock::new(TimedHashMap::new(1)),
        }
    }

    fn update_config(&self, cfg: &Config, addr: SocketAddr) {
        *self.update_addr.write().unwrap() = resolve_update_addr(&cfg.master, addr);

        // set timeouts from new config
        let timeout = &cfg.master.server.timeout;
        self.challenges
            .write()
            .unwrap()
            .set_timeout(timeout.challenge);
        self.servers.write().unwrap().set_timeout(timeout.server);
        self.admin_challenges
            .write()
            .unwrap()
            .set_timeout(timeout.challenge);
        self.admin_limit.write().unwrap().set_timeout(timeout.admin);
    }

    fn clear(&self) {
        self.challenges.write().unwrap().clear();
        self.servers.write().unwrap().clear();
        self.admin_challenges.write().unwrap().clear();
        self.admin_limit.write().unwrap().clear();
        self.client_rate_limit.write().unwrap().clear();
        self.update_gamedir.write().unwrap().clear();
    }
}

pub struct UdpServerGeneric<Addr: AddrExt> {
    main: bool,

    cfg: MasterConfig,
    rng: Rng,

    sock: UdpSocket,

    state: Arc<UdpServerState<Addr>>,
    stats: Arc<Stats>,

    // temporary data
    filtered_servers: Vec<Addr>,
    filtered_servers_nat: Vec<Addr>,
}

impl<Addr: AddrExt> UdpServerGeneric<Addr> {
    pub fn new(cfg: Config, addr: Addr) -> Result<Self, UdpServerError> {
        info!("Listen address: {addr}");

        let state = Arc::new(UdpServerState::new(&cfg, &addr));
        let sock = bind(addr.wrap())?;

        Ok(Self {
            main: true,

            sock,
            rng: Rng::new(),
            state,
            stats: Arc::new(Stats::new(cfg.stat)),

            filtered_servers: Default::default(),
            filtered_servers_nat: Default::default(),

            cfg: cfg.master,
        })
    }

    pub fn try_clone(&self) -> Result<Self, UdpServerError> {
        Ok(Self {
            main: false,
            cfg: self.cfg.clone(),
            rng: Rng::new(),
            sock: bind(self.sock.local_addr()?)?,
            state: Arc::clone(&self.state),
            stats: Arc::clone(&self.stats),
            filtered_servers: Vec::new(),
            filtered_servers_nat: Vec::new(),
        })
    }

    pub fn local_addr(&self) -> io::Result<SocketAddr> {
        self.sock.local_addr()
    }

    pub fn update_config(&mut self, cfg: Config) -> Result<(), UdpServerError> {
        let old_addr = self.local_addr()?;
        let new_addr = cfg.master.server.addr();
        if old_addr.is_ipv4() != new_addr.is_ipv4() {
            return Err(UdpServerError::IpVersion);
        }

        if old_addr != new_addr {
            if self.main {
                info!("Listen address: {new_addr}");
            }
            self.sock = bind(new_addr)?;
            if self.main {
                self.clear();
            }
        }

        if self.main {
            self.state.update_config(&cfg, new_addr);
            self.stats.update_config(cfg.stat);
        }

        self.cfg = cfg.master;
        Ok(())
    }

    pub fn run(&mut self) -> Result<(), UdpServerError> {
        let mut buf = [0; 2048];
        while SignalFlags::get().is_empty() {
            let (n, from) = match self.sock.recv_from(&mut buf) {
                Ok(x) => x,
                Err(e) => match e.kind() {
                    io::ErrorKind::Interrupted => break,
                    io::ErrorKind::TimedOut => break,
                    io::ErrorKind::WouldBlock => break,
                    _ => Err(e)?,
                },
            };

            let from = match Addr::extract(from) {
                Ok(from) => from,
                Err(_) => continue,
            };

            if self.is_blocked(from.ip()) {
                continue;
            }

            let src = &buf[..n];
            if let Err(err) = self.handle_packet(&from, src) {
                self.stats.on_error();

                match err {
                    UdpServerError::GameRateLimit(counter) => {
                        trace!("{from}: client rate limit {}", counter);
                    }
                    UdpServerError::AdminRateLimit => {
                        trace!("{from}: admin rate limit");
                    }
                    _ => {
                        trace!("{from}: {err}: {:?}", Str(src));
                    }
                }
            }
        }
        Ok(())
    }

    fn clear(&mut self) {
        info!("Clear all servers and challenges");
        self.state.clear();
        self.stats.clear();
    }

    fn handle_server_challenge(
        &mut self,
        from: &Addr,
        msg: &server::Challenge,
    ) -> Result<(), UdpServerError> {
        let challenge = self.server_challenge_add(*from);
        let resp = master::ChallengeResponse::new(challenge, msg.server_challenge);
        trace!("{from}: send {resp:?}");
        let mut buf = [0; 32];
        let packet = resp.encode(&mut buf)?;
        self.sock.send_to(packet, from.wrap())?;
        Ok(())
    }

    fn handle_server_add(
        &mut self,
        from: &Addr,
        msg: &server::ServerAdd,
    ) -> Result<(), UdpServerError> {
        if msg.version < self.cfg.server.min_version {
            let ver = msg.version;
            let min = self.cfg.server.min_version;
            warn!("{from}: server version is {ver} but minimal allowed is {min}",);
            return Ok(());
        }
        let Some(challenge) = self.server_challenge_get(from) else {
            trace!("{from}: challenge does not exist");
            return Ok(());
        };
        if msg.challenge != challenge {
            let c = msg.challenge;
            warn!("{from}: expected challenge {challenge} but received {c}",);
            return Ok(());
        }
        self.state.challenges.write().unwrap().remove(from);
        self.add_server(*from, ServerInfo::new(msg));
        self.stats.on_server_add();
        // FIXME: outdated servers are also counted
        self.stats
            .servers_count(self.state.servers.read().unwrap().len());
        Ok(())
    }

    fn handle_server_remove(&mut self, _from: &Addr) -> Result<(), UdpServerError> {
        self.stats.on_server_del();
        Ok(())
    }

    fn allow_game_request(&mut self, from: &Addr) -> Result<(), UdpServerError> {
        if self.cfg.server.client_rate_limit > 0 {
            let mut client_rate_limit = self.state.client_rate_limit.write().unwrap();
            let counter = client_rate_limit.entry(*from.ip()).or_default();
            counter.value = counter.value.saturating_add(1);
            if counter.value > self.cfg.server.client_rate_limit {
                return Err(UdpServerError::GameRateLimit(counter.value));
            }
        }
        Ok(())
    }

    fn is_buildnum_valid(&self, from: &Addr, query: &QueryServers<Filter>, min: u32) -> bool {
        if min == 0 {
            return true;
        }
        let Some(buildnum) = query.filter.client_buildnum else {
            trace!("{from}: query rejected, no buildnum field");
            return false;
        };
        if buildnum < min {
            trace!("{from}: query rejected, buildnum {buildnum} is less than {min}");
            return false;
        }
        true
    }

    fn is_query_servers_valid(&self, from: &Addr, query: &QueryServers<Filter>) -> bool {
        // FIXME: if we will ever support XashNT master server protocol, depends whether
        // Unkle Mike would like to use our implementation and server, just hide this
        // whole mess under a "feature" and host a MS for him on a separate port

        let Some(version) = query.filter.clver else {
            // clver field is required
            trace!("{from}: query rejected, no clver field");
            return false;
        };
        if version < self.cfg.client.min_version {
            let min = self.cfg.client.min_version;
            trace!("{from}: query rejected, version {version} is less than {min}");
            return false;
        }

        let buildnum_min = if version < Version::new(0, 20) {
            // old engine has separate buildnum limit
            self.cfg.client.min_old_engine_buildnum
        } else {
            self.cfg.client.min_engine_buildnum
        };
        self.is_buildnum_valid(from, query, buildnum_min)
    }

    fn send_fake_server(
        &self,
        from: &Addr,
        key: Option<u32>,
        update_addr: SocketAddr,
    ) -> Result<(), UdpServerError> {
        trace!("{from}: send fake server ({key:?}, {update_addr})");
        match update_addr {
            SocketAddr::V4(addr) => {
                self.send_server_list(from, key, &[addr])?;
            }
            SocketAddr::V6(addr) => {
                self.send_server_list(from, key, &[addr])?;
            }
        }
        Ok(())
    }

    fn handle_game_query_servers(
        &mut self,
        from: &Addr,
        query: &QueryServers<Filter>,
    ) -> Result<(), UdpServerError> {
        let filter = &query.filter;
        self.stats.on_query_servers();

        if !self.is_query_servers_valid(from, query) {
            self.save_client_gamedir(from, query.filter.gamedir);
            let update_addr = self.state.update_addr.read().unwrap();
            return self.send_fake_server(from, filter.key, *update_addr);
        }

        let Some(client_version) = filter.clver else {
            // checked in is_query_servers_valid
            return Ok(());
        };

        self.filtered_servers.clear();
        self.filtered_servers_nat.clear();

        for (addr, info) in self.state.servers.read().unwrap().iter() {
            // skip if server does not match filter
            if info.region != query.region || !filter.matches(info) {
                continue;
            }

            // skip if client is 0.20 and server protocol is above 48
            if client_version < Version::new(0, 20) && info.protocol != 48 {
                continue;
            }

            self.filtered_servers.push(*addr);

            if info.flags.contains(FilterFlags::NAT) {
                // add server to client announce list
                self.filtered_servers_nat.push(*addr);
            }
        }

        self.send_server_list(from, filter.key, &self.filtered_servers)?;

        // NOTE: If NAT is not set in a filter then by default the client is announced
        // to filtered servers behind NAT.
        if !self.filtered_servers_nat.is_empty()
            && filter.contains_flags(FilterFlags::NAT).unwrap_or(true)
        {
            self.send_client_to_nat_servers(from, &self.filtered_servers_nat)?;
        }

        Ok(())
    }

    fn save_client_gamedir(&mut self, from: &Addr, gamedir: Option<Str<&[u8]>>) {
        let err_msg = "failed to save gamedir for update message";
        let Some(gamedir) = gamedir else {
            trace!("{from}: {err_msg}, gamedir is none");
            return;
        };
        let Some(gamedir) = StrArr::new(&gamedir) else {
            trace!("{from}: {err_msg}, gamedir is invalid {gamedir:?}");
            return;
        };
        self.state
            .update_gamedir
            .write()
            .unwrap()
            .insert(*from, gamedir);
    }

    fn handle_game_get_server_info(
        &mut self,
        from: &Addr,
        msg: &game::GetServerInfo,
    ) -> Result<(), UdpServerError> {
        let gamedir = self.state.update_gamedir.write().unwrap().remove(from);
        let resp = server::GetServerInfoResponse {
            map: Str(self.cfg.client.update_map.as_bytes()),
            host: Str(self.cfg.client.update_title.as_bytes()),
            protocol: msg.protocol,
            dm: true,
            maxcl: 32,
            gamedir: Str(gamedir.as_ref().map_or("valve", |i| i.as_str()).as_bytes()),
            ..Default::default()
        };
        trace!("{from}: send {resp:?}");
        let mut buf = Addr::mtu_buffer();
        let packet = resp.encode(buf.as_mut())?;
        self.sock.send_to(packet, from.wrap())?;
        Ok(())
    }

    fn allow_admin_request(&mut self, from: &Addr) -> Result<(), UdpServerError> {
        if self
            .state
            .admin_limit
            .read()
            .unwrap()
            .get(from.ip())
            .is_none()
        {
            Ok(())
        } else {
            Err(UdpServerError::AdminRateLimit)
        }
    }

    fn handle_admin_challenge(&mut self, from: &Addr) -> Result<(), UdpServerError> {
        let (master_challenge, hash_challenge) = self.admin_challenge_add(from);
        let resp = master::AdminChallengeResponse::new(master_challenge, hash_challenge);
        trace!("{from}: send {resp:?}");
        let mut buf = [0; 64];
        let packet = resp.encode(&mut buf)?;
        self.sock.send_to(packet, from.wrap())?;
        Ok(())
    }

    fn handle_admin_command(
        &mut self,
        from: &Addr,
        msg: &admin::AdminCommand,
    ) -> Result<(), UdpServerError> {
        let entry = *self
            .state
            .admin_challenges
            .read()
            .unwrap()
            .get(from.ip())
            .ok_or(UdpServerError::AdminChallengeNotFound)?;

        if entry.0 != msg.master_challenge {
            trace!("{from}: master challenge is not valid");
            return Ok(());
        }

        let state = Params::new()
            .hash_length(self.cfg.hash.len)
            .key(self.cfg.hash.key.as_bytes())
            .personal(self.cfg.hash.personal.as_bytes())
            .to_state();

        let admin = self.cfg.admin_list.iter().find(|i| {
            let hash = state
                .clone()
                .update(i.password.as_bytes())
                .update(&entry.1.to_le_bytes())
                .finalize();
            *msg.hash == hash.as_bytes()
        });

        match admin {
            Some(admin) => {
                info!("{from}: admin({}), command: {:?}", &admin.name, msg.command);
                self.admin_command(msg.command);
                self.admin_challenge_remove(from);
            }
            None => {
                warn!("{from}: invalid admin hash, command: {:?}", msg.command);
                self.state
                    .admin_limit
                    .write()
                    .unwrap()
                    .insert(*from.ip(), ());
            }
        }

        Ok(())
    }

    #[inline(always)]
    fn dump_message(&self, from: &Addr, msg: impl fmt::Debug) {
        trace!("{from}: recv {msg:?}");
    }

    fn handle_packet(&mut self, from: &Addr, src: &[u8]) -> Result<(), UdpServerError> {
        if src.starts_with(server::Challenge::HEADER) {
            let msg = server::Challenge::decode(src)?;
            self.dump_message(from, &msg);
            return self.handle_server_challenge(from, &msg);
        }

        if src.starts_with(server::ServerAdd::HEADER) {
            let msg = server::ServerAdd::decode(src)?;
            self.dump_message(from, &msg);
            return self.handle_server_add(from, &msg);
        }

        if src.starts_with(server::ServerRemove::HEADER) {
            let msg = server::ServerRemove::decode(src)?;
            self.dump_message(from, &msg);
            return self.handle_server_remove(from);
        }

        if src.starts_with(game::QueryServers::HEADER) {
            self.allow_game_request(from)?;
            let msg = game::QueryServers::decode(src)?;
            self.dump_message(from, &msg);
            return self.handle_game_query_servers(from, &msg);
        }

        if src.starts_with(game::GetServerInfo::HEADER) {
            self.allow_game_request(from)?;
            let msg = game::GetServerInfo::decode(src)?;
            self.dump_message(from, &msg);
            return self.handle_game_get_server_info(from, &msg);
        }

        if src.starts_with(admin::AdminChallenge::HEADER) {
            self.allow_admin_request(from)?;
            let msg = admin::AdminChallenge::decode(src)?;
            self.dump_message(from, &msg);
            return self.handle_admin_challenge(from);
        }

        if src.starts_with(admin::AdminCommand::HEADER) {
            self.allow_admin_request(from)?;
            let msg = admin::AdminCommand::decode_with_hash_len(self.cfg.hash.len, src)?;
            self.dump_message(from, &msg);
            return self.handle_admin_command(from, &msg);
        }

        Err(UdpServerError::UndefinedPacket)
    }

    fn server_challenge_add(&mut self, addr: Addr) -> u32 {
        self.state
            .challenges
            .write()
            .unwrap()
            .entry(addr)
            .or_insert_with(|| Timed::new(self.rng.u32(..)))
            .value
    }

    fn server_challenge_get(&self, addr: &Addr) -> Option<u32> {
        self.state
            .challenges
            .read()
            .unwrap()
            .get(addr)
            .map(|i| i.value)
    }

    fn admin_challenge_add(&mut self, addr: &Addr) -> (u32, u32) {
        let challenge = (self.rng.u32(..), self.rng.u32(..));
        self.state
            .admin_challenges
            .write()
            .unwrap()
            .insert(*addr.ip(), challenge);
        challenge
    }

    fn admin_challenge_remove(&mut self, addr: &Addr) {
        self.state
            .admin_challenges
            .write()
            .unwrap()
            .remove(addr.ip());
    }

    #[allow(dead_code)]
    fn count_all_servers(&self) -> usize {
        self.state.servers.read().unwrap().len()
    }

    fn remove_servers_by_ip(&mut self, ip: &Addr::Ip) {
        self.state
            .servers
            .write()
            .unwrap()
            .retain(|addr, _| addr.ip() != ip);
    }

    fn add_server(&mut self, addr: Addr, server: ServerInfo) {
        let mut servers = self.state.servers.write().unwrap();
        if let hash_map::Entry::Occupied(mut e) = servers.entry(addr) {
            trace!("{addr}: game server updated");
            e.insert(Timed::new(server));
        } else {
            for (i, _) in servers.keys().filter(|i| i.ip() == addr.ip()).enumerate() {
                if i >= usize::from(self.cfg.server.max_servers_per_ip) {
                    trace!("{addr}: game server rejected, max servers per ip");
                    return;
                }
            }
            trace!("{addr}: game server added");
            servers.insert(addr, server);
        }
    }

    fn send_server_list<A, S>(
        &self,
        to: &A,
        key: Option<u32>,
        servers: &[S],
    ) -> Result<(), UdpServerError>
    where
        A: AddrExt,
        S: ServerAddress,
    {
        let list = master::QueryServersResponse::new(key);
        let mut buf = Addr::mtu_buffer();
        let mut offset = 0;
        loop {
            let (packet, count) = list.encode(buf.as_mut(), &servers[offset..])?;
            self.sock.send_to(packet, to.wrap())?;
            offset += count;
            if offset >= servers.len() {
                break;
            }
        }
        Ok(())
    }

    fn send_client_to_nat_servers(
        &self,
        to: &Addr,
        servers: &[Addr],
    ) -> Result<(), UdpServerError> {
        let mut buf = [0; 64];
        let packet = master::ClientAnnounce::new(to.wrap()).encode(&mut buf)?;
        for i in servers {
            self.sock.send_to(packet, i.wrap())?;
        }
        Ok(())
    }

    #[inline]
    fn is_blocked(&self, ip: &Addr::Ip) -> bool {
        self.state.blocklist.read().unwrap().contains(ip)
    }

    fn admin_command(&mut self, cmd: &str) {
        let args: Vec<_> = cmd.split(' ').collect();

        fn helper<Addr, F>(args: &[&str], mut op: F)
        where
            Addr: AddrExt,
            F: FnMut(&str, Addr::Ip),
        {
            let iter = args.iter().map(|i| (i, i.parse::<Addr::Ip>()));
            for (i, ip) in iter {
                match ip {
                    Ok(ip) => op(i, ip),
                    Err(_) => warn!("invalid ip: {i}"),
                }
            }
        }

        match args[0] {
            "ban" => {
                helper::<Addr, _>(&args[1..], |_, ip| {
                    if self.state.blocklist.write().unwrap().insert(ip) {
                        info!("ban ip: {ip}");

                        self.remove_servers_by_ip(&ip);
                    }
                });
            }
            "unban" => {
                helper::<Addr, _>(&args[1..], |_, ip| {
                    if self.state.blocklist.write().unwrap().remove(&ip) {
                        info!("unban ip: {ip}");
                    }
                });
            }
            _ => {
                warn!("invalid admin command: {}", args[0]);
            }
        }
    }
}
