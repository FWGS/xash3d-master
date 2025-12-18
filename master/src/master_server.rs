use std::{
    cmp::Eq,
    collections::hash_map,
    fmt::Display,
    hash::Hash,
    io,
    net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6, ToSocketAddrs, UdpSocket},
    str::{self, FromStr},
    sync::atomic::{AtomicBool, Ordering},
    time::Duration,
};

use ahash::AHashSet as HashSet;
use blake2b_simd::Params;
use fastrand::Rng;
use log::{debug, error, info, trace, warn};
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
    Stats, StrArr,
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
pub enum Error {
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
    #[error("Unexpected packet")]
    UnexpectedPacket,
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

pub enum Master {
    V4(MasterServer<SocketAddrV4>),
    V6(MasterServer<SocketAddrV6>),
}

impl Master {
    pub fn new(cfg: Config) -> Result<Self, Error> {
        match SocketAddr::new(cfg.master.server.ip, cfg.master.server.port) {
            SocketAddr::V4(addr) => MasterServer::new(cfg, addr).map(Self::V4),
            SocketAddr::V6(addr) => MasterServer::new(cfg, addr).map(Self::V6),
        }
    }

    pub fn update_config(&mut self, cfg: Config) -> Result<(), Error> {
        let cfg = match self {
            Self::V4(inner) => inner.update_config(cfg)?,
            Self::V6(inner) => inner.update_config(cfg)?,
        };
        if let Some(cfg) = cfg {
            info!("Server IP version changed, full restart");
            *self = Self::new(cfg)?;
        }
        Ok(())
    }

    pub fn run(&mut self, sig_flag: &AtomicBool) -> Result<(), Error> {
        match self {
            Self::V4(inner) => inner.run(sig_flag),
            Self::V6(inner) => inner.run(sig_flag),
        }
    }
}

pub struct MasterServer<Addr: AddrExt> {
    cfg: MasterConfig,
    rng: Rng,

    sock: UdpSocket,
    challenges: TimedHashMap<Addr, u32>,
    servers: TimedHashMap<Addr, ServerInfo>,

    admin_challenges: TimedHashMap<Addr::Ip, (u32, u32)>,
    // rate limit if hash is invalid
    admin_limit: TimedHashMap<Addr::Ip, ()>,

    update_addr: SocketAddr,
    update_gamedir: TimedHashMap<Addr, StrArr<GAMEDIR_MAX_SIZE>>,
    client_rate_limit: TimedHashMap<Addr::Ip, u32>,

    blocklist: HashSet<Addr::Ip>,

    stats: Stats,

    // temporary data
    filtered_servers: Vec<Addr>,
    filtered_servers_nat: Vec<Addr>,
}

impl<Addr: AddrExt> MasterServer<Addr> {
    pub fn new(cfg: Config, addr: Addr) -> Result<Self, Error> {
        info!("Listen address: {addr}");

        let sock = UdpSocket::bind(addr).map_err(Error::BindSocket)?;
        // make socket interruptable by singals
        sock.set_read_timeout(Some(Duration::from_secs(u32::MAX as u64)))?;

        let update_addr = resolve_update_addr(&cfg.master, addr.wrap());
        let timeout = &cfg.master.server.timeout;

        Ok(Self {
            sock,
            challenges: TimedHashMap::new(timeout.challenge),
            servers: TimedHashMap::new(timeout.server),
            rng: Rng::new(),
            update_addr,
            update_gamedir: TimedHashMap::new(5),
            client_rate_limit: TimedHashMap::new(1),
            admin_challenges: TimedHashMap::new(timeout.challenge),
            admin_limit: TimedHashMap::new(timeout.admin),
            blocklist: Default::default(),
            stats: Stats::new(cfg.stat),

            filtered_servers: Default::default(),
            filtered_servers_nat: Default::default(),

            cfg: cfg.master,
        })
    }

    pub fn local_addr(&self) -> io::Result<SocketAddr> {
        self.sock.local_addr()
    }

    pub fn update_config(&mut self, cfg: Config) -> Result<Option<Config>, Error> {
        let local_addr = self.local_addr()?;
        let addr = SocketAddr::new(cfg.master.server.ip, cfg.master.server.port);
        if local_addr.is_ipv4() != addr.is_ipv4() {
            return Ok(Some(cfg));
        } else if local_addr != addr {
            info!("Listen address: {addr}");
            self.sock = UdpSocket::bind(addr).map_err(Error::BindSocket)?;
            // make socket interruptible by signals
            let timeout = Duration::from_secs(u32::MAX as u64);
            self.sock.set_read_timeout(Some(timeout))?;
            self.clear();
        }

        self.update_addr = resolve_update_addr(&cfg.master, addr);
        self.stats.update_config(cfg.stat);
        self.cfg = cfg.master;

        // set timeouts from new config
        let timeout = &self.cfg.server.timeout;
        self.challenges.set_timeout(timeout.challenge);
        self.servers.set_timeout(timeout.server);
        self.admin_challenges.set_timeout(timeout.challenge);
        self.admin_limit.set_timeout(timeout.admin);

        Ok(None)
    }

    pub fn run(&mut self, sig_flag: &AtomicBool) -> Result<(), Error> {
        let mut buf = [0; 2048];
        while !sig_flag.load(Ordering::Relaxed) {
            let (n, from) = match self.sock.recv_from(&mut buf) {
                Ok(x) => x,
                Err(e) => match e.kind() {
                    io::ErrorKind::Interrupted => break,
                    io::ErrorKind::TimedOut | io::ErrorKind::WouldBlock => continue,
                    _ => Err(e)?,
                },
            };

            let from = match Addr::extract(from) {
                Ok(from) => from,
                Err(_) => continue,
            };

            let src = &buf[..n];
            if let Err(e) = self.handle_packet(from, src) {
                debug!("{}: {}: \"{}\"", from, e, Str(src));
                self.stats.on_error();
            }
        }
        Ok(())
    }

    fn clear(&mut self) {
        info!("Clear all servers and challenges");
        self.challenges.clear();
        self.servers.clear();
        self.admin_challenges.clear();
        self.stats.clear();
        self.client_rate_limit.clear();
    }

    fn handle_server_packet(&mut self, from: Addr, p: server::Packet) -> Result<(), Error> {
        trace!("{from}: recv {p:?}");

        match p {
            server::Packet::Challenge(p) => {
                let challenge = self.server_challenge_add(from);
                let resp = master::ChallengeResponse::new(challenge, p.server_challenge);
                trace!("{from}: send {resp:?}");
                let mut buf = [0; 32];
                let packet = resp.encode(&mut buf)?;
                self.sock.send_to(packet, from)?;
            }
            server::Packet::ServerAdd(p) => {
                if p.version < self.cfg.server.min_version {
                    let min = self.cfg.server.min_version;
                    warn!(
                        "{from}: server version is {} but minimal allowed is {min}",
                        p.version
                    );
                    return Ok(());
                }
                let Some(challenge) = self.server_challenge_get(&from) else {
                    trace!("{from}: challenge does not exist");
                    return Ok(());
                };
                if p.challenge != challenge {
                    warn!(
                        "{from}: expected challenge {challenge} but received {}",
                        p.challenge
                    );
                    return Ok(());
                }
                if self.challenges.remove(&from).is_some() {
                    self.add_server(from, ServerInfo::new(&p));
                    self.stats.on_server_add();
                    self.stats.servers_count(self.servers.len());
                }
            }
            server::Packet::ServerRemove => {
                self.stats.on_server_del();
            }
            _ => {
                return Err(Error::UnexpectedPacket);
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
        from: Addr,
        key: Option<u32>,
        update_addr: SocketAddr,
    ) -> Result<(), Error> {
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

    fn send_servers(&mut self, from: Addr, query: &QueryServers<Filter>) -> Result<(), Error> {
        let filter = &query.filter;

        if !self.is_query_servers_valid(&from, query) {
            self.save_client_gamedir(from, query.filter.gamedir);
            return self.send_fake_server(from, filter.key, self.update_addr);
        }

        let Some(client_version) = filter.clver else {
            // checked in is_query_servers_valid
            return Ok(());
        };

        self.filtered_servers.clear();
        self.filtered_servers_nat.clear();

        for (addr, info) in self.servers.iter() {
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
        if filter.contains_flags(FilterFlags::NAT).unwrap_or(true) {
            self.send_client_to_nat_servers(from, &self.filtered_servers_nat)?;
        }

        Ok(())
    }

    fn save_client_gamedir(&mut self, from: Addr, gamedir: Option<Str<&[u8]>>) {
        let err_msg = "failed to save gamedir for update message";
        let Some(gamedir) = gamedir else {
            trace!("{from}: {err_msg}, gamedir is none");
            return;
        };
        let Some(gamedir) = StrArr::new(&gamedir) else {
            trace!("{from}: {err_msg}, gamedir is invalid {gamedir:?}");
            return;
        };
        self.update_gamedir.insert(from, gamedir);
    }

    fn send_update_info(&mut self, from: Addr, protocol: u8) -> Result<(), Error> {
        let gamedir = self.update_gamedir.remove(&from);
        let resp = server::GetServerInfoResponse {
            map: self.cfg.client.update_map.as_ref(),
            host: self.cfg.client.update_title.as_ref(),
            protocol,
            dm: true,
            maxcl: 32,
            gamedir: gamedir.as_ref().map_or("valve", |i| i.as_str()),
            ..Default::default()
        };
        trace!("{from}: send {resp:?}");
        let mut buf = Addr::mtu_buffer();
        let packet = resp.encode(buf.as_mut())?;
        self.sock.send_to(packet, from)?;
        Ok(())
    }

    fn handle_game_packet(&mut self, from: Addr, p: game::Packet) -> Result<(), Error> {
        if self.cfg.server.client_rate_limit > 0 {
            let counter = self.client_rate_limit.entry(*from.ip()).or_default();
            counter.value = counter.value.saturating_add(1);
            if counter.value > self.cfg.server.client_rate_limit {
                trace!("{from}: client rate limit {}", counter.value);
                return Ok(());
            }
        }

        trace!("{from}: recv {p:?}");
        match p {
            game::Packet::QueryServers(p) => {
                self.stats.on_query_servers();
                self.send_servers(from, &p)?;
            }
            game::Packet::GetServerInfo(p) => {
                self.send_update_info(from, p.protocol)?;
            }
        }
        Ok(())
    }

    fn handle_admin_packet(&mut self, from: Addr, p: admin::Packet) -> Result<(), Error> {
        trace!("{from}: recv {p:?}");

        if self.admin_limit.get(from.ip()).is_some() {
            trace!("{from}: admin rate limit");
            return Ok(());
        }

        match p {
            admin::Packet::AdminChallenge => {
                let (master_challenge, hash_challenge) = self.admin_challenge_add(from);

                let resp = master::AdminChallengeResponse::new(master_challenge, hash_challenge);
                trace!("{from}: send {resp:?}");
                let mut buf = [0; 64];
                let packet = resp.encode(&mut buf)?;
                self.sock.send_to(packet, from)?;
            }
            admin::Packet::AdminCommand(p) => {
                let entry = *self
                    .admin_challenges
                    .get(from.ip())
                    .ok_or(Error::AdminChallengeNotFound)?;

                if entry.0 != p.master_challenge {
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
                    *p.hash == hash.as_bytes()
                });

                match admin {
                    Some(admin) => {
                        info!("{from}: admin({}), command: {:?}", &admin.name, p.command);
                        self.admin_command(p.command);
                        self.admin_challenge_remove(from);
                    }
                    None => {
                        warn!("{from}: invalid admin hash, command: {:?}", p.command);
                        self.admin_limit.insert(*from.ip(), ());
                    }
                }
            }
        }

        Ok(())
    }

    fn handle_packet(&mut self, from: Addr, src: &[u8]) -> Result<(), Error> {
        if self.is_blocked(from.ip()) {
            return Ok(());
        }

        match server::Packet::decode(src) {
            Ok(Some(p)) => return self.handle_server_packet(from, p),
            Ok(None) => {}
            Err(e) => Err(e)?,
        }

        match game::Packet::decode(src) {
            Ok(Some(p)) => return self.handle_game_packet(from, p),
            Ok(None) => {}
            Err(e) => Err(e)?,
        }

        match admin::Packet::decode(self.cfg.hash.len, src) {
            Ok(Some(p)) => return self.handle_admin_packet(from, p),
            Ok(None) => {}
            Err(e) => Err(e)?,
        }

        Err(Error::UndefinedPacket)
    }

    fn server_challenge_add(&mut self, addr: Addr) -> u32 {
        self.challenges
            .entry(addr)
            .or_insert_with(|| Timed::new(self.rng.u32(..)))
            .value
    }

    fn server_challenge_get(&self, addr: &Addr) -> Option<u32> {
        self.challenges.get(addr).map(|i| i.value)
    }

    fn admin_challenge_add(&mut self, addr: Addr) -> (u32, u32) {
        let x = self.rng.u32(..);
        let y = self.rng.u32(..);
        self.admin_challenges.insert(*addr.ip(), (x, y));
        (x, y)
    }

    fn admin_challenge_remove(&mut self, addr: Addr) {
        self.admin_challenges.remove(addr.ip());
    }

    #[allow(dead_code)]
    fn count_all_servers(&self) -> usize {
        self.servers.len()
    }

    fn count_servers(&self, ip: &Addr::Ip) -> u16 {
        self.servers.keys().filter(|i| i.ip() == ip).count() as u16
    }

    fn remove_servers_by_ip(&mut self, ip: &Addr::Ip) {
        let mut servers_to_remove: Vec<Addr> = Vec::new();

        // have to create a copy to not mutate while iterating
        for (addr, _) in self.servers.iter() {
            if addr.ip() == ip {
                servers_to_remove.push(addr.clone());
            }
        }

        for addr in servers_to_remove {
            self.servers.remove(&addr);
        }
    }

    fn add_server(&mut self, addr: Addr, server: ServerInfo) {
        match self.servers.entry(addr) {
            hash_map::Entry::Occupied(mut e) => {
                trace!("{addr}: game server updated");
                e.insert(Timed::new(server));
            }
            hash_map::Entry::Vacant(_) => {
                if self.count_servers(addr.ip()) >= self.cfg.server.max_servers_per_ip {
                    trace!("{addr}: game server rejected, max servers per ip");
                    return;
                }
                trace!("{addr}: game server added");
                self.servers.insert(addr, server);
            }
        }
    }

    fn send_server_list<A, S>(&self, to: A, key: Option<u32>, servers: &[S]) -> Result<(), Error>
    where
        A: ToSocketAddrs,
        S: ServerAddress,
    {
        let mut list = master::QueryServersResponse::new(key);
        let mut buf = Addr::mtu_buffer();
        let mut offset = 0;
        loop {
            let (packet, count) = list.encode(buf.as_mut(), &servers[offset..])?;
            self.sock.send_to(packet, &to)?;
            offset += count;
            if offset >= servers.len() {
                break;
            }
        }
        Ok(())
    }

    fn send_client_to_nat_servers(&self, to: Addr, servers: &[Addr]) -> Result<(), Error> {
        let mut buf = [0; 64];
        let packet = master::ClientAnnounce::new(to.wrap()).encode(&mut buf)?;
        for i in servers {
            self.sock.send_to(packet, i)?;
        }
        Ok(())
    }

    #[inline]
    fn is_blocked(&self, ip: &Addr::Ip) -> bool {
        self.blocklist.contains(ip)
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
                    if self.blocklist.insert(ip) {
                        info!("ban ip: {ip}");

                        self.remove_servers_by_ip(&ip);
                    }
                });
            }
            "unban" => {
                helper::<Addr, _>(&args[1..], |_, ip| {
                    if self.blocklist.remove(&ip) {
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

#[cfg(test)]
mod tests {
    use super::*;

    use xash3d_protocol::server::Region;

    #[test]
    fn check_remove_server_by_ip() {
        use server::{Os, ServerAdd, ServerFlags, ServerType};

        let cfg = Config::default();

        let addr = SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0);
        let mut master = MasterServer::new(cfg, addr).unwrap();

        let server_add = ServerAdd {
            gamedir: Str(&b"valve"[..]),
            map: Str(&b"crossfire"[..]),
            version: Version::new(0, 20),
            challenge: 0x12345678,
            server_type: ServerType::Dedicated,
            os: Os::Linux,
            region: Region::RestOfTheWorld,
            protocol: 49,
            players: 4,
            max: 32,
            bots: 8,
            flags: ServerFlags::all(),
        };

        let dummy_ip = Ipv4Addr::new(1, 1, 1, 1);
        let dummy_ip2 = Ipv4Addr::new(1, 1, 1, 2);

        master.add_server(
            SocketAddrV4::new(dummy_ip, 27015),
            ServerInfo::new(&server_add),
        );
        master.add_server(
            SocketAddrV4::new(dummy_ip, 27016),
            ServerInfo::new(&server_add),
        );
        master.add_server(
            SocketAddrV4::new(dummy_ip, 27017),
            ServerInfo::new(&server_add),
        );
        master.add_server(
            SocketAddrV4::new(dummy_ip2, 27015),
            ServerInfo::new(&server_add),
        );

        assert_eq!(master.count_all_servers(), 4);

        master.remove_servers_by_ip(&Ipv4Addr::new(1, 1, 1, 1));

        assert_eq!(master.count_all_servers(), 1);
    }

    #[test]
    fn check_query_servers() {
        const BUILDNUM_NEW: u32 = 3500;
        const BUILDNUM_OLD: u32 = 3000;

        let mut cfg = Config::default();
        cfg.master.client.min_version = Version::new(0, 19);
        cfg.master.client.min_engine_buildnum = BUILDNUM_NEW;
        cfg.master.client.min_old_engine_buildnum = BUILDNUM_OLD;

        let addr = SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0);
        let master = MasterServer::new(cfg, addr).unwrap();

        let mut query = QueryServers {
            region: Region::RestOfTheWorld,
            last: SocketAddr::V4(addr),
            filter: Filter::default(),
        };

        // check missing fields
        query.filter.clver = None;
        query.filter.client_buildnum = None;
        assert!(!master.is_query_servers_valid(&addr, &query));

        query.filter.clver = Some(Version::new(0, 21));
        query.filter.client_buildnum = None;
        assert!(!master.is_query_servers_valid(&addr, &query));

        query.filter.clver = None;
        query.filter.client_buildnum = Some(BUILDNUM_NEW);
        assert!(!master.is_query_servers_valid(&addr, &query));

        // check engine buildnum
        query.filter.clver = Some(Version::new(0, 21));
        query.filter.client_buildnum = Some(BUILDNUM_NEW);
        assert!(master.is_query_servers_valid(&addr, &query));
        query.filter.client_buildnum = Some(BUILDNUM_NEW - 1);
        assert!(!master.is_query_servers_valid(&addr, &query));

        // check engine buildnum
        query.filter.clver = Some(Version::new(0, 19));
        query.filter.client_buildnum = Some(BUILDNUM_OLD);
        assert!(master.is_query_servers_valid(&addr, &query));
        query.filter.client_buildnum = Some(BUILDNUM_OLD - 1);
        assert!(!master.is_query_servers_valid(&addr, &query));
    }
}
