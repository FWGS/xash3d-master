// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::{
    cmp::Eq,
    collections::hash_map,
    fmt::Display,
    hash::Hash,
    io,
    net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6, ToSocketAddrs, UdpSocket},
    ops::Deref,
    str::FromStr,
    sync::atomic::{AtomicBool, Ordering},
    time::{Duration, Instant},
};

use ahash::{AHashMap as HashMap, AHashSet as HashSet};
use blake2b_simd::Params;
use fastrand::Rng;
use log::{debug, error, info, trace, warn};
use thiserror::Error;
use xash3d_protocol::{
    admin,
    filter::{Filter, FilterFlags, Version},
    game::{self, QueryServers},
    master::{self, ServerAddress},
    server::{self, Region},
    wrappers::Str,
    Error as ProtocolError,
};

use crate::{config::Config, stats::Stats};

type ServerInfo = xash3d_protocol::ServerInfo<Box<[u8]>>;

pub trait AddrExt: Sized + Eq + Hash + Display + Copy + ToSocketAddrs + ServerAddress {
    type Ip: Eq + Hash + Display + Copy + FromStr;

    fn extract(addr: SocketAddr) -> Result<Self, SocketAddr>;
    fn ip(&self) -> &Self::Ip;
    fn wrap(self) -> SocketAddr;

    fn mtu() -> usize;
}

impl AddrExt for SocketAddrV4 {
    type Ip = Ipv4Addr;

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
    fn mtu() -> usize {
        512
    }
}

impl AddrExt for SocketAddrV6 {
    type Ip = Ipv6Addr;

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
    fn mtu() -> usize {
        MAX_PACKET_SIZE
    }
}

/// The maximum size of UDP packets.
const MAX_PACKET_SIZE: usize = 1280;

/// How many cleanup calls should be skipped before removing outdated servers.
const SERVER_CLEANUP_MAX: usize = 100;

/// How many cleanup calls should be skipped before removing outdated challenges.
const CHALLENGE_CLEANUP_MAX: usize = 100;

/// How many cleanup calls should be skipped before removing outdated admin challenges.
const ADMIN_CHALLENGE_CLEANUP_MAX: usize = 100;

/// How many cleanup calls should be skipped before removing outdated admin limit entries
const ADMIN_LIMIT_CLEANUP_MAX: usize = 100;

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

/// HashMap entry to keep tracking creation time.
#[derive(Copy, Clone, Debug)]
struct Entry<T> {
    time: u32,
    value: T,
}

impl<T> Entry<T> {
    fn new(time: u32, value: T) -> Self {
        Self { time, value }
    }

    fn is_valid(&self, now: u32, duration: u32) -> bool {
        (now - self.time) < duration
    }
}

impl Entry<ServerInfo> {
    fn matches(&self, region: Region, filter: &Filter) -> bool {
        self.region == region && filter.matches(&self.value)
    }
}

impl<T> Deref for Entry<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

struct Counter {
    max: usize,
    cur: usize,
}

impl Counter {
    fn new(max: usize) -> Self {
        Self { max, cur: 0 }
    }

    fn next(&mut self) -> bool {
        if self.cur <= self.max {
            self.cur += 1;
            false
        } else {
            self.cur = 0;
            true
        }
    }
}

pub struct MasterServer<Addr: AddrExt> {
    cfg: Config,

    sock: UdpSocket,
    challenges: HashMap<Addr, Entry<u32>>,
    challenges_counter: Counter,
    servers: HashMap<Addr, Entry<ServerInfo>>,
    servers_counter: Counter,
    rng: Rng,

    start_time: Instant,

    update_addr: SocketAddr,

    admin_challenges: HashMap<Addr::Ip, Entry<(u32, u32)>>,
    admin_challenges_counter: Counter,
    // rate limit if hash is invalid
    admin_limit: HashMap<Addr::Ip, Entry<()>>,
    admin_limit_counter: Counter,

    blocklist: HashSet<Addr::Ip>,

    stats: Stats,

    // temporary data
    filtered_servers: Vec<Addr>,
    filtered_servers_nat: Vec<Addr>,
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

fn resolve_update_addr(cfg: &Config, local_addr: SocketAddr) -> SocketAddr {
    if let Some(s) = cfg.client.update_addr.as_deref() {
        let addr = if !s.contains(':') {
            format!("{}:{}", s, local_addr.port())
        } else {
            s.to_owned()
        };

        match resolve_socket_addr(&addr, local_addr.is_ipv4()) {
            Ok(Some(x)) => return x,
            Ok(None) => error!("Update address: failed to resolve IP for \"{}\"", addr),
            Err(e) => error!("Update address: {}", e),
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
        match SocketAddr::new(cfg.server.ip, cfg.server.port) {
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

impl<Addr: AddrExt> MasterServer<Addr> {
    pub fn new(cfg: Config, addr: Addr) -> Result<Self, Error> {
        info!("Listen address: {}", addr);

        let sock = UdpSocket::bind(addr).map_err(Error::BindSocket)?;
        // make socket interruptable by singals
        sock.set_read_timeout(Some(Duration::from_secs(u32::MAX as u64)))?;

        let update_addr = resolve_update_addr(&cfg, addr.wrap());

        Ok(Self {
            sock,
            start_time: Instant::now(),
            challenges: Default::default(),
            challenges_counter: Counter::new(CHALLENGE_CLEANUP_MAX),
            servers: Default::default(),
            servers_counter: Counter::new(SERVER_CLEANUP_MAX),
            rng: Rng::new(),
            update_addr,
            admin_challenges: Default::default(),
            admin_challenges_counter: Counter::new(ADMIN_CHALLENGE_CLEANUP_MAX),
            admin_limit: Default::default(),
            admin_limit_counter: Counter::new(ADMIN_LIMIT_CLEANUP_MAX),
            blocklist: Default::default(),
            stats: Stats::new(cfg.stat.clone()),

            filtered_servers: Default::default(),
            filtered_servers_nat: Default::default(),

            cfg,
        })
    }

    fn local_addr(&self) -> io::Result<SocketAddr> {
        self.sock.local_addr()
    }

    pub fn update_config(&mut self, cfg: Config) -> Result<Option<Config>, Error> {
        let local_addr = self.local_addr()?;
        let addr = SocketAddr::new(cfg.server.ip, cfg.server.port);
        if local_addr.is_ipv4() != addr.is_ipv4() {
            return Ok(Some(cfg));
        } else if local_addr != addr {
            info!("Listen address: {}", addr);
            self.sock = UdpSocket::bind(addr).map_err(Error::BindSocket)?;
            // make socket interruptable by singals
            self.sock
                .set_read_timeout(Some(Duration::from_secs(u32::MAX as u64)))?;
            self.clear();
        }

        self.update_addr = resolve_update_addr(&cfg, addr);
        self.stats.update_config(cfg.stat.clone());
        self.cfg = cfg;

        Ok(None)
    }

    pub fn run(&mut self, sig_flag: &AtomicBool) -> Result<(), Error> {
        let mut buf = [0; MAX_PACKET_SIZE];
        while !sig_flag.load(Ordering::Relaxed) {
            let (n, from) = match self.sock.recv_from(&mut buf[..Addr::mtu()]) {
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
    }

    fn handle_server_packet(&mut self, from: Addr, p: server::Packet) -> Result<(), Error> {
        trace!("{}: recv {:?}", from, p);

        match p {
            server::Packet::Challenge(p) => {
                let master_challenge = self.add_challenge(from);
                let mut buf = [0; MAX_PACKET_SIZE];
                let p = master::ChallengeResponse::new(master_challenge, p.server_challenge);
                trace!("{}: send {:?}", from, p);
                let n = p.encode(&mut buf)?;
                self.sock.send_to(&buf[..n], from)?;
                self.remove_outdated_challenges();
            }
            server::Packet::ServerAdd(p) => {
                let entry = match self.challenges.get(&from) {
                    Some(e) => e,
                    None => {
                        trace!("{}: Challenge does not exists", from);
                        return Ok(());
                    }
                };
                if !entry.is_valid(self.now(), self.cfg.server.timeout.challenge) {
                    return Ok(());
                }
                if p.version < self.cfg.server.min_version {
                    warn!(
                        "{}: server version is {} but minimal allowed is {}",
                        from, p.version, self.cfg.server.min_version
                    );
                    return Ok(());
                }
                if p.challenge != entry.value {
                    warn!(
                        "{}: Expected challenge {} but received {}",
                        from, entry.value, p.challenge
                    );
                    return Ok(());
                }
                if self.challenges.remove(&from).is_some() {
                    self.add_server(from, ServerInfo::new(&p));
                    self.stats.on_server_add();
                    self.stats.servers_count(self.servers.len());
                }
                self.remove_outdated_servers();
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

    fn is_query_servers_valid(&self, from: &Addr, query: &QueryServers<Filter>) -> bool {
        // FIXME: if we will ever support XashNT master server protocol, depends whether
        // Unkle Mike would like to use our implementation and server, just hide this
        // whole mess under a "feature" and host a MS for him on a separate port

        let Some(version) = query.filter.clver else {
            // clver field is required
            trace!("{from}: query rejected, no clver field");
            return false;
        };

        let Some(buildnum) = query.filter.client_buildnum else {
            // buildnum field is required
            trace!("{from}: query rejected, no buildnum field");
            return false;
        };

        if version < self.cfg.client.min_version {
            let min = self.cfg.client.min_version;
            trace!("{from}: query rejected, version {version} is less than {min}");
            return false;
        }

        if version < Version::new(0, 20) {
            // old engine has separate buildnum limit
            if buildnum < self.cfg.client.min_old_engine_buildnum {
                let min = self.cfg.client.min_old_engine_buildnum;
                trace!("{from}: query rejected, buildnum {buildnum} is less than {min}");
                return false;
            }
        } else if buildnum < self.cfg.client.min_engine_buildnum {
            let min = self.cfg.client.min_engine_buildnum;
            trace!("{from}: query rejected, buildnum {buildnum} is less than {min}");
            return false;
        }

        true
    }

    fn send_fake_server(
        &self,
        from: Addr,
        key: Option<u32>,
        update_addr: SocketAddr,
    ) -> Result<(), Error> {
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

    fn handle_game_packet(&mut self, from: Addr, p: game::Packet) -> Result<(), Error> {
        trace!("{}: recv {:?}", from, p);

        match p {
            game::Packet::QueryServers(p) => {
                if self.is_query_servers_valid(&from, &p) {
                    return self.send_fake_server(from, p.filter.key, self.update_addr);
                }

                let now = self.now();

                self.filtered_servers.clear();
                self.filtered_servers_nat.clear();
                self.servers
                    .iter()
                    .filter(|(_addr, info)| {
                        info.is_valid(now, self.cfg.server.timeout.server)
                            && info.matches(p.region, &p.filter)
                    })
                    .for_each(|(addr, info)| {
                        self.filtered_servers.push(*addr);
                        if info.flags.contains(FilterFlags::NAT) {
                            self.filtered_servers_nat.push(*addr);
                        }
                    });

                self.send_server_list(from, p.filter.key, &self.filtered_servers)?;

                // NOTE: If NAT is not set in a filter then by default the client is announced
                // to filtered servers behind NAT.
                if p.filter.contains_flags(FilterFlags::NAT).unwrap_or(true) {
                    self.send_client_to_nat_servers(from, &self.filtered_servers_nat)?;
                }

                self.stats.on_query_servers();
            }
            game::Packet::GetServerInfo(_) => {
                let p = server::GetServerInfoResponse {
                    map: self.cfg.client.update_map.as_ref(),
                    host: self.cfg.client.update_title.as_ref(),
                    // XXX: how to detect what version client will accept?
                    protocol: self.cfg.client.update_protocol,
                    dm: true,
                    maxcl: 32,
                    // XXX: probably must be specific for client...
                    gamedir: &self.cfg.client.update_gamedir,
                    ..Default::default()
                };
                trace!("{}: send {:?}", from, p);
                let mut buf = [0; MAX_PACKET_SIZE];
                let n = p.encode(&mut buf[..Addr::mtu()])?;
                self.sock.send_to(&buf[..n], from)?;
            }
        }

        Ok(())
    }

    fn handle_admin_packet(&mut self, from: Addr, p: admin::Packet) -> Result<(), Error> {
        trace!("{}: recv {:?}", from, p);

        let now = self.now();

        if let Some(e) = self.admin_limit.get(from.ip()) {
            if e.is_valid(now, self.cfg.server.timeout.admin) {
                trace!("{}: rate limit", from);
                return Ok(());
            }
        }

        match p {
            admin::Packet::AdminChallenge => {
                let (master_challenge, hash_challenge) = self.admin_challenge_add(from);

                let p = master::AdminChallengeResponse::new(master_challenge, hash_challenge);
                trace!("{}: send {:?}", from, p);
                let mut buf = [0; 64];
                let n = p.encode(&mut buf)?;
                self.sock.send_to(&buf[..n], from)?;

                self.admin_challenges_cleanup();
            }
            admin::Packet::AdminCommand(p) => {
                let entry = *self
                    .admin_challenges
                    .get(from.ip())
                    .ok_or(Error::AdminChallengeNotFound)?;

                if entry.0 != p.master_challenge {
                    trace!("{}: master challenge is not valid", from);
                    return Ok(());
                }

                if !entry.is_valid(now, self.cfg.server.timeout.challenge) {
                    trace!("{}: challenge is outdated", from);
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
                        info!("{}: admin({}), command: {:?}", from, &admin.name, p.command);
                        self.admin_command(p.command);
                        self.admin_challenge_remove(from);
                    }
                    None => {
                        warn!("{}: invalid admin hash, command: {:?}", from, p.command);
                        self.admin_limit.insert(*from.ip(), Entry::new(now, ()));
                        self.admin_limit_cleanup();
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

    fn now(&self) -> u32 {
        self.start_time.elapsed().as_secs() as u32
    }

    fn add_challenge(&mut self, addr: Addr) -> u32 {
        let x = self.rng.u32(..);
        let entry = Entry::new(self.now(), x);
        self.challenges.insert(addr, entry);
        x
    }

    fn remove_outdated_challenges(&mut self) {
        if self.challenges_counter.next() {
            let now = self.now();
            self.challenges
                .retain(|_, v| v.is_valid(now, self.cfg.server.timeout.challenge));
        }
    }

    fn admin_challenge_add(&mut self, addr: Addr) -> (u32, u32) {
        let x = self.rng.u32(..);
        let y = self.rng.u32(..);
        let entry = Entry::new(self.now(), (x, y));
        self.admin_challenges.insert(*addr.ip(), entry);
        (x, y)
    }

    fn admin_challenge_remove(&mut self, addr: Addr) {
        self.admin_challenges.remove(addr.ip());
    }

    /// Remove outdated entries
    fn admin_challenges_cleanup(&mut self) {
        if self.admin_challenges_counter.next() {
            let now = self.now();
            self.admin_challenges
                .retain(|_, v| v.is_valid(now, self.cfg.server.timeout.challenge));
        }
    }

    fn admin_limit_cleanup(&mut self) {
        if self.admin_limit_counter.next() {
            let now = self.now();
            self.admin_limit
                .retain(|_, v| v.is_valid(now, self.cfg.server.timeout.admin));
        }
    }

    fn count_servers(&self, ip: &Addr::Ip) -> u16 {
        self.servers.keys().filter(|i| i.ip() == ip).count() as u16
    }

    fn add_server(&mut self, addr: Addr, server: ServerInfo) {
        let now = self.now();
        match self.servers.entry(addr) {
            hash_map::Entry::Occupied(mut e) => {
                trace!("{}: Updated GameServer", addr);
                e.insert(Entry::new(now, server));
            }
            hash_map::Entry::Vacant(_) => {
                if self.count_servers(addr.ip()) >= self.cfg.server.max_servers_per_ip {
                    trace!("{}: max servers per ip", addr);
                    return;
                }
                trace!("{}: New GameServer", addr);
                self.servers.insert(addr, Entry::new(now, server));
            }
        }
    }

    fn remove_outdated_servers(&mut self) {
        if self.servers_counter.next() {
            let now = self.now();
            self.servers
                .retain(|_, v| v.is_valid(now, self.cfg.server.timeout.server));
            self.stats.servers_count(self.servers.len());
        }
    }

    fn send_server_list<A, S>(&self, to: A, key: Option<u32>, servers: &[S]) -> Result<(), Error>
    where
        A: ToSocketAddrs,
        S: ServerAddress,
    {
        let mut buf = [0; MAX_PACKET_SIZE];
        let mut offset = 0;
        let mut list = master::QueryServersResponse::new(key);
        while offset < servers.len() {
            let (n, c) = list.encode(&mut buf[..Addr::mtu()], &servers[offset..])?;
            offset += c;
            self.sock.send_to(&buf[..n], &to)?;
        }
        Ok(())
    }

    fn send_client_to_nat_servers(&self, to: Addr, servers: &[Addr]) -> Result<(), Error> {
        let mut buf = [0; 64];
        let n = master::ClientAnnounce::new(to.wrap()).encode(&mut buf)?;
        let buf = &buf[..n];
        for i in servers {
            self.sock.send_to(buf, i)?;
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
                    Err(_) => warn!("invalid ip: {}", i),
                }
            }
        }

        match args[0] {
            "ban" => {
                helper::<Addr, _>(&args[1..], |_, ip| {
                    if self.blocklist.insert(ip) {
                        info!("ban ip: {}", ip);
                    }
                });
            }
            "unban" => {
                helper::<Addr, _>(&args[1..], |_, ip| {
                    if self.blocklist.remove(&ip) {
                        info!("unban ip: {}", ip);
                    }
                });
            }
            _ => {
                warn!("invalid command: {}", args[0]);
            }
        }
    }
}
