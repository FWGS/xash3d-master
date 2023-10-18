// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::collections::{HashMap, HashSet};
use std::io;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4, ToSocketAddrs, UdpSocket};
use std::ops::Deref;
use std::time::Instant;

use blake2b_simd::Params;
use fastrand::Rng;
use log::{error, info, trace, warn};
use thiserror::Error;
use xash3d_protocol::filter::{Filter, Version};
use xash3d_protocol::server::Region;
use xash3d_protocol::{admin, game, master, server, Error as ProtocolError, ServerInfo};

use crate::config::{self, Config};

/// The maximum size of UDP packets.
const MAX_PACKET_SIZE: usize = 512;

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
    fn matches(&self, addr: SocketAddrV4, region: Region, filter: &Filter) -> bool {
        self.region == region && filter.matches(addr, &self.value)
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

struct MasterServer {
    sock: UdpSocket,
    challenges: HashMap<SocketAddrV4, Entry<u32>>,
    challenges_counter: Counter,
    servers: HashMap<SocketAddrV4, Entry<ServerInfo>>,
    servers_counter: Counter,
    rng: Rng,

    start_time: Instant,
    timeout: config::TimeoutConfig,

    clver: Version,
    update_title: Box<str>,
    update_map: Box<str>,
    update_addr: SocketAddrV4,

    admin_challenges: HashMap<Ipv4Addr, Entry<(u32, u32)>>,
    admin_challenges_counter: Counter,
    admin_list: Box<[config::AdminConfig]>,
    // rate limit if hash is invalid
    admin_limit: HashMap<Ipv4Addr, Entry<()>>,
    admin_limit_counter: Counter,
    hash: config::HashConfig,

    blocklist: HashSet<Ipv4Addr>,
}

impl MasterServer {
    fn new(cfg: Config) -> Result<Self, Error> {
        let addr = SocketAddr::new(cfg.server.ip, cfg.server.port);
        info!("Listen address: {}", addr);
        let sock = UdpSocket::bind(addr).map_err(Error::BindSocket)?;
        let update_addr =
            cfg.client
                .update_addr
                .unwrap_or_else(|| match sock.local_addr().unwrap() {
                    SocketAddr::V4(addr) => addr,
                    _ => todo!(),
                });

        Ok(Self {
            sock,
            start_time: Instant::now(),
            challenges: Default::default(),
            challenges_counter: Counter::new(CHALLENGE_CLEANUP_MAX),
            servers: Default::default(),
            servers_counter: Counter::new(SERVER_CLEANUP_MAX),
            rng: Rng::new(),
            timeout: cfg.server.timeout,
            clver: cfg.client.version,
            update_title: cfg.client.update_title,
            update_map: cfg.client.update_map,
            update_addr,
            admin_challenges: Default::default(),
            admin_challenges_counter: Counter::new(ADMIN_CHALLENGE_CLEANUP_MAX),
            admin_list: cfg.admin_list,
            admin_limit: Default::default(),
            admin_limit_counter: Counter::new(ADMIN_LIMIT_CLEANUP_MAX),
            hash: cfg.hash,
            blocklist: Default::default(),
        })
    }

    fn run(&mut self) -> Result<(), Error> {
        let mut buf = [0; MAX_PACKET_SIZE];
        loop {
            let (n, from) = self.sock.recv_from(&mut buf)?;

            let from = match from {
                SocketAddr::V4(a) => a,
                _ => {
                    warn!("{}: Received message from IPv6, unimplemented", from);
                    continue;
                }
            };

            if let Err(e) = self.handle_packet(from, &buf[..n]) {
                error!("{}: {}", from, e);
            }
        }
    }

    fn handle_packet(&mut self, from: SocketAddrV4, src: &[u8]) -> Result<(), Error> {
        if self.is_blocked(from.ip()) {
            return Ok(());
        }

        if let Ok(p) = server::Packet::decode(src) {
            match p {
                server::Packet::Challenge(p) => {
                    trace!("{}: recv {:?}", from, p);
                    let master_challenge = self.add_challenge(from);
                    let mut buf = [0; MAX_PACKET_SIZE];
                    let p = master::ChallengeResponse::new(master_challenge, p.server_challenge);
                    trace!("{}: send {:?}", from, p);
                    let n = p.encode(&mut buf)?;
                    self.sock.send_to(&buf[..n], from)?;
                    self.remove_outdated_challenges();
                }
                server::Packet::ServerAdd(p) => {
                    trace!("{}: recv {:?}", from, p);
                    let entry = match self.challenges.get(&from) {
                        Some(e) => e,
                        None => {
                            trace!("{}: Challenge does not exists", from);
                            return Ok(());
                        }
                    };
                    if !entry.is_valid(self.now(), self.timeout.challenge) {
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
                    }
                    self.remove_outdated_servers();
                }
                _ => {
                    trace!("{}: recv {:?}", from, p);
                }
            }
        }

        if let Ok(p) = game::Packet::decode(src) {
            match p {
                game::Packet::QueryServers(p) => {
                    trace!("{}: recv {:?}", from, p);
                    if p.filter.clver < self.clver {
                        let iter = std::iter::once(self.update_addr);
                        self.send_server_list(from, iter)?;
                    } else {
                        let now = self.now();
                        let iter = self
                            .servers
                            .iter()
                            .filter(|i| i.1.is_valid(now, self.timeout.server))
                            .filter(|i| i.1.matches(*i.0, p.region, &p.filter))
                            .map(|i| *i.0);
                        self.send_server_list(from, iter)?;
                    }
                }
                game::Packet::GetServerInfo(p) => {
                    trace!("{}: recv {:?}", from, p);
                    let p = server::GetServerInfoResponse {
                        map: self.update_map.as_ref(),
                        host: self.update_title.as_ref(),
                        protocol: 49,
                        dm: true,
                        maxcl: 32,
                        gamedir: "valve",
                        ..Default::default()
                    };
                    trace!("{}: send {:?}", from, p);
                    let mut buf = [0; MAX_PACKET_SIZE];
                    let n = p.encode(&mut buf)?;
                    self.sock.send_to(&buf[..n], from)?;
                }
            }
        }

        if let Ok(p) = admin::Packet::decode(self.hash.len, src) {
            let now = self.now();

            if let Some(e) = self.admin_limit.get(from.ip()) {
                if e.is_valid(now, self.timeout.admin) {
                    trace!("{}: rate limit", from);
                    return Ok(());
                }
            }

            match p {
                admin::Packet::AdminChallenge(p) => {
                    trace!("{}: recv {:?}", from, p);
                    let (master_challenge, hash_challenge) = self.admin_challenge_add(from);

                    let p = master::AdminChallengeResponse::new(master_challenge, hash_challenge);
                    trace!("{}: send {:?}", from, p);
                    let mut buf = [0; 64];
                    let n = p.encode(&mut buf)?;
                    self.sock.send_to(&buf[..n], from)?;

                    self.admin_challenges_cleanup();
                }
                admin::Packet::AdminCommand(p) => {
                    trace!("{}: recv {:?}", from, p);
                    let entry = *self
                        .admin_challenges
                        .get(from.ip())
                        .ok_or(Error::AdminChallengeNotFound)?;

                    if entry.0 != p.master_challenge {
                        trace!("{}: master challenge is not valid", from);
                        return Ok(());
                    }

                    if !entry.is_valid(now, self.timeout.challenge) {
                        trace!("{}: challenge is outdated", from);
                        return Ok(());
                    }

                    let state = Params::new()
                        .hash_length(self.hash.len)
                        .key(self.hash.key.as_bytes())
                        .personal(self.hash.personal.as_bytes())
                        .to_state();

                    let admin = self.admin_list.iter().find(|i| {
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
        }

        Ok(())
    }

    fn now(&self) -> u32 {
        self.start_time.elapsed().as_secs() as u32
    }

    fn add_challenge(&mut self, addr: SocketAddrV4) -> u32 {
        let x = self.rng.u32(..);
        let entry = Entry::new(self.now(), x);
        self.challenges.insert(addr, entry);
        x
    }

    fn remove_outdated_challenges(&mut self) {
        if self.challenges_counter.next() {
            let now = self.now();
            self.challenges
                .retain(|_, v| v.is_valid(now, self.timeout.challenge));
        }
    }

    fn admin_challenge_add(&mut self, addr: SocketAddrV4) -> (u32, u32) {
        let x = self.rng.u32(..);
        let y = self.rng.u32(..);
        let entry = Entry::new(self.now(), (x, y));
        self.admin_challenges.insert(*addr.ip(), entry);
        (x, y)
    }

    fn admin_challenge_remove(&mut self, addr: SocketAddrV4) {
        self.admin_challenges.remove(addr.ip());
    }

    /// Remove outdated entries
    fn admin_challenges_cleanup(&mut self) {
        if self.admin_challenges_counter.next() {
            let now = self.now();
            self.admin_challenges
                .retain(|_, v| v.is_valid(now, self.timeout.challenge));
        }
    }

    fn admin_limit_cleanup(&mut self) {
        if self.admin_limit_counter.next() {
            let now = self.now();
            self.admin_limit
                .retain(|_, v| v.is_valid(now, self.timeout.admin));
        }
    }

    fn add_server(&mut self, addr: SocketAddrV4, server: ServerInfo) {
        match self.servers.insert(addr, Entry::new(self.now(), server)) {
            Some(_) => trace!("{}: Updated GameServer", addr),
            None => trace!("{}: New GameServer", addr),
        }
    }

    fn remove_outdated_servers(&mut self) {
        if self.servers_counter.next() {
            let now = self.now();
            self.servers
                .retain(|_, v| v.is_valid(now, self.timeout.server));
        }
    }

    fn send_server_list<A, I>(&self, to: A, iter: I) -> Result<(), Error>
    where
        A: ToSocketAddrs,
        I: Iterator<Item = SocketAddrV4>,
    {
        let mut list = master::QueryServersResponse::new(iter);
        loop {
            let mut buf = [0; MAX_PACKET_SIZE];
            let (n, is_end) = list.encode(&mut buf)?;
            self.sock.send_to(&buf[..n], &to)?;
            if is_end {
                break;
            }
        }
        Ok(())
    }

    #[inline]
    fn is_blocked(&self, ip: &Ipv4Addr) -> bool {
        self.blocklist.contains(ip)
    }

    fn admin_command(&mut self, cmd: &str) {
        let args: Vec<_> = cmd.split(' ').collect();

        fn helper<F: FnMut(&str, Ipv4Addr)>(args: &[&str], mut op: F) {
            let iter = args.iter().map(|i| (i, i.parse::<Ipv4Addr>()));
            for (i, ip) in iter {
                match ip {
                    Ok(ip) => op(i, ip),
                    Err(_) => warn!("invalid ip: {}", i),
                }
            }
        }

        match args[0] {
            "ban" => {
                helper(&args[1..], |_, ip| {
                    if self.blocklist.insert(ip) {
                        info!("ban ip: {}", ip);
                    }
                });
            }
            "unban" => {
                helper(&args[1..], |_, ip| {
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

pub fn run(cfg: Config) -> Result<(), Error> {
    MasterServer::new(cfg)?.run()
}
