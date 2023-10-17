// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::collections::HashMap;
use std::io;
use std::net::{SocketAddr, SocketAddrV4, ToSocketAddrs, UdpSocket};
use std::ops::Deref;
use std::time::Instant;

use fastrand::Rng;
use log::{error, info, trace, warn};
use thiserror::Error;
use xash3d_protocol::filter::{Filter, Version};
use xash3d_protocol::server::Region;
use xash3d_protocol::{ServerInfo, admin, game, master, server, Error as ProtocolError};

use crate::config::{self, Config};

/// The maximum size of UDP packets.
const MAX_PACKET_SIZE: usize = 512;

/// How many cleanup calls should be skipped before removing outdated servers.
const SERVER_CLEANUP_MAX: usize = 100;

/// How many cleanup calls should be skipped before removing outdated challenges.
const CHALLENGE_CLEANUP_MAX: usize = 100;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Failed to bind server socket: {0}")]
    BindSocket(io::Error),
    #[error(transparent)]
    Protocol(#[from] ProtocolError),
    #[error(transparent)]
    Io(#[from] io::Error),
}

/// HashMap entry to keep tracking creation time.
#[derive(Clone, Debug)]
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

struct MasterServer {
    sock: UdpSocket,
    challenges: HashMap<SocketAddrV4, Entry<u32>>,
    servers: HashMap<SocketAddrV4, Entry<ServerInfo>>,
    rng: Rng,

    start_time: Instant,
    cleanup_challenges: usize,
    cleanup_servers: usize,
    timeout: config::TimeoutConfig,

    clver: Version,
    update_title: Box<str>,
    update_map: Box<str>,
    update_addr: SocketAddrV4,
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
            servers: Default::default(),
            rng: Rng::new(),
            cleanup_challenges: 0,
            cleanup_servers: 0,
            timeout: cfg.server.timeout,
            clver: cfg.client.version,
            update_title: cfg.client.update_title,
            update_map: cfg.client.update_map,
            update_addr,
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

        if let Ok(p) = admin::Packet::decode(src) {
            match p {
                admin::Packet::AdminChallenge(p) => {
                    trace!("{}: recv {:?}", from, p);
                    let challenge = 0x12345678; // TODO:
                    let p = master::AdminChallengeResponse::new(challenge);
                    let mut buf = [0; 64];
                    let n = p.encode(&mut buf)?;
                    self.sock.send_to(&buf[..n], from)?;
                }
                admin::Packet::AdminCommand(p) => {
                    trace!("{}: recv {:?}", from, p);
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
        if self.cleanup_challenges < CHALLENGE_CLEANUP_MAX {
            self.cleanup_challenges += 1;
            return;
        }
        let now = self.now();
        let old = self.challenges.len();
        self.challenges
            .retain(|_, v| v.is_valid(now, self.timeout.challenge));
        let new = self.challenges.len();
        if old != new {
            trace!("Removed {} outdated challenges", old - new);
        }
        self.cleanup_challenges = 0;
    }

    fn add_server(&mut self, addr: SocketAddrV4, server: ServerInfo) {
        match self.servers.insert(addr, Entry::new(self.now(), server)) {
            Some(_) => trace!("{}: Updated GameServer", addr),
            None => trace!("{}: New GameServer", addr),
        }
    }

    fn remove_outdated_servers(&mut self) {
        if self.cleanup_servers < SERVER_CLEANUP_MAX {
            self.cleanup_servers += 1;
            return;
        }
        let now = self.now();
        let old = self.servers.len();
        self.servers
            .retain(|_, v| v.is_valid(now, self.timeout.server));
        let new = self.servers.len();
        if old != new {
            trace!("Removed {} outdated servers", old - new);
        }
        self.cleanup_servers = 0;
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
}

pub fn run(cfg: Config) -> Result<(), Error> {
    MasterServer::new(cfg)?.run()
}
