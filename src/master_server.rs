// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::collections::HashMap;
use std::io::prelude::*;
use std::io::{self, Cursor};
use std::net::{SocketAddr, SocketAddrV4, ToSocketAddrs, UdpSocket};
use std::ops::Deref;
use std::time::Instant;

use fastrand::Rng;
use log::{error, info, trace, warn};
use thiserror::Error;

use crate::client::Packet;
use crate::config::{self, Config};
use crate::filter::Filter;
use crate::server::Server;
use crate::server_info::Region;

/// The maximum size of UDP packets.
const MAX_PACKET_SIZE: usize = 512;

const CHALLENGE_RESPONSE_HEADER: &[u8] = b"\xff\xff\xff\xffs\n";
const SERVER_LIST_HEADER: &[u8] = b"\xff\xff\xff\xfff\n";

/// How many cleanup calls should be skipped before removing outdated servers.
const SERVER_CLEANUP_MAX: usize = 100;

/// How many cleanup calls should be skipped before removing outdated challenges.
const CHALLENGE_CLEANUP_MAX: usize = 100;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Failed to bind server socket: {0}")]
    BindSocket(io::Error),
    #[error("Failed to decode packet: {0}")]
    ClientPacket(#[from] crate::client::Error),
    #[error("Missing challenge in ServerInfo")]
    MissingChallenge,
    #[error(transparent)]
    Io(#[from] io::Error),
}

/// HashMap entry to keep tracking creation time.
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

impl Entry<Server> {
    fn matches(&self, addr: SocketAddrV4, region: Region, filter: &Filter) -> bool {
        self.region == region && filter.matches(addr, self)
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
    start_time: Instant,
    challenges: HashMap<SocketAddrV4, Entry<u32>>,
    servers: HashMap<SocketAddrV4, Entry<Server>>,
    rng: Rng,
    cleanup_challenges: usize,
    cleanup_servers: usize,
    timeout: config::TimeoutConfig,
}

impl MasterServer {
    fn new(cfg: Config) -> Result<Self, Error> {
        let addr = SocketAddr::new(cfg.server.ip, cfg.server.port);
        info!("Listen address: {}", addr);
        let sock = UdpSocket::bind(addr).map_err(Error::BindSocket)?;

        Ok(Self {
            sock,
            start_time: Instant::now(),
            challenges: Default::default(),
            servers: Default::default(),
            rng: Rng::new(),
            cleanup_challenges: 0,
            cleanup_servers: 0,
            timeout: cfg.server.timeout,
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

    fn handle_packet(&mut self, from: SocketAddrV4, s: &[u8]) -> Result<(), Error> {
        let packet = Packet::decode(s)?;
        trace!("{}: recv {:?}", from, packet);

        match packet {
            Packet::Challenge(server_challenge) => {
                let challenge = self.add_challenge(from);
                trace!("{}: New challenge {}", from, challenge);
                self.send_challenge_response(from, challenge, server_challenge)?;
                self.remove_outdated_challenges();
            }
            Packet::ServerAdd(challenge, info) => {
                let challenge = match challenge {
                    Some(c) => c,
                    None => return Err(Error::MissingChallenge),
                };
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
                if challenge != entry.value {
                    warn!(
                        "{}: Expected challenge {} but received {}",
                        from, entry.value, challenge
                    );
                    return Ok(());
                }
                if self.challenges.remove(&from).is_some() {
                    self.add_server(from, Server::new(&info));
                }
                self.remove_outdated_servers();
            }
            Packet::ServerRemove => { /* ignore */ }
            Packet::QueryServers(region, filter) => match Filter::from_bytes(&filter) {
                Ok(filter) => self.send_server_list(from, region, &filter)?,
                _ => {
                    warn!("{}: Invalid filter: {:?}", from, filter);
                    return Ok(());
                }
            },
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

    fn add_server(&mut self, addr: SocketAddrV4, server: Server) {
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

    fn send_challenge_response<A: ToSocketAddrs>(
        &self,
        to: A,
        challenge: u32,
        server_challenge: Option<u32>,
    ) -> Result<(), io::Error> {
        let mut buf = [0; MAX_PACKET_SIZE];
        let mut cur = Cursor::new(&mut buf[..]);

        cur.write_all(CHALLENGE_RESPONSE_HEADER)?;
        cur.write_all(&challenge.to_le_bytes())?;
        if let Some(x) = server_challenge {
            cur.write_all(&x.to_le_bytes())?;
        }

        let n = cur.position() as usize;
        self.sock.send_to(&buf[..n], to)?;
        Ok(())
    }

    fn send_server_list<A: ToSocketAddrs>(
        &self,
        to: A,
        region: Region,
        filter: &Filter,
    ) -> Result<(), io::Error> {
        let now = self.now();
        let mut iter = self
            .servers
            .iter()
            .filter(|i| i.1.is_valid(now, self.timeout.server))
            .filter(|i| i.1.matches(*i.0, region, filter))
            .map(|i| i.0);

        let mut buf = [0; MAX_PACKET_SIZE];
        let mut done = false;
        while !done {
            let mut cur = Cursor::new(&mut buf[..]);
            cur.write_all(SERVER_LIST_HEADER)?;

            loop {
                match iter.next() {
                    Some(i) => {
                        cur.write_all(&i.ip().octets()[..])?;
                        cur.write_all(&i.port().to_be_bytes())?;
                    }
                    None => {
                        done = true;
                        break;
                    }
                }

                if (cur.position() as usize) > (MAX_PACKET_SIZE - 12) {
                    break;
                }
            }

            // terminate list
            cur.write_all(&[0; 6][..])?;

            let n = cur.position() as usize;
            self.sock.send_to(&buf[..n], &to)?;
        }
        Ok(())
    }
}

pub fn run(cfg: Config) -> Result<(), Error> {
    MasterServer::new(cfg)?.run()
}
