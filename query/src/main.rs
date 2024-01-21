// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

mod cli;

use std::cmp;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::io;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4, UdpSocket};
use std::process;
use std::time::{Duration, Instant};

use serde::{Serialize, Serializer};
use thiserror::Error;
use xash3d_protocol::wrappers::Str;
use xash3d_protocol::{color, game, master, server, Error as ProtocolError};

use crate::cli::Cli;

#[derive(Error, Debug)]
enum Error {
    #[error("Undefined command")]
    UndefinedCommand,
    #[error(transparent)]
    Protocol(#[from] ProtocolError),
    #[error(transparent)]
    Io(#[from] io::Error),
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "status")]
#[serde(rename_all = "lowercase")]
enum ServerResultKind {
    Ok {
        #[serde(flatten)]
        info: ServerInfo,
    },
    Error {
        message: String,
    },
    Invalid {
        message: String,
        response: String,
    },
    Timeout,
    Protocol,
}

#[derive(Clone, Debug, Serialize)]
struct ServerResult {
    address: SocketAddrV4,
    #[serde(skip_serializing_if = "Option::is_none")]
    ping: Option<f32>,
    #[serde(flatten)]
    kind: ServerResultKind,
}

impl ServerResult {
    fn new(address: SocketAddrV4, ping: Option<f32>, kind: ServerResultKind) -> Self {
        Self {
            address,
            ping,
            kind,
        }
    }

    fn ok(address: SocketAddrV4, ping: f32, info: ServerInfo) -> Self {
        Self::new(address, Some(ping), ServerResultKind::Ok { info })
    }

    fn timeout(address: SocketAddrV4) -> Self {
        Self::new(address, None, ServerResultKind::Timeout)
    }

    fn protocol(address: SocketAddrV4, ping: f32) -> Self {
        Self::new(address, Some(ping), ServerResultKind::Protocol)
    }

    fn error<T>(address: SocketAddrV4, message: T) -> Self
    where
        T: fmt::Display,
    {
        Self::new(
            address,
            None,
            ServerResultKind::Error {
                message: message.to_string(),
            },
        )
    }

    fn invalid<T>(address: SocketAddrV4, ping: f32, message: T, response: &[u8]) -> Self
    where
        T: fmt::Display,
    {
        Self::new(
            address,
            Some(ping),
            ServerResultKind::Invalid {
                message: message.to_string(),
                response: Str(response).to_string(),
            },
        )
    }
}

#[derive(Clone, Debug, Serialize)]
struct ServerInfo {
    pub gamedir: String,
    pub map: String,
    #[serde(serialize_with = "serialize_colored")]
    pub host: String,
    pub protocol: u8,
    pub numcl: u8,
    pub maxcl: u8,
    pub dm: bool,
    pub team: bool,
    pub coop: bool,
    pub password: bool,
}

impl ServerInfo {
    fn from(other: server::GetServerInfoResponse<&str>) -> Self {
        Self {
            gamedir: other.gamedir.to_owned(),
            map: other.map.to_owned(),
            host: other.host.to_owned(),
            protocol: other.protocol,
            numcl: other.numcl,
            maxcl: other.maxcl,
            dm: other.dm,
            team: other.team,
            coop: other.coop,
            password: other.password,
        }
    }
}

#[derive(Clone, Debug, Serialize)]
struct InfoResult<'a> {
    protocol: &'a [u8],
    master_timeout: u32,
    server_timeout: u32,
    masters: &'a [Box<str>],
    filter: &'a str,
    servers: &'a [&'a ServerResult],
}

#[derive(Clone, Debug, Serialize)]
struct ListResult<'a> {
    master_timeout: u32,
    masters: &'a [Box<str>],
    filter: &'a str,
    servers: &'a [SocketAddrV4],
}

fn serialize_colored<S>(s: &str, ser: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    ser.serialize_str(color::trim_color(s).as_ref())
}

struct Colored<'a> {
    inner: &'a str,
    forced: bool,
}

impl<'a> Colored<'a> {
    fn new(s: &'a str, forced: bool) -> Self {
        Self { inner: s, forced }
    }
}

impl fmt::Display for Colored<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        #[cfg(feature = "color")]
        if self.forced || termion::is_tty(&io::stdout()) {
            use termion::color::*;

            for (color, text) in color::ColorIter::new(self.inner) {
                match color::Color::try_from(color) {
                    Ok(color::Color::Black) => write!(fmt, "{}", Fg(Black))?,
                    Ok(color::Color::Red) => write!(fmt, "{}", Fg(Red))?,
                    Ok(color::Color::Green) => write!(fmt, "{}", Fg(Green))?,
                    Ok(color::Color::Yellow) => write!(fmt, "{}", Fg(Yellow))?,
                    Ok(color::Color::Blue) => write!(fmt, "{}", Fg(Blue))?,
                    Ok(color::Color::Cyan) => write!(fmt, "{}", Fg(Cyan))?,
                    Ok(color::Color::Magenta) => write!(fmt, "{}", Fg(Magenta))?,
                    Ok(color::Color::White) => write!(fmt, "{}", Fg(White))?,
                    _ => {}
                }
                write!(fmt, "{}", text)?;
            }
            return write!(fmt, "{}", Fg(Reset));
        }

        for (_, text) in color::ColorIter::new(self.inner) {
            write!(fmt, "{}", text)?;
        }
        Ok(())
    }
}

fn get_socket_addrs<'a>(iter: impl Iterator<Item = &'a str>) -> Result<Vec<SocketAddrV4>, Error> {
    use std::net::ToSocketAddrs;

    let mut out = Vec::with_capacity(iter.size_hint().0);
    for i in iter {
        match i
            .to_socket_addrs()?
            .find(|i| matches!(i, SocketAddr::V4(_)))
        {
            Some(SocketAddr::V4(addr)) => out.push(addr),
            _ => eprintln!("warn: failed to resolve address for {}", i),
        }
    }

    Ok(out)
}

struct ServerQuery {
    start: Instant,
    protocol: usize,
}

impl ServerQuery {
    fn ping(&self) -> f32 {
        self.start.elapsed().as_micros() as f32 / 1000.0
    }
}

impl ServerQuery {
    fn new(protocol: usize) -> Self {
        Self {
            start: Instant::now(),
            protocol,
        }
    }
}

struct Scan<'a> {
    cli: &'a Cli,
    masters: Vec<SocketAddrV4>,
    sock: UdpSocket,
}

impl<'a> Scan<'a> {
    fn new(cli: &'a Cli) -> Result<Self, Error> {
        Ok(Self {
            cli,
            masters: get_socket_addrs(cli.masters.iter().map(|i| i.as_ref()))?,
            sock: UdpSocket::bind(SocketAddrV4::new(Ipv4Addr::new(0, 0, 0, 0), 0))?,
        })
    }

    fn is_master(&self, addr: &SocketAddrV4) -> bool {
        self.masters.iter().any(|i| i == addr)
    }

    fn query_servers(&self) -> Result<(), Error> {
        let mut buf = [0; 512];
        let packet = game::QueryServers {
            region: server::Region::RestOfTheWorld,
            last: SocketAddrV4::new(Ipv4Addr::new(0, 0, 0, 0), 0),
            filter: self.cli.filter.as_str(),
        };
        let n = packet.encode(&mut buf)?;
        let packet = &buf[..n];

        for i in &self.masters {
            self.sock.send_to(packet, i)?;
        }

        Ok(())
    }

    fn servers(&self) -> Result<HashSet<SocketAddrV4>, Error> {
        self.query_servers()?;

        let mut set = HashSet::with_capacity(256);
        let mut buf = [0; 2048];
        let timeout = Duration::from_secs(self.cli.master_timeout as u64);
        let start_time = Instant::now();

        while let Some(timeout) = timeout.checked_sub(start_time.elapsed()) {
            self.sock.set_read_timeout(Some(timeout))?;

            let (n, from) = match self.sock.recv_from(&mut buf) {
                Ok(x) => x,
                Err(e) => match e.kind() {
                    io::ErrorKind::AddrInUse => break,
                    io::ErrorKind::WouldBlock => break,
                    _ => Err(e)?,
                },
            };

            let from = match from {
                SocketAddr::V4(x) => x,
                _ => todo!(),
            };

            if self.is_master(&from) {
                if let Ok(packet) = master::QueryServersResponse::decode(&buf[..n]) {
                    if self.check_key(&from, packet.key) {
                        set.extend(packet.iter());
                    }
                } else {
                    eprintln!(
                        "warn: invalid packet from master {}, raw \"{}\"",
                        from,
                        Str(&buf[..n])
                    );
                }
            }
        }

        Ok(set)
    }

    fn server_info(
        &self,
        list: &[SocketAddrV4],
    ) -> Result<HashMap<SocketAddrV4, ServerResult>, Error> {
        let mut set = HashSet::new();
        let mut active = HashMap::new();
        let mut out = HashMap::new();
        let mut buf = [0; 2048];

        let now = Instant::now();
        let master_timeout = Duration::from_secs(self.cli.master_timeout as u64);
        let server_timeout = Duration::from_secs(self.cli.server_timeout as u64);
        let master_end = now + master_timeout;
        let mut server_end = now + server_timeout;

        if list.is_empty() {
            self.query_servers()?;
        } else {
            let mut buf = [0; 512];
            let n = game::GetServerInfo::new(self.cli.protocol[0]).encode(&mut buf)?;

            for addr in list.iter().filter(|i| set.insert(**i)) {
                match self.sock.send_to(&buf[..n], addr) {
                    Ok(_) => {
                        let query = ServerQuery::new(0);
                        server_end = query.start + server_timeout;
                        active.insert(*addr, query);
                    }
                    Err(e) => {
                        let res = ServerResult::error(*addr, e);
                        out.insert(*addr, res);
                    }
                }
            }
        }

        loop {
            let time = cmp::max(master_end, server_end);
            match time.checked_duration_since(Instant::now()) {
                Some(t) => self.sock.set_read_timeout(Some(t))?,
                None => break,
            }

            let (n, from) = match self.sock.recv_from(&mut buf) {
                Ok(x) => x,
                Err(e) => match e.kind() {
                    io::ErrorKind::AddrInUse => break,
                    io::ErrorKind::WouldBlock => break,
                    _ => Err(e)?,
                },
            };
            let from = match from {
                SocketAddr::V4(x) => x,
                _ => todo!(),
            };
            let raw = &buf[..n];

            if self.is_master(&from) {
                if let Ok(packet) = master::QueryServersResponse::decode(raw) {
                    if self.check_key(&from, packet.key) {
                        for addr in packet.iter().filter(|i| set.insert(*i)) {
                            let mut buf = [0; 512];
                            let n =
                                game::GetServerInfo::new(self.cli.protocol[0]).encode(&mut buf)?;

                            match self.sock.send_to(&buf[..n], addr) {
                                Ok(_) => {
                                    let query = ServerQuery::new(0);
                                    server_end = query.start + server_timeout;
                                    active.insert(addr, query);
                                }
                                Err(e) => {
                                    let res = ServerResult::error(addr, e);
                                    out.insert(addr, res);
                                }
                            }
                        }
                    }
                }
            } else if let Some(query) = active.remove(&from) {
                match server::GetServerInfoResponse::decode(raw) {
                    Ok(packet) => {
                        let info = ServerInfo::from(packet);
                        let res = ServerResult::ok(from, query.ping(), info);
                        out.insert(from, res);
                    }
                    Err(ProtocolError::InvalidProtocolVersion) => {
                        let next_protocol = query.protocol + 1;
                        if let Some(protocol) = self.cli.protocol.get(next_protocol) {
                            let mut buf = [0; 512];
                            let n = game::GetServerInfo::new(*protocol).encode(&mut buf)?;

                            match self.sock.send_to(&buf[..n], from) {
                                Ok(_) => {
                                    active.insert(from, ServerQuery::new(next_protocol));
                                }
                                Err(e) => {
                                    let res = ServerResult::error(from, e);
                                    out.insert(from, res);
                                }
                            }
                        } else {
                            let res = ServerResult::protocol(from, query.ping());
                            out.insert(from, res);
                        }
                    }
                    Err(e) => {
                        let res = ServerResult::invalid(from, query.ping(), e, raw);
                        out.insert(from, res);
                    }
                }
            }
        }

        for (addr, _) in active {
            let res = ServerResult::timeout(addr);
            out.insert(addr, res);
        }

        Ok(out)
    }

    fn check_key(&self, from: &SocketAddrV4, key: Option<u32>) -> bool {
        let res = match (self.cli.key, key) {
            (Some(a), Some(b)) => a == b,
            (None, None) => true,
            _ => false,
        };
        if !res {
            eprintln!("error: invalid key from master({})", from);
        }
        res
    }
}

fn query_server_info(cli: &Cli, servers: &[String]) -> Result<(), Error> {
    let scan = Scan::new(cli)?;
    let servers = get_socket_addrs(servers.iter().map(|i| i.as_str()))?;
    let servers = scan.server_info(&servers)?;

    let mut servers: Vec<_> = servers.values().collect();
    servers.sort_by(|a, b| a.address.cmp(&b.address));

    if cli.json || cli.debug {
        let result = InfoResult {
            protocol: &cli.protocol,
            master_timeout: cli.master_timeout,
            server_timeout: cli.server_timeout,
            masters: &cli.masters,
            filter: &cli.filter,
            servers: &servers,
        };

        if cli.json {
            println!("{}", serde_json::to_string_pretty(&result).unwrap());
        } else if cli.debug {
            println!("{:#?}", result);
        } else {
            todo!()
        }
    } else {
        for i in servers {
            print!("server: {}", i.address);
            if let Some(ping) = i.ping {
                print!(" [{:.3} ms]", ping);
            }
            println!();

            macro_rules! p {
                ($($key:ident: $value:expr),+ $(,)?) => {
                    $(println!("    {}: \"{}\"", stringify!($key), $value);)+
                };
            }

            match &i.kind {
                ServerResultKind::Ok { info } => {
                    p! {
                        status: "ok",
                        host: Colored::new(&info.host, cli.force_color),
                        gamedir: info.gamedir,
                        map: info.map,
                        protocol: info.protocol,
                        numcl: info.numcl,
                        maxcl: info.maxcl,
                        dm: info.dm,
                        team: info.team,
                        coop: info.coop,
                        password: info.password,
                    }
                }
                ServerResultKind::Timeout => {
                    p! {
                        status: "timeout",
                    }
                }
                ServerResultKind::Protocol => {
                    p! {
                        status: "protocol",
                    }
                }
                ServerResultKind::Error { message } => {
                    p! {
                        status: "error",
                        message: message,
                    }
                }
                ServerResultKind::Invalid { message, response } => {
                    p! {
                        status: "invalid",
                        message: message,
                        response: response,
                    }
                }
            }
            println!();
        }
    }

    Ok(())
}

fn list_servers(cli: &Cli) -> Result<(), Error> {
    let scan = Scan::new(cli)?;
    let mut servers: Vec<_> = scan.servers()?.into_iter().collect();
    servers.sort();

    if cli.json || cli.debug {
        let result = ListResult {
            master_timeout: cli.master_timeout,
            masters: &cli.masters,
            filter: &cli.filter,
            servers: &servers,
        };

        if cli.json {
            println!("{}", serde_json::to_string_pretty(&result).unwrap());
        } else if cli.debug {
            println!("{:#?}", result);
        } else {
            todo!()
        }
    } else {
        for i in servers {
            println!("{}", i);
        }
    }

    Ok(())
}

fn execute(cli: Cli) -> Result<(), Error> {
    match cli.args.first().map(|s| s.as_str()).unwrap_or_default() {
        "all" | "" => query_server_info(&cli, &[])?,
        "info" => query_server_info(&cli, &cli.args[1..])?,
        "list" => list_servers(&cli)?,
        _ => return Err(Error::UndefinedCommand),
    }

    Ok(())
}

fn main() {
    let cli = cli::parse();

    // suppress broken pipe error
    unsafe {
        libc::signal(libc::SIGPIPE, libc::SIG_DFL);
    }

    if let Err(e) = execute(cli) {
        eprintln!("error: {}", e);
        process::exit(1);
    }
}
