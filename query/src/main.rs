// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

mod cli;

use std::cmp;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::io;
use std::net::{Ipv4Addr, SocketAddrV4, UdpSocket};
use std::process;
use std::sync::{mpsc, Arc};
use std::thread;
use std::time::{Duration, Instant};

use serde::{Serialize, Serializer};
use thiserror::Error;
use xash3d_protocol::types::Str;
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
enum ServerResultKind {
    #[serde(rename = "ok")]
    Ok { info: ServerInfo },
    #[serde(rename = "error")]
    Error { message: String },
    #[serde(rename = "invalid")]
    Invalid { message: String, response: String },
    #[serde(rename = "timeout")]
    Timeout,
    #[serde(rename = "protocol")]
    Protocol,
}

#[derive(Clone, Debug, Serialize)]
struct ServerResult {
    address: String,
    ping: f32,
    #[serde(flatten)]
    kind: ServerResultKind,
}

impl ServerResult {
    fn new(address: String, ping: f32, kind: ServerResultKind) -> Self {
        Self {
            address: address.to_string(),
            ping,
            kind,
        }
    }

    fn ok(address: String, ping: f32, info: ServerInfo) -> Self {
        Self::new(address, ping, ServerResultKind::Ok { info })
    }

    fn timeout(address: String) -> Self {
        Self::new(address, 0.0, ServerResultKind::Timeout)
    }

    fn protocol(address: String, ping: f32) -> Self {
        Self::new(address, ping, ServerResultKind::Protocol)
    }

    fn error<T>(address: String, message: T) -> Self
    where
        T: fmt::Display,
    {
        Self::new(
            address,
            0.0,
            ServerResultKind::Error {
                message: message.to_string(),
            },
        )
    }

    fn invalid<T>(address: String, ping: f32, message: T, response: &[u8]) -> Self
    where
        T: fmt::Display,
    {
        Self::new(
            address,
            ping,
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
    servers: &'a [&'a str],
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

enum Message {
    Servers(Vec<String>),
    ServerResult(ServerResult),
    End,
}

fn cmp_address(a: &str, b: &str) -> cmp::Ordering {
    match (a.parse::<SocketAddrV4>(), b.parse::<SocketAddrV4>()) {
        (Ok(a), Ok(b)) => a.cmp(&b),
        _ => a.cmp(b),
    }
}

fn query_servers(
    host: &str,
    cli: &Cli,
    timeout: Duration,
    tx: &mpsc::Sender<Message>,
) -> Result<(), Error> {
    let sock = UdpSocket::bind("0.0.0.0:0")?;
    sock.connect(host)?;

    let mut buf = [0; 512];
    let p = game::QueryServers {
        region: server::Region::RestOfTheWorld,
        last: SocketAddrV4::new(Ipv4Addr::new(0, 0, 0, 0), 0),
        filter: cli.filter.as_str(),
    };
    let n = p.encode(&mut buf)?;
    sock.send(&buf[..n])?;

    let start_time = Instant::now();
    while let Some(timeout) = timeout.checked_sub(start_time.elapsed()) {
        sock.set_read_timeout(Some(timeout))?;
        let n = match sock.recv(&mut buf) {
            Ok(n) => n,
            Err(e) => match e.kind() {
                io::ErrorKind::AddrInUse | io::ErrorKind::WouldBlock => break,
                _ => Err(e)?,
            },
        };
        if let Ok(packet) = master::QueryServersResponse::decode(&buf[..n]) {
            tx.send(Message::Servers(
                packet.iter().map(|i| i.to_string()).collect(),
            ))
            .unwrap();
        } else {
            eprintln!("Unexpected packet from master {}", host);
        }
    }

    Ok(())
}

fn get_server_info(
    addr: String,
    versions: &[u8],
    timeout: Duration,
) -> Result<ServerResult, Error> {
    let sock = UdpSocket::bind("0.0.0.0:0")?;
    sock.connect(&addr)?;
    sock.set_read_timeout(Some(timeout))?;

    let mut ping = 0.0;
    for &i in versions {
        let p = game::GetServerInfo::new(i);
        let mut buf = [0; 2048];
        let n = p.encode(&mut buf)?;
        let start = Instant::now();
        sock.send(&buf[..n])?;

        let n = match sock.recv(&mut buf) {
            Ok(n) => n,
            Err(e) => match e.kind() {
                io::ErrorKind::AddrInUse | io::ErrorKind::WouldBlock => {
                    return Ok(ServerResult::timeout(addr));
                }
                _ => Err(e)?,
            },
        };
        ping = start.elapsed().as_micros() as f32 / 1000.0;

        let response = &buf[..n];
        match server::GetServerInfoResponse::decode(response) {
            Ok(packet) => {
                let info = ServerInfo::from(packet);
                return Ok(ServerResult::ok(addr, ping, info));
            }
            Err(ProtocolError::InvalidProtocolVersion) => {
                // try another protocol version
            }
            Err(e) => {
                return Ok(ServerResult::invalid(addr, ping, e, response));
            }
        }
    }

    Ok(ServerResult::protocol(addr, ping))
}

fn query_server_info(cli: &Arc<Cli>, servers: &[String]) -> Result<(), Error> {
    let (tx, rx) = mpsc::channel();
    let mut workers = 0;

    if servers.is_empty() {
        for i in cli.masters.iter() {
            let master = i.to_owned();
            let tx = tx.clone();
            let timeout = Duration::from_secs(cli.master_timeout as u64);
            let cli = cli.clone();
            thread::spawn(move || {
                if let Err(e) = query_servers(&master, &cli, timeout, &tx) {
                    eprintln!("master({}) error: {}", master, e);
                }
                tx.send(Message::End).unwrap();
            });
            workers += 1;
        }
    } else {
        tx.send(Message::Servers(servers.to_vec())).unwrap();
    }

    let mut servers = HashMap::new();
    while let Ok(msg) = rx.recv() {
        match msg {
            Message::Servers(list) => {
                for address in list {
                    let tx = tx.clone();
                    let timeout = Duration::from_secs(cli.server_timeout as u64);
                    let versions = cli.protocol.clone();
                    thread::spawn(move || {
                        let result = get_server_info(address.clone(), &versions, timeout)
                            .unwrap_or_else(|e| ServerResult::error(address, e));
                        tx.send(Message::ServerResult(result)).unwrap();
                        tx.send(Message::End).unwrap();
                    });
                    workers += 1;
                }
            }
            Message::End => {
                workers -= 1;
                if workers == 0 {
                    break;
                }
            }
            Message::ServerResult(result) => {
                servers.insert(result.address.clone(), result);
            }
        }
    }

    let mut servers: Vec<_> = servers.values().collect();
    servers.sort_by(|a, b| cmp_address(&a.address, &b.address));

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
            println!("server: {} [{:.3} ms]", i.address, i.ping);

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

fn list_servers(cli: &Arc<Cli>) -> Result<(), Error> {
    let (tx, rx) = mpsc::channel();
    let mut workers = 0;

    for i in cli.masters.iter() {
        let master = i.to_owned();
        let tx = tx.clone();
        let timeout = Duration::from_secs(cli.master_timeout as u64);
        let cli = cli.clone();
        thread::spawn(move || {
            if let Err(e) = query_servers(&master, &cli, timeout, &tx) {
                eprintln!("master({}) error: {}", master, e);
            }
            tx.send(Message::End).unwrap();
        });
        workers += 1;
    }

    let mut servers = HashSet::new();
    while let Ok(msg) = rx.recv() {
        match msg {
            Message::Servers(list) => {
                servers.extend(list);
            }
            Message::End => {
                workers -= 1;
                if workers == 0 {
                    break;
                }
            }
            _ => panic!(),
        }
    }

    let mut servers: Vec<_> = servers.iter().map(|i| i.as_str()).collect();
    servers.sort_by(|a, b| cmp_address(a, b));

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
    let cli = Arc::new(cli);
    match cli.args.get(0).map(|s| s.as_str()).unwrap_or_default() {
        "all" | "" => query_server_info(&cli, &[])?,
        "info" => query_server_info(&cli, &cli.args[1..])?,
        "list" => list_servers(&cli)?,
        _ => return Err(Error::UndefinedCommand),
    }

    Ok(())
}

fn main() {
    let cli = cli::parse();

    if let Err(e) = execute(cli) {
        eprintln!("error: {}", e);
        process::exit(1);
    }
}
