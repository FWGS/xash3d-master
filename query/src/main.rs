// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

mod cli;

use std::cmp;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::io;
use std::net::{Ipv4Addr, SocketAddrV4, UdpSocket};
use std::process;
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use serde::Serialize;
use thiserror::Error;
use xash3d_protocol::types::Str;
use xash3d_protocol::{filter, game, master, server, Error as ProtocolError};

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
#[serde(tag = "type")]
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
    #[serde(flatten)]
    kind: ServerResultKind,
}

impl ServerResult {
    fn new(address: String, kind: ServerResultKind) -> Self {
        Self {
            address: address.to_string(),
            kind,
        }
    }

    fn ok<T: Into<ServerInfo>>(address: String, info: T) -> Self {
        Self::new(address, ServerResultKind::Ok { info: info.into() })
    }

    fn timeout(address: String) -> Self {
        Self::new(address, ServerResultKind::Timeout)
    }

    fn protocol(address: String) -> Self {
        Self::new(address, ServerResultKind::Protocol)
    }

    fn error<T>(address: String, message: T) -> Self
    where
        T: fmt::Display,
    {
        Self::new(
            address,
            ServerResultKind::Error {
                message: message.to_string(),
            },
        )
    }

    fn invalid<T>(address: String, message: T, response: &[u8]) -> Self
    where
        T: fmt::Display,
    {
        Self::new(
            address,
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
    pub host: String,
    pub protocol: u8,
    pub numcl: u8,
    pub maxcl: u8,
    pub dm: bool,
    pub team: bool,
    pub coop: bool,
    pub password: bool,
}

impl From<server::GetServerInfoResponse<&str>> for ServerInfo {
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
    servers: &'a [&'a ServerResult],
}

#[derive(Clone, Debug, Serialize)]
struct ListResult<'a> {
    master_timeout: u32,
    masters: &'a [Box<str>],
    servers: &'a [&'a str],
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

fn query_servers(host: &str, timeout: Duration, tx: &mpsc::Sender<Message>) -> Result<(), Error> {
    let sock = UdpSocket::bind("0.0.0.0:0")?;
    sock.connect(host)?;

    let mut buf = [0; 512];
    let p = game::QueryServers {
        region: server::Region::RestOfTheWorld,
        last: SocketAddrV4::new(Ipv4Addr::new(0, 0, 0, 0), 0),
        filter: filter::Filter {
            gamedir: b"valve",
            clver: filter::Version::new(0, 20),
            // TODO: filter
            ..Default::default()
        },
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

    for &i in versions {
        let p = game::GetServerInfo::new(i);
        let mut buf = [0; 2048];
        let n = p.encode(&mut buf)?;
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

        let response = &buf[..n];
        match server::GetServerInfoResponse::decode(response) {
            Ok(packet) => {
                return Ok(ServerResult::ok(addr, packet));
            }
            Err(ProtocolError::InvalidProtocolVersion) => {
                // try another protocol version
            }
            Err(e) => {
                return Ok(ServerResult::invalid(addr, e, response));
            }
        }
    }

    Ok(ServerResult::protocol(addr))
}

fn query_server_info(cli: &Cli, servers: &[String]) -> Result<(), Error> {
    let (tx, rx) = mpsc::channel();
    let mut workers = 0;

    if servers.is_empty() {
        for i in cli.masters.iter() {
            let master = i.to_owned();
            let tx = tx.clone();
            let timeout = Duration::from_secs(cli.master_timeout as u64);
            thread::spawn(move || {
                if let Err(e) = query_servers(&master, timeout, &tx) {
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
            println!("server: {}", i.address);

            macro_rules! p {
                ($($key:ident: $value:expr),+ $(,)?) => {
                    $(println!("    {}: \"{}\"", stringify!($key), $value);)+
                };
            }

            match &i.kind {
                ServerResultKind::Ok { info } => {
                    p! {
                        type: "ok",
                        host: info.host,
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
                        type: "timeout",
                    }
                }
                ServerResultKind::Protocol => {
                    p! {
                        type: "protocol",
                    }
                }
                ServerResultKind::Error { message } => {
                    p! {
                        type: "error",
                        message: message,
                    }
                }
                ServerResultKind::Invalid { message, response } => {
                    p! {
                        type: "invalid",
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
    let (tx, rx) = mpsc::channel();
    let mut workers = 0;

    for i in cli.masters.iter() {
        let master = i.to_owned();
        let tx = tx.clone();
        let timeout = Duration::from_secs(cli.master_timeout as u64);
        thread::spawn(move || {
            if let Err(e) = query_servers(&master, timeout, &tx) {
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
