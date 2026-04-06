use std::{
    cmp,
    collections::{HashMap, HashSet},
    net::SocketAddr,
    process,
    time::{Duration, Instant},
};

use serde::Serialize;
use xash3d_observer::Handler;

use crate::{
    cli::Cli,
    color::Colored,
    server_info::ServerInfo,
    server_result::{ServerResult, ServerResultKind},
    ProtocolError, QueryError,
};

#[derive(Clone, Debug, Serialize)]
struct InfoResult<'a> {
    protocol: &'a [u8],
    master_timeout: u32,
    server_timeout: u32,
    masters: &'a [Box<str>],
    filter: &'a str,
    servers: &'a [&'a ServerResult],
}

struct CollectServerInfo {
    start_time: Instant,
    master_timeout: Duration,
    server_timeout: Duration,
    custom_servers: Vec<SocketAddr>,
    servers: HashMap<SocketAddr, ServerResult>,
    pending: HashSet<SocketAddr>,
}

impl CollectServerInfo {
    fn new(cli: &Cli, custom_servers: Vec<SocketAddr>) -> Self {
        Self {
            start_time: Instant::now(),
            master_timeout: Duration::from_secs(cli.master_timeout as u64),
            server_timeout: Duration::from_secs(cli.server_timeout as u64),
            custom_servers,
            servers: HashMap::with_capacity(128),
            pending: HashSet::with_capacity(128),
        }
    }

    fn insert(&mut self, addr: SocketAddr, result: ServerResult) {
        self.pending.remove(&addr);
        self.servers.insert(addr, result);
    }
}

impl Handler for CollectServerInfo {
    fn stop_observer(&mut self) -> bool {
        if !self.servers.is_empty() && self.pending.is_empty() {
            return true;
        }

        let mut timeout = self.server_timeout;
        if self.custom_servers.is_empty() {
            timeout = cmp::max(timeout, self.master_timeout);
        } else if self.servers.len() == self.custom_servers.len() {
            return true;
        }

        timeout < self.start_time.elapsed()
    }

    fn query_servers_from_master(&mut self, _: SocketAddr) -> bool {
        self.custom_servers.is_empty()
    }

    fn extra_servers(&mut self) -> &[SocketAddr] {
        self.pending.extend(&self.custom_servers);
        self.custom_servers.as_slice()
    }

    fn query_info_for_server(&mut self, _: SocketAddr, server: SocketAddr) -> bool {
        if self.servers.contains_key(&server) {
            return false;
        }

        self.pending.insert(server);
        true
    }

    fn server_update(
        &mut self,
        addr: SocketAddr,
        info: &xash3d_observer::GetServerInfoResponse,
        _: bool,
        ping: Duration,
    ) {
        let info = ServerInfo::from(info);
        let res = ServerResult::ok(addr, ping, info);
        self.insert(addr, res);
    }

    fn server_timeout(&mut self, addr: SocketAddr) {
        let res = ServerResult::timeout(addr);
        self.insert(addr, res);
    }

    fn server_invalid_protocol(&mut self, addr: SocketAddr, ping: Duration) {
        let res = ServerResult::invalid_protocol(addr, ping);
        self.insert(addr, res);
    }

    fn server_invalid_packet(
        &mut self,
        addr: SocketAddr,
        ping: Duration,
        packet: &[u8],
        error: ProtocolError,
    ) {
        let res = ServerResult::invalid_packet(addr, ping, error.to_string(), packet);
        self.insert(addr, res);
    }
}

fn print_server_info(cli: &Cli, servers: &[&ServerResult]) {
    if cli.json || cli.debug {
        let result = InfoResult {
            protocol: &cli.protocol,
            master_timeout: cli.master_timeout,
            server_timeout: cli.server_timeout,
            masters: &cli.masters,
            filter: &cli.filter,
            servers,
        };

        if cli.json {
            println!("{}", serde_json::to_string_pretty(&result).unwrap());
        } else if cli.debug {
            println!("{result:#?}");
        } else {
            todo!()
        }
    } else {
        for i in servers {
            print!("server: {}", i.address);
            if let Some(ping) = i.ping {
                print!(" [{ping:.3} ms]");
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
                ServerResultKind::InvalidProtocol => {
                    p! {
                        status: "protocol",
                    }
                }
                ServerResultKind::InvalidPacket { message, response } => {
                    p! {
                        status: "invalid",
                        message: message,
                        response: response,
                    }
                }
                ServerResultKind::Remove => unreachable!(),
            }
            println!();
        }
    }
}

pub(crate) fn run(cli: &Cli, servers: &[String]) -> Result<(), QueryError> {
    let mut custom_servers = Vec::with_capacity(servers.len());
    for i in servers {
        match i.parse() {
            Ok(addr) => custom_servers.push(addr),
            Err(_) => eprintln!("invalid address {i}"),
        }
    }
    if servers.len() != custom_servers.len() {
        process::exit(1);
    }

    let handler = CollectServerInfo::new(cli, custom_servers);
    let mut observer = crate::create_observer(cli, handler)?;
    observer.run()?;
    let handler = observer.into_handler();

    let mut servers: Vec<_> = handler.servers.values().collect();
    servers.sort_by(|a, b| a.address.cmp(&b.address));
    print_server_info(cli, &servers);

    Ok(())
}
