use std::{
    cmp,
    collections::{HashMap, HashSet},
    net::SocketAddr,
    time::{Duration, Instant},
};

use serde::Serialize;
use xash3d_observer::{Handler, Observer};

use crate::{
    cli::Cli,
    color::Colored,
    print_json,
    server_info::ServerInfo,
    server_result::{ServerResult, ServerResultKind},
    ProtocolError, QueryError,
};

#[derive(Clone, Debug, Serialize)]
struct InfoResult<'a> {
    protocol: &'a [u8],
    master_timeout: u64,
    server_timeout: u64,
    masters: &'a [Box<str>],
    filter: &'a str,
    servers: &'a [&'a ServerResult],
}

struct CollectServerInfo {
    start_time: Instant,
    master_timeout: Duration,
    server_timeout: Duration,
    is_custom_servers: bool,
    custom_servers: Vec<SocketAddr>,
    servers: HashMap<SocketAddr, ServerResult>,
    pending: HashSet<SocketAddr>,
}

impl CollectServerInfo {
    fn new(cli: &Cli, custom_servers: Vec<SocketAddr>) -> Self {
        let pending = custom_servers.iter().copied().collect();

        Self {
            start_time: Instant::now(),
            master_timeout: cli.master_timeout,
            server_timeout: cli.server_timeout,
            is_custom_servers: !custom_servers.is_empty(),
            custom_servers,
            servers: HashMap::new(),
            pending,
        }
    }

    fn insert(&mut self, addr: SocketAddr, result: ServerResult) {
        // do not fetch info for this server again
        self.custom_servers.retain(|i| *i != addr);

        self.pending.remove(&addr);
        self.servers.insert(addr, result);
    }
}

impl Handler for CollectServerInfo {
    fn stop_observer(&mut self) -> bool {
        // early exit if received results for all custom servers
        if self.is_custom_servers && !self.servers.is_empty() && self.pending.is_empty() {
            return true;
        }

        let mut timeout = self.server_timeout;
        if !self.is_custom_servers {
            timeout = cmp::max(timeout, self.master_timeout);
        }

        timeout < self.start_time.elapsed()
    }

    fn extra_servers(&mut self) -> &[SocketAddr] {
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
            master_timeout: cli.master_timeout.as_secs(),
            server_timeout: cli.server_timeout.as_secs(),
            masters: &cli.masters,
            filter: &cli.filter,
            servers,
        };

        if cli.json {
            print_json(cli, &result);
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
                ServerResultKind::Ping => unreachable!(),
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

fn run(cli: &Cli, mut observer: Observer<CollectServerInfo>) -> Result<(), QueryError> {
    observer.run()?;
    let handler = observer.into_handler();

    let mut servers: Vec<_> = handler.servers.values().collect();
    servers.sort_by_key(|a| a.address);
    print_server_info(cli, &servers);

    Ok(())
}

pub(crate) fn run_all(cli: &Cli) -> Result<(), QueryError> {
    let handler = CollectServerInfo::new(cli, Vec::new());
    let observer = crate::create_observer(cli, handler)?;
    run(cli, observer)
}

pub(crate) fn run_custom_servers(cli: &Cli, servers: Vec<SocketAddr>) -> Result<(), QueryError> {
    if servers.is_empty() {
        return Ok(());
    }
    let handler = CollectServerInfo::new(cli, servers);
    let observer = crate::create_observer_no_masters(cli, handler)?;
    run(cli, observer)
}
