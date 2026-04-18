use std::{
    collections::{hash_map::Entry, HashMap, HashSet},
    net::SocketAddr,
    time::{Duration, Instant},
};

use serde::Serialize;
use xash3d_observer::{event::Event, Buffer, ObserverNew};

use crate::{
    cli::Cli,
    color::Colored,
    server_info::ServerInfo,
    server_result::{ServerResult, ServerResultKind},
    utils::{self, print_json},
    QueryError,
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

fn print_server_info(cli: &Cli, servers: &HashMap<SocketAddr, ServerResult>) {
    let mut servers: Vec<_> = servers.values().collect();
    servers.sort_by_key(|a| a.address);

    if cli.json || cli.debug {
        let result = InfoResult {
            protocol: &cli.protocol,
            master_timeout: cli.master_timeout.as_secs(),
            server_timeout: cli.server_timeout.as_secs(),
            masters: &cli.masters,
            filter: &cli.filter,
            servers: &servers,
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

struct QueryServersInfo {
    custom: bool,
    timeout_master: bool,
    timeout: Duration,
    servers: HashMap<SocketAddr, ServerResult>,
    servers_custom: HashSet<SocketAddr>,
    observer: ObserverNew,
}

impl QueryServersInfo {
    fn new(cli: &Cli, observer: ObserverNew, custom: bool) -> Self {
        let (timeout, timeout_master) = if !custom {
            // Wait a response from any master server and then change to game server timeout.
            (cli.master_timeout, true)
        } else {
            (cli.server_timeout, false)
        };

        Self {
            custom,
            timeout_master,
            timeout,
            servers: HashMap::new(),
            servers_custom: HashSet::new(),
            observer,
        }
    }

    fn insert_custom_server(&mut self, addr: SocketAddr) {
        self.servers_custom.insert(addr);
        self.insert_server(addr);
    }

    fn insert_server(&mut self, addr: SocketAddr) {
        self.observer.insert_server(addr);

        // Set default result to timeout for all new servers.
        if let Entry::Vacant(e) = self.servers.entry(addr) {
            e.insert(ServerResult::timeout(addr));
        }
    }

    fn set_server_result(&mut self, addr: SocketAddr, result: ServerResult) {
        if self.custom {
            self.servers_custom.remove(&addr);
        }
        self.servers.insert(addr, result);
    }

    fn run(&mut self, cli: &Cli) -> Result<(), QueryError> {
        let mut buffer = Buffer::new();
        let mut remaining = Some(self.timeout);
        let start_time = Instant::now();
        while remaining.is_some() {
            // TODO: Do same trick for servers recevied from master servers?
            if self.custom && self.servers_custom.is_empty() {
                break;
            }

            match self.observer.wait_event(&mut buffer, remaining)? {
                Event::Timeout => break,
                Event::ServerList(list) => {
                    if self.timeout_master {
                        self.timeout_master = false;
                        self.timeout = cli.server_timeout;
                    }

                    for addr in list.iter() {
                        self.insert_server(addr);
                    }
                }
                Event::ServerInfo(server_info) => {
                    let addr = *server_info.address();
                    let info = ServerInfo::from(&server_info);
                    let result = ServerResult::ok(addr, server_info.ping(), info);
                    self.set_server_result(addr, result);
                }
                Event::ServerInvalidProtocol(addr) => {
                    let result = ServerResult::invalid_protocol(addr);
                    self.set_server_result(addr, result);
                }
                Event::ServerInvalidPacket(addr, data) => {
                    let result = self.servers.get(&addr);
                    if result.is_none() || result.is_some_and(|i| i.kind.is_timeout()) {
                        let result = ServerResult::invalid_packet(addr, data);
                        self.set_server_result(addr, result);
                    }
                }
                _ => {}
            }

            remaining = self.timeout.checked_sub(start_time.elapsed());
        }

        print_server_info(cli, &self.servers);

        Ok(())
    }
}

pub(crate) fn run(cli: &Cli) -> Result<(), QueryError> {
    let observer = utils::create_observer_with_masters(cli)?;
    let mut query = QueryServersInfo::new(cli, observer, false);
    query.run(cli)
}

pub(crate) fn run_custom_servers(cli: &Cli, servers: Vec<SocketAddr>) -> Result<(), QueryError> {
    if servers.is_empty() {
        return Ok(());
    }

    let observer = utils::create_observer(cli)?;
    let mut query = QueryServersInfo::new(cli, observer, true);
    for addr in servers {
        query.insert_custom_server(addr);
    }
    query.run(cli)
}
