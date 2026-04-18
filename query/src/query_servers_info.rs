use std::{
    collections::{hash_map::Entry, HashMap, HashSet},
    net::SocketAddr,
    time::{Duration, Instant},
};

use serde::Serialize;
use xash3d_observer::{event::Event, Buffer, ObserverNew, Server};
use xash3d_protocol::PROTOCOL_VERSION;

use crate::{
    cli::Cli,
    color::Colored,
    server_info::{PlayerInfo, Players, ServerInfo},
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
    servers: &'a [ServerResult],
}

struct Printer<'a> {
    servers: &'a [ServerResult],
    /// Temporary storage for players.
    players: Vec<&'a PlayerInfo>,
}

impl<'a> Printer<'a> {
    fn new(servers: &'a [ServerResult]) -> Self {
        Self {
            servers,
            players: Vec::new(),
        }
    }

    fn print_json(&self, cli: &Cli) {
        let result = InfoResult {
            protocol: &cli.protocol,
            master_timeout: cli.master_timeout.as_secs(),
            server_timeout: cli.server_timeout.as_secs(),
            masters: &cli.masters,
            filter: &cli.filter,
            servers: self.servers,
        };

        if cli.json {
            print_json(cli, &result);
        } else if cli.debug {
            println!("{result:#?}");
        } else {
            unreachable!()
        }
    }

    fn print_server(&mut self, cli: &Cli, i: usize, server: &'a ServerResult) {
        let ServerResultKind::Ok { info } = &server.kind else {
            return;
        };

        if i > 0 {
            println!();
        }

        let w = 10;
        print!("{:>w$}: {}", "server", server.address);
        if let Some(ping) = server.ping_millis_f32() {
            print!(" [ping {ping:.0}ms]");
        }
        if info.protocol != PROTOCOL_VERSION {
            print!(" [protocol {}]", info.protocol);
        }
        if info.password {
            print!(" [password]");
        }
        println!();

        let host = Colored::new(&info.host, cli.force_color);
        println!("{:>w$}: {}", "name", host);
        println!("{:>w$}: {}", "game", info.gamedir);
        println!("{:>w$}: {}", "map", info.map);

        print!("{:>w$}:", "mode");
        if info.coop || info.team || info.dm {
            if info.coop {
                print!(" coop");
            }
            if info.team {
                print!(" team");
            }
            if info.dm {
                print!(" deathmatch");
            }
        } else {
            print!(" unknown");
        }
        println!();

        println!("{:>w$}: {}/{}", "players", info.numcl, info.maxcl);

        if !info.players.is_empty() {
            self.players.clear();
            self.players.extend(info.players.iter());
            self.players.sort_by_key(|i| i.frags);
            for (i, player) in self.players.iter().rev().enumerate() {
                let name = Colored::new(&player.name, cli.force_color);
                println!("{i:w$}: {} {name}", player.frags);
            }
        }
    }

    fn print(&mut self, cli: &Cli) {
        if cli.json || cli.debug {
            self.print_json(cli);
            return;
        }

        for (i, server) in self.servers.iter().enumerate() {
            self.print_server(cli, i, server);
        }
    }
}

struct QueryServersInfo {
    custom: bool,
    players: bool,
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
            players: cli.players,
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
        let server = Server::new(addr).with_players(self.players);
        self.observer.insert_server(server);

        // Set default result to timeout for all new servers.
        if let Entry::Vacant(e) = self.servers.entry(addr) {
            e.insert(ServerResult::new_timeout(addr));
        }
    }

    fn set_server_result(&mut self, addr: SocketAddr, result: ServerResult) {
        if self.custom {
            self.servers_custom.remove(&addr);
        }
        self.servers.insert(addr, result);
    }

    fn set_server_result_ok(&mut self, addr: SocketAddr, ping: Duration, info: ServerInfo) {
        let e = self
            .servers
            .entry(addr)
            .or_insert_with(|| ServerResult::new_timeout(addr));
        if self.custom && (!self.players || e.has_players()) {
            self.servers_custom.remove(&addr);
        }
        e.set_ok(ping, info);
    }

    fn set_server_players(&mut self, addr: SocketAddr, players: Players) {
        let e = self.servers.get_mut(&addr).expect("server");
        if self.custom && (!self.players || e.is_ok()) {
            self.servers_custom.remove(&addr);
        }
        e.set_players(players);
    }

    fn run(mut self, cli: &Cli) -> Result<(), QueryError> {
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
                    self.set_server_result_ok(addr, server_info.ping(), info);
                }
                Event::ServerPlayers(addr, players) => {
                    self.set_server_players(addr, players.into());
                }
                Event::ServerInvalidProtocol(addr) => {
                    let result = ServerResult::new_invalid_protocol(addr);
                    self.set_server_result(addr, result);
                }
                Event::ServerInvalidPacket(addr, data) => {
                    let result = self.servers.get(&addr);
                    if result.is_none() || result.is_some_and(|i| i.kind.is_timeout()) {
                        let result = ServerResult::new_invalid_packet(addr, data);
                        self.set_server_result(addr, result);
                    }
                }
                _ => {}
            }

            remaining = self.timeout.checked_sub(start_time.elapsed());
        }

        let mut servers: Vec<_> = self.servers.into_values().collect();
        servers.sort_by_key(|a| a.address);
        Printer::new(&servers).print(cli);

        Ok(())
    }
}

pub(crate) fn run(cli: &Cli) -> Result<(), QueryError> {
    let observer = utils::create_observer_with_masters(cli)?;
    let query = QueryServersInfo::new(cli, observer, false);
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
