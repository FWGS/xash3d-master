use std::{
    collections::{hash_map::Entry, HashMap},
    net::SocketAddr,
    time::Duration,
};

use xash3d_observer::{event::Event, Buffer, Server};

use crate::{
    cli::Cli,
    server_info::ServerInfo,
    server_result::{ServerAddress, ServerResult, ServerResultKind},
    utils::{self, print_json},
    QueryError,
};

struct Monitor<'a> {
    cli: &'a Cli,
    servers: HashMap<SocketAddr, ServerInfo>,
    domains: HashMap<SocketAddr, String>,
}

impl<'a> Monitor<'a> {
    fn new(cli: &'a Cli) -> Self {
        Self {
            cli,
            servers: HashMap::new(),
            domains: HashMap::new(),
        }
    }

    fn print_json(&self, mut result: ServerResult) {
        if let Some(domain) = self.domains.get(&result.address.resolved) {
            result.address.domain = Some(domain.clone());
        }
        print_json(self.cli, &result);
    }

    fn print_info(&mut self, addr: SocketAddr, ping: Duration, info: ServerInfo) {
        match self.servers.entry(addr) {
            Entry::Occupied(mut e) => {
                let p = e.get().printer(self.cli);
                println!("{:24?} --- {:>7.1} {}", addr, ' ', p,);
                let p = info.printer(self.cli);
                println!("{addr:24?} +++ {ping:>7.1?} {p}");
                e.insert(info);
            }
            Entry::Vacant(e) => {
                let p = info.printer(self.cli);
                println!("{addr:24?} +++ {ping:>7.1?} {p}");
                e.insert(info);
            }
        }
    }
}

pub(crate) fn run(cli: &Cli, servers: Vec<ServerAddress>) -> Result<(), QueryError> {
    let mut observer = if servers.is_empty() {
        utils::create_observer_with_masters(cli)?
    } else {
        utils::create_observer(cli)?
    };

    let mut monitor = Monitor::new(cli);
    for addr in servers {
        if let Some(domain) = addr.domain {
            monitor.domains.insert(addr.resolved, domain);
        }
        let server = Server::new(addr.resolved);
        observer.insert_server(server);
    }

    let mut buffer = Buffer::new();
    loop {
        match observer.wait_event(&mut buffer, None)? {
            Event::ServerList(list) => {
                for addr in list.iter() {
                    let server = Server::new(addr);
                    observer.insert_server(server);
                }
            }
            Event::ServerInfo(server_info) if server_info.is_changed() => {
                let addr = *server_info.address();
                let ping = server_info.ping();
                let info = ServerInfo::from(&server_info);
                if cli.json {
                    let mut result = ServerResult::new_timeout(addr);
                    result.set_ok(ping, info);
                    monitor.print_json(result);
                } else {
                    monitor.print_info(addr, ping, info);
                }
            }
            Event::ServerInfo(server_info) if cli.json && !server_info.is_changed() => {
                let result = ServerResult::new_ping(*server_info.address(), server_info.ping());
                monitor.print_json(result);
            }
            Event::ServerInfoTimeout(addr) if cli.json => {
                let result = ServerResult::new_timeout(addr);
                monitor.print_json(result);
            }
            Event::ServerRemove(addr) if cli.json => {
                let result = ServerResult::new(addr, None, ServerResultKind::Remove);
                monitor.print_json(result);
            }
            Event::ServerRemove(addr) => {
                monitor.servers.remove(&addr);
            }
            _ => {}
        }
    }
}
