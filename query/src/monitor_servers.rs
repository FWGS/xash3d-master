use std::{
    collections::{hash_map::Entry, HashMap},
    net::SocketAddr,
};

use xash3d_observer::{event::Event, Buffer};

use crate::{
    cli::Cli,
    server_info::ServerInfo,
    server_result::{ServerResult, ServerResultKind},
    utils::{self, print_json},
    QueryError,
};

pub(crate) fn run(cli: &Cli, servers: Vec<SocketAddr>) -> Result<(), QueryError> {
    let mut observer = if servers.is_empty() {
        utils::create_observer_with_masters(cli)?
    } else {
        utils::create_observer(cli)?
    };

    for addr in servers {
        observer.insert_server(addr);
    }

    let mut servers = HashMap::<SocketAddr, ServerInfo>::new();
    let mut buffer = Buffer::new();
    loop {
        match observer.wait_event(&mut buffer, None)? {
            Event::ServerList(list) => {
                for addr in list.iter() {
                    observer.insert_server(addr);
                }
            }
            Event::ServerInfo(server_info) if server_info.is_changed() => {
                let addr = *server_info.address();
                let ping = server_info.ping();
                let info = ServerInfo::from(&server_info);
                if cli.json {
                    let result = ServerResult::ok(addr, ping, info);
                    print_json(cli, &result);
                } else {
                    match servers.entry(addr) {
                        Entry::Occupied(mut e) => {
                            let p = e.get().printer(cli);
                            println!("{:24?} --- {:>7.1} {}", addr, ' ', p,);
                            let p = info.printer(cli);
                            println!("{addr:24?} +++ {ping:>7.1?} {p}");
                            e.insert(info);
                        }
                        Entry::Vacant(e) => {
                            let p = info.printer(cli);
                            println!("{addr:24?} +++ {ping:>7.1?} {p}");
                            e.insert(info);
                        }
                    }
                }
            }
            Event::ServerInfo(server_info) if cli.json && !server_info.is_changed() => {
                let result = ServerResult::ping(*server_info.address(), server_info.ping());
                print_json(cli, &result);
            }
            Event::ServerInfoTimeout(addr) if cli.json => {
                let result = ServerResult::timeout(addr);
                print_json(cli, &result);
            }
            Event::ServerRemove(addr) => {
                if cli.json {
                    let result = ServerResult::new(addr, None, ServerResultKind::Remove);
                    print_json(cli, &result);
                } else {
                    servers.remove(&addr);
                }
            }
            _ => {}
        }
    }
}
