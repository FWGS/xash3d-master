use std::{
    io::{self, Write},
    net::{Ipv4Addr, SocketAddr, SocketAddrV4, ToSocketAddrs},
    process,
};

use serde::Serialize;
use xash3d_observer::{Master, ObserverNew};

use crate::cli::Cli;

pub fn create_observer(cli: &Cli) -> io::Result<ObserverNew> {
    // TODO: ipv6
    let unspecified = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0));
    let mut observer = ObserverNew::bind(unspecified)?;
    observer.set_filter_raw(cli.filter.clone());
    Ok(observer)
}

pub fn create_observer_with_masters(cli: &Cli) -> io::Result<ObserverNew> {
    let mut observer = create_observer(cli)?;
    let local_addr = observer.local_addr()?;
    for i in &cli.masters {
        for addr in i.to_socket_addrs()? {
            if addr.is_ipv4() == local_addr.is_ipv4() {
                let master = Master::new(addr);
                observer.insert_master(master);
                break;
            }
        }
    }
    Ok(observer)
}

pub fn parse_server_addresses(servers: &[String]) -> Vec<SocketAddr> {
    let mut list = Vec::with_capacity(servers.len());
    for i in servers {
        match i.parse() {
            Ok(addr) => list.push(addr),
            Err(_) => eprintln!("invalid address {i}"),
        }
    }
    if servers.len() != list.len() {
        process::exit(1);
    }
    list.sort_unstable();
    list.dedup();
    list
}

pub fn print_json<T: Serialize>(cli: &Cli, value: &T) {
    let print = if !cli.compact {
        serde_json::to_writer_pretty
    } else {
        serde_json::to_writer
    };
    let mut stdout = io::stdout().lock();
    print(&mut stdout, value).unwrap();
    stdout.write_all(b"\n").unwrap();
    stdout.flush().unwrap();
}
