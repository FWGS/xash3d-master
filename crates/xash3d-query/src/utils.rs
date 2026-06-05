use std::{
    io::{self, Write},
    net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6, ToSocketAddrs},
    process,
};

use serde::Serialize;
use xash3d_observer::{Master, Observer};

use crate::cli::Cli;

enum IpVersion {
    Any,
    V4,
    V6,
    Both,
}

/// Detects an IP version from a list of addresses.
///
/// Masters that fail to resolve are skipped with a warning.
fn ip_version_for(addrs: &[Box<str>]) -> io::Result<IpVersion> {
    let mut version = IpVersion::Any;
    for i in addrs {
        let Ok(mut it) = i.to_socket_addrs() else {
            eprintln!("warning: failed to resolve master {i}");
            continue;
        };
        if let Some(addr) = it.next() {
            match version {
                IpVersion::Any | IpVersion::V4 if addr.is_ipv4() => {
                    version = IpVersion::V4;
                }
                IpVersion::Any | IpVersion::V6 if addr.is_ipv6() => {
                    version = IpVersion::V6;
                }
                _ => return Ok(IpVersion::Both),
            }
        }
    }
    Ok(version)
}

pub fn create_observer(cli: &Cli) -> io::Result<Observer> {
    let unspecified = match ip_version_for(&cli.masters)? {
        IpVersion::Both => {
            eprintln!("error: master servers with different IP versions is not supported");
            process::exit(1);
        }
        IpVersion::V6 => SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::UNSPECIFIED, 0, 0, 0)),
        _ => SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0)),
    };
    let mut observer = Observer::bind(unspecified)?;
    observer.set_filter_raw(cli.filter.clone());
    Ok(observer)
}

pub fn create_observer_with_masters(cli: &Cli) -> io::Result<Observer> {
    let mut observer = create_observer(cli)?;
    let local_addr = observer.local_addr()?;
    let mut inserted = 0;
    for i in &cli.masters {
        let Ok(addrs) = i.to_socket_addrs() else { continue };
        for addr in addrs {
            if addr.is_ipv4() == local_addr.is_ipv4() {
                let master = Master::new(addr);
                observer.insert_master(master);
                inserted += 1;
                break;
            }
        }
    }
    if inserted == 0 {
        eprintln!("error: no master servers could be resolved");
        process::exit(1);
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
