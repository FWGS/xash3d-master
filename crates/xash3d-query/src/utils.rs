use std::{
    io::{self, Write},
    net::{SocketAddr, ToSocketAddrs},
    process,
};

use serde::Serialize;
use xash3d_observer::{Master, Observer};

use crate::{cli::Cli, server_result::ServerAddress};

pub fn create_observer(cli: &Cli) -> io::Result<Observer> {
    let mut observer = Observer::new()?;
    observer.set_filter_raw(cli.filter.clone());
    Ok(observer)
}

pub fn create_observer_with_masters(cli: &Cli) -> io::Result<Observer> {
    let mut observer = create_observer(cli)?;
    for i in &cli.masters {
        let Ok(mut addrs) = i.to_socket_addrs() else {
            eprintln!("warning: failed to resolve master {i}");
            continue;
        };
        // TODO: add a CLI option to select IPv4 or IPv6?
        if let Some(addr) = addrs.next() {
            let master = Master::new(addr);
            observer.insert_master(master);
        }
    }
    if observer.masters().is_empty() {
        eprintln!("error: no master servers could be resolved");
        process::exit(1);
    }
    Ok(observer)
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum IpVersion {
    Any,
    V4,
    V6,
}

impl IpVersion {
    pub fn matches(&self, addr: &SocketAddr) -> bool {
        match self {
            IpVersion::Any => true,
            IpVersion::V4 => addr.is_ipv4(),
            IpVersion::V6 => addr.is_ipv6(),
        }
    }
}

pub fn parse_server_addresses(servers: &[String], ip_version: IpVersion) -> Vec<ServerAddress> {
    let mut list = Vec::with_capacity(servers.len());
    for address in servers {
        if let Ok(addr) = address.parse() {
            list.push(ServerAddress {
                domain: None,
                resolved: addr,
            });
            continue;
        }

        match address.to_socket_addrs() {
            Ok(addrs) => {
                let mut addr = None;
                for i in addrs {
                    // match exact version
                    if ip_version.matches(&i) {
                        addr = Some(i);
                        break;
                    }

                    // fallback to any version
                    if addr.is_none() {
                        addr = Some(i);
                    }
                }

                if let Some(addr) = addr {
                    // found address for a server
                    list.push(ServerAddress {
                        domain: Some(address.clone()),
                        resolved: addr,
                    });
                } else {
                    eprintln!("warning: no IP address for server {address}");
                }
            }
            Err(e) => {
                eprintln!("error: invalid server address {address}, {e}");
            }
        }
    }
    if servers.len() != list.len() {
        process::exit(1);
    }
    list.sort_unstable();
    list.dedup_by_key(|i| i.resolved);
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
