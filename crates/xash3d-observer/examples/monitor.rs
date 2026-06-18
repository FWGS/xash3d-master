use std::{
    collections::{hash_map::Entry, HashMap},
    fmt, io,
    net::ToSocketAddrs,
};

use xash3d_observer::{
    event::{Event, ServerInfo},
    filter::Filter,
    Buffer, Master, Observer, Server,
};

#[derive(Clone, Debug)]
pub struct MyServerInfo {
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
    pub dedicated: bool,
}

impl fmt::Display for MyServerInfo {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fn flag(c: char, cond: bool) -> char {
            if cond {
                c
            } else {
                '-'
            }
        }

        write!(
            fmt,
            "{}{}{}{}{} {:>2}/{:<2} {:8} {:18} \"{}\"",
            flag('d', self.dm),
            flag('t', self.team),
            flag('c', self.coop),
            flag('p', self.password),
            flag('D', self.dedicated),
            self.numcl,
            self.maxcl,
            self.gamedir,
            self.map,
            self.host,
        )
    }
}

impl MyServerInfo {
    pub fn new(packet: &ServerInfo) -> Self {
        fn lossy_no_color(bytes: &[u8]) -> String {
            let s = String::from_utf8_lossy(bytes);
            xash3d_colored::str::remove_colors(&s).trim().to_string()
        }

        let gamedir = lossy_no_color(packet.gamedir());
        let map = lossy_no_color(packet.map());
        let host = lossy_no_color(packet.host());
        let protocol = packet.protocol();
        let numcl = packet.clients_count();
        let maxcl = packet.clients_max();
        let dm = packet.is_deathmatch();
        let team = packet.has_teams();
        let coop = packet.is_coop();
        let password = packet.has_password();
        let dedicated = packet.is_dedicated();

        MyServerInfo {
            gamedir,
            map,
            host,
            protocol,
            numcl,
            maxcl,
            dm,
            team,
            coop,
            password,
            dedicated,
        }
    }
}

fn main() -> io::Result<()> {
    let mut observer = Observer::new()?;

    let masters = &["mentality.rip:27010", "mentality.rip:27011"];
    for i in masters {
        let addr = i.to_socket_addrs()?.next().unwrap();
        observer.insert_master(Master::new(addr));
    }

    let mut filter = Filter::default();
    filter.set_nat(false);
    let gamedir = std::env::args().nth(1);
    if let Some(gamedir) = gamedir.as_deref() {
        filter.set_gamedir(gamedir);
    }
    observer.set_filter(&filter);

    let mut servers = HashMap::new();
    let mut buffer = Buffer::new();
    loop {
        match observer.wait_event(&mut buffer, None)? {
            Event::ServerList(servers) => {
                for addr in servers.iter() {
                    let server = Server::new(addr);
                    observer.insert_server(server);
                }
            }
            Event::ServerInfo(server_info) => {
                let addr = *server_info.address();
                let ping = server_info.ping();
                let info = MyServerInfo::new(&server_info);
                match servers.entry(addr) {
                    Entry::Occupied(mut e) => {
                        if server_info.is_changed() {
                            println!("{:8} {addr:24?} {ping:>7.1?} {info}", "update");
                            e.insert(info);
                        } else {
                            // println!("{:8} {addr:24?} {ping:>7.1?}", "ping");
                            println!("{:8} {addr:24?} {ping:>7.1?} {info}", "same");
                        }
                    }
                    Entry::Vacant(e) => {
                        println!("{:8} {addr:24?} {ping:>7.1?} {info}", "new");
                        e.insert(info);
                    }
                }
            }
            Event::ServerInfoTimeout(addr) => {
                println!("{:8} {addr:24?}", "timeout");
            }
            Event::ServerRemove(addr) => {
                println!("{:8} {addr:24?}", "remove");
                servers.remove(&addr);
            }
            _ => todo!(),
        }
    }
}
