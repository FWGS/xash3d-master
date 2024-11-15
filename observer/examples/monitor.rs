use std::{
    collections::{hash_map::Entry, HashMap},
    fmt, io,
    net::SocketAddr,
};

use xash3d_observer::{GetServerInfoResponse, Handler, ObserverBuilder};
use xash3d_protocol::color::trim_color;

#[derive(Clone, Debug)]
pub struct ServerInfo {
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

impl fmt::Display for ServerInfo {
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

impl ServerInfo {
    pub fn new(packet: &GetServerInfoResponse) -> Self {
        fn lossy_no_color(bytes: &[u8]) -> String {
            let s = String::from_utf8_lossy(bytes);
            trim_color(&s).trim().to_string()
        }

        let gamedir = lossy_no_color(packet.gamedir);
        let map = lossy_no_color(packet.map);
        let host = lossy_no_color(packet.host);
        let protocol = packet.protocol;
        let numcl = packet.numcl;
        let maxcl = packet.maxcl;
        let dm = packet.dm;
        let team = packet.team;
        let coop = packet.coop;
        let password = packet.password;
        let dedicated = packet.dedicated;

        ServerInfo {
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

#[derive(Default)]
struct Monitor {
    servers: HashMap<SocketAddr, ServerInfo>,
}

impl Handler for Monitor {
    fn server_update(&mut self, addr: SocketAddr, info: &GetServerInfoResponse, _: bool) {
        let info = ServerInfo::new(info);
        match self.servers.entry(addr) {
            Entry::Occupied(mut e) => {
                println!("{:24?} --- {}", addr, e.get());
                println!("{:24?} +++ {}", addr, info);
                e.insert(info);
            }
            Entry::Vacant(e) => {
                println!("{:24?} +++ {}", addr, info);
                e.insert(info);
            }
        }
    }

    fn server_remove(&mut self, addr: &SocketAddr) {
        self.servers.remove(addr);
    }
}

fn main() -> io::Result<()> {
    let gamedir = std::env::args().nth(1);
    let gamedir = gamedir.as_deref();
    let masters = &["mentality.rip:27010", "mentality.rip:27011"];
    let mut builder = ObserverBuilder::default().nat(false);
    if let Some(gamedir) = gamedir {
        builder = builder.gamedir(gamedir)
    }
    builder.build(Monitor::default(), masters)?.run()
}
