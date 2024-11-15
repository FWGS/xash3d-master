#[macro_use]
extern crate log;

use std::{
    cmp,
    collections::hash_map::{Entry, HashMap},
    fmt, io,
    net::{Ipv4Addr, SocketAddr, SocketAddrV4, ToSocketAddrs, UdpSocket},
    time::{Duration, Instant},
};

use xash3d_protocol as proto;

pub type GetServerInfoResponse<'a, T = &'a [u8]> =
    xash3d_protocol::server::GetServerInfoResponse<T>;

pub const MASTER_INTERVAL: Duration = Duration::from_secs(8);
pub const SERVER_INTERVAL: Duration = Duration::from_secs(2);
pub const SERVER_TIMEOUT: Duration = Duration::from_secs(16);
pub const SERVER_CLEAN_INTERVAL: Duration = Duration::from_secs(16);

#[derive(PartialEq, Eq)]
#[repr(u8)]
enum ConnectionState {
    /// Server protocol version is not known yet.
    ProtocolDetection,
    /// No input is expected from a server.
    Idle,
    /// Waiting for info from a server.
    WaitingInfo,
}

struct Connection {
    protocol: u8,
    state: ConnectionState,
    time: Instant,
    data: Box<[u8]>,
}

impl Connection {
    fn new(now: Instant) -> Self {
        Self {
            protocol: proto::PROTOCOL_VERSION,
            time: now,
            state: ConnectionState::ProtocolDetection,
            data: Default::default(),
        }
    }

    fn is_valid(&self, now: Instant) -> bool {
        now.duration_since(self.time) < SERVER_TIMEOUT
    }

    fn query_info(&mut self, sock: &UdpSocket, addr: SocketAddr) -> io::Result<()> {
        let mut buf = [0; 512];
        let packet = proto::game::GetServerInfo {
            protocol: self.protocol,
        };
        let n = packet.encode(&mut buf[..]).unwrap();
        sock.send_to(&buf[..n], addr)?;
        Ok(())
    }

    fn is_changed(&mut self, now: Instant, buf: &[u8]) -> bool {
        self.time = now;
        if self.data.as_ref() != buf {
            self.data = Box::from(buf);
            true
        } else {
            false
        }
    }
}

#[allow(unused_variables)]
pub trait Handler {
    fn server_update(&mut self, addr: SocketAddr, info: &GetServerInfoResponse, is_new: bool) {}

    fn server_remove(&mut self, addr: &SocketAddr) {}

    fn server_timeout(&mut self, addr: &SocketAddr) {}
}

#[derive(Default)]
pub struct ObserverBuilder<'a> {
    gamedir: Option<&'a str>,
    nat: Option<bool>,
}

impl<'a> ObserverBuilder<'a> {
    pub fn gamedir(mut self, value: &'a str) -> Self {
        self.gamedir = Some(value);
        self
    }

    pub fn nat(mut self, value: bool) -> Self {
        self.nat = Some(value);
        self
    }

    pub fn build<T: Handler>(self, handler: T, masters: &[&str]) -> io::Result<Observer<T>> {
        let sock = UdpSocket::bind("0.0.0.0:0")?;
        let local_addr = sock.local_addr()?;

        let mut vec = Vec::with_capacity(masters.len());
        for i in masters {
            for addr in i.to_socket_addrs()? {
                if local_addr.is_ipv4() == addr.is_ipv4() {
                    vec.push(addr);
                    break;
                }
            }
        }

        fn append<T: fmt::Display>(out: &mut String, key: &str, value: Option<T>) {
            use fmt::Write;
            if let Some(value) = value {
                write!(out, "\\{}\\{}", key, value).unwrap();
            }
        }

        let mut filter = String::new();
        append(&mut filter, "nat", self.nat.map(|i| i as u8));
        append(&mut filter, "gamedir", self.gamedir);

        let connections = HashMap::new();
        let now = Instant::now();

        Ok(Observer {
            sock,
            filter,
            masters: vec,
            master_time: now,
            server_time: now,
            server_clean_time: now + SERVER_CLEAN_INTERVAL,
            now,
            connections,
            handler,
        })
    }
}

pub struct Observer<T> {
    sock: UdpSocket,
    filter: String,
    masters: Vec<SocketAddr>,
    master_time: Instant,
    server_time: Instant,
    server_clean_time: Instant,
    now: Instant,
    connections: HashMap<SocketAddr, Connection>,
    handler: T,
}

impl<T: Handler> Observer<T> {
    pub fn builder<'a>() -> ObserverBuilder<'a> {
        ObserverBuilder::default()
    }

    fn is_master(&self, addr: &SocketAddr) -> bool {
        self.masters.iter().any(|i| i == addr)
    }

    fn first_event_time(&self) -> Instant {
        cmp::min(self.master_time, self.server_time)
    }

    fn update_now(&mut self) {
        self.now = Instant::now();
    }

    fn query_servers(&self, filter: &str) -> io::Result<()> {
        let mut buf = [0; 512];
        let packet = proto::game::QueryServers {
            region: proto::server::Region::RestOfTheWorld,
            last: SocketAddrV4::new(Ipv4Addr::new(0, 0, 0, 0), 0).into(),
            filter,
        };
        let n = packet.encode(&mut buf[..]).unwrap(); // TODO: handle error, filter may not fit

        for addr in self.masters.iter() {
            self.sock.send_to(&buf[..n], addr)?;
        }

        Ok(())
    }

    fn query_info_all(&mut self) -> io::Result<()> {
        use ConnectionState as S;

        let iter = self
            .connections
            .iter_mut()
            .filter(|(_, i)| i.is_valid(self.now));
        for (addr, con) in iter {
            match con.state {
                S::Idle | S::WaitingInfo => {
                    if con.state == S::WaitingInfo {
                        self.handler.server_timeout(addr);
                    }
                    con.query_info(&self.sock, *addr)?;
                    con.state = ConnectionState::WaitingInfo;
                }
                S::ProtocolDetection => {
                    con.query_info(&self.sock, *addr)?;
                }
            }
        }

        Ok(())
    }

    fn cleanup(&mut self) -> io::Result<()> {
        let iter = self
            .connections
            .iter()
            .filter(|(_, conn)| !conn.is_valid(self.now));

        for (addr, _) in iter {
            self.handler.server_remove(addr);
        }

        self.connections.retain(|_, i| i.is_valid(self.now));

        Ok(())
    }

    fn receive(&mut self) -> io::Result<()> {
        let mut buf = [0; 512];
        let time = self.first_event_time();
        while self.now < time {
            let dur = time.duration_since(self.now);
            self.sock.set_read_timeout(Some(dur))?;
            match self.sock.recv_from(&mut buf) {
                Ok((n, from)) => self.handle_packet(&buf[..n], from)?,
                Err(e) => match e.kind() {
                    io::ErrorKind::AddrInUse | io::ErrorKind::WouldBlock => break,
                    _ => return Err(e),
                },
            }
        }
        Ok(())
    }

    fn handle_packet(&mut self, buf: &[u8], from: SocketAddr) -> io::Result<()> {
        self.update_now();

        if self.is_master(&from) {
            self.handle_master_packet(buf, from)
        } else {
            self.handle_server_packet(buf, from)
        }
    }

    fn handle_master_packet(&mut self, buf: &[u8], from: SocketAddr) -> io::Result<()> {
        match proto::master::QueryServersResponse::decode(buf) {
            Ok(packet) => {
                for addr in packet.iter().map(SocketAddr::V4) {
                    if let Entry::Vacant(e) = self.connections.entry(addr) {
                        let mut conn = Connection::new(self.now);
                        conn.query_info(&self.sock, addr)?;
                        e.insert(conn);
                    }
                }
            }
            Err(err) => warn!("invalid packet from master {}: {}", from, err),
        }
        Ok(())
    }

    fn handle_server_packet(&mut self, buf: &[u8], from: SocketAddr) -> io::Result<()> {
        use ConnectionState as S;

        match GetServerInfoResponse::decode(buf) {
            Ok(packet) => {
                if let Some(con) = self.connections.get_mut(&from) {
                    match con.state {
                        S::ProtocolDetection | S::WaitingInfo => {
                            if con.is_changed(self.now, buf) {
                                let is_new = con.state == S::ProtocolDetection;
                                self.handler.server_update(from, &packet, is_new);
                            }
                            con.state = S::Idle;
                        }
                        S::Idle => {}
                    }
                }
            }
            Err(proto::Error::InvalidProtocolVersion) => {
                if let Some(c) = self.connections.get_mut(&from) {
                    if c.state == S::ProtocolDetection && c.protocol == proto::PROTOCOL_VERSION {
                        // try previous protocol version
                        c.protocol -= 1;
                        c.query_info(&self.sock, from)?;
                    } else {
                        trace!("invalid protocol {}", from);
                        self.connections.remove(&from);
                    }
                }
            }
            Err(err) => debug!("server {}: {} \"{}\"", from, err, proto::wrappers::Str(buf)),
        }
        Ok(())
    }

    pub fn run(&mut self) -> io::Result<()> {
        loop {
            self.update_now();

            if self.master_time <= self.now {
                self.query_servers(&self.filter)?;
                self.master_time = update_time(self.now, self.master_time, MASTER_INTERVAL);
            }

            if self.server_time <= self.now {
                self.query_info_all()?;
                self.server_time = update_time(self.now, self.server_time, SERVER_INTERVAL);
            }

            if self.server_clean_time <= self.now {
                self.cleanup()?;
                self.server_clean_time =
                    update_time(self.now, self.server_clean_time, SERVER_CLEAN_INTERVAL);
            }

            self.receive()?;
        }
    }
}

fn update_time(now: Instant, mut time: Instant, interval: Duration) -> Instant {
    time += interval;
    if time <= now {
        now + interval
    } else {
        time
    }
}
