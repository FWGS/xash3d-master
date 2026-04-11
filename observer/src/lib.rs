#[macro_use]
extern crate log;

use std::{
    cmp,
    collections::hash_map::{Entry, HashMap},
    fmt, io,
    net::{Ipv4Addr, SocketAddr, SocketAddrV4, ToSocketAddrs, UdpSocket},
    time::{Duration, Instant},
};

use xash3d_protocol::{self as proto, filter::Version, Error as ProtocolError};

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
        let packet = packet.encode(&mut buf[..]).unwrap();
        sock.send_to(packet, addr)?;
        Ok(())
    }

    fn is_changed(&mut self, buf: &[u8]) -> bool {
        if self.data.as_ref() != buf {
            self.data = Box::from(buf);
            true
        } else {
            false
        }
    }

    fn ping(&self, now: Instant) -> Duration {
        now.duration_since(self.time)
    }
}

#[allow(unused_variables)]
pub trait Handler {
    /// Returns `true` if observer's main loop should stop.
    fn stop_observer(&mut self) -> bool {
        false
    }

    /// Returns `true` if observer should query server list from a given master server.
    fn query_servers_from_master(&mut self, master: SocketAddr) -> bool {
        true
    }

    /// Returns extra servers for which observer should query info.
    fn extra_servers(&mut self) -> &[SocketAddr] {
        &[]
    }

    /// Return `true` if observer should query info for this server.
    ///
    /// Observer calls this method every time it receives a server address from a master server.
    fn query_info_for_server(&mut self, master: SocketAddr, server: SocketAddr) -> bool {
        true
    }

    /// Called if an invalid packet received from a master server.
    fn master_invalid_packet(&mut self, addr: SocketAddr, packet: &[u8], error: ProtocolError) {
        let data = proto::wrappers::Str(packet);
        warn!("invalid packet from master {addr}: {error} \"{data}\"");
    }

    /// Called if a server info changed.
    fn server_update(
        &mut self,
        addr: SocketAddr,
        info: &GetServerInfoResponse,
        is_new: bool,
        ping: Duration,
    ) {
    }

    /// Called if a server info does not changed.
    fn server_update_ping(&mut self, addr: SocketAddr, ping: Duration) {}

    /// Called if a server removed from a query list.
    fn server_remove(&mut self, addr: SocketAddr) {}

    /// Called if a server does not respond.
    fn server_timeout(&mut self, addr: SocketAddr) {}

    /// Called if failed to detect a protocol version for a server.
    fn server_invalid_protocol(&mut self, addr: SocketAddr, ping: Duration) {
        debug!("failed to detect protocol for server {addr}");
    }

    /// Called if an invalid packet received from a master server.
    fn server_invalid_packet(
        &mut self,
        addr: SocketAddr,
        ping: Duration,
        packet: &[u8],
        error: ProtocolError,
    ) {
        let data = proto::wrappers::Str(packet);
        debug!("invalid packet from server {addr}: {error} \"{data}\"");
    }
}

struct Master {
    addr: SocketAddr,
    key: u32,
}

impl Master {
    fn new(addr: SocketAddr) -> Self {
        Self { addr, key: 0 }
    }

    fn encode_query_servers_packet<'a>(&mut self, filter: &str, buf: &'a mut [u8]) -> &'a [u8] {
        struct FilterKey<'b> {
            filter: &'b str,
            key: u32,
        }

        impl fmt::Display for FilterKey<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}", self.filter)?;
                write!(f, "\\key\\{:x}", self.key)?;
                Ok(())
            }
        }

        // generate a fresh key for each request
        self.key = fastrand::u32(..);

        let packet = proto::game::QueryServers {
            region: proto::server::Region::RestOfTheWorld,
            last: SocketAddrV4::new(Ipv4Addr::new(0, 0, 0, 0), 0).into(),
            filter: FilterKey {
                filter,
                key: self.key,
            },
        };

        // TODO: handle error, filter may not fit
        packet.encode(buf).unwrap()
    }
}

pub struct ObserverBuilder<'a> {
    client_version: Option<Version>,
    client_build_number: Option<u32>,
    gamedir: Option<&'a str>,
    nat: Option<bool>,
    filter: Option<&'a str>,
}

impl<'a> Default for ObserverBuilder<'a> {
    fn default() -> Self {
        Self::with_default_client_version()
    }
}

impl<'a> ObserverBuilder<'a> {
    /// Creates a new observer builder with the default client version.
    ///
    /// See [Self::client_version] for more information.
    pub fn with_default_client_version() -> Self {
        Self {
            client_version: Some(xash3d_protocol::CLIENT_VERSION),
            ..Self::new()
        }
    }

    /// Creates a new observer builder.
    pub fn new() -> Self {
        Self {
            client_version: None,
            client_build_number: None,
            gamedir: None,
            nat: None,
            filter: None,
        }
    }

    // Sets a client version for requests sent to master servers.
    //
    // # Note
    //
    // The master server may respond with a fake server if the client version is lower than
    // what is specified in the master server's configuration file.
    pub fn client_version(mut self, version: Version) -> Self {
        self.client_version = Some(version);
        self
    }

    // Sets a client build number for requests sent to master servers.
    //
    // # Note
    //
    // The master server may respond with a fake server if the client build number is lower than
    // what is specified in the master server's configuration file.
    pub fn client_build_number(mut self, build_number: u32) -> Self {
        self.client_build_number = Some(build_number);
        self
    }

    pub fn gamedir(mut self, value: &'a str) -> Self {
        self.gamedir = Some(value);
        self
    }

    pub fn nat(mut self, value: bool) -> Self {
        self.nat = Some(value);
        self
    }

    pub fn filter(mut self, value: &'a str) -> Self {
        self.filter = Some(value);
        self
    }

    pub fn build<T: Handler>(
        self,
        handler: T,
        masters: &[impl AsRef<str>],
    ) -> io::Result<Observer<T>> {
        let sock = UdpSocket::bind("0.0.0.0:0")?;
        let local_addr = sock.local_addr()?;

        let mut vec = Vec::with_capacity(masters.len());
        for i in masters {
            for addr in i.as_ref().to_socket_addrs()? {
                if local_addr.is_ipv4() == addr.is_ipv4() {
                    vec.push(Master::new(addr));
                    break;
                }
            }
        }

        fn append<T: fmt::Display>(out: &mut String, key: &str, value: Option<T>) {
            use fmt::Write;
            if let Some(value) = value {
                write!(out, "\\{key}\\{value}").unwrap();
            }
        }

        let mut filter = String::new();
        append(&mut filter, "clver", self.client_version);
        append(&mut filter, "buildnum", self.client_build_number);
        append(&mut filter, "nat", self.nat.map(|i| i as u8));
        append(&mut filter, "gamedir", self.gamedir);
        if let Some(s) = self.filter {
            filter.push_str(s);
        }

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
    masters: Vec<Master>,
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

    /// Returns a shared reference to a user handler.
    pub fn handler_ref(&self) -> &T {
        &self.handler
    }

    /// Returns a mutable reference to a user handler.
    pub fn handler_mut(&mut self) -> &mut T {
        &mut self.handler
    }

    /// Destroy this observer and returns a user handler.
    pub fn into_handler(self) -> T {
        self.handler
    }

    fn get_master(&self, addr: SocketAddr) -> Option<&Master> {
        self.masters.iter().find(|master| master.addr == addr)
    }

    fn first_event_time(&self) -> Instant {
        cmp::min(self.master_time, self.server_time)
    }

    fn update_now(&mut self) {
        self.now = Instant::now();
    }

    fn query_servers(&mut self, buf: &mut [u8]) -> io::Result<()> {
        for master in self.masters.iter_mut() {
            if self.handler.query_servers_from_master(master.addr) {
                let packet = master.encode_query_servers_packet(&self.filter, buf);
                self.sock.send_to(packet, master.addr)?;
            }
        }
        Ok(())
    }

    fn query_info_all(&mut self) -> io::Result<()> {
        use ConnectionState as S;

        for &i in self.handler.extra_servers() {
            if let Entry::Vacant(e) = self.connections.entry(i) {
                e.insert(Connection::new(self.now));
            }
        }

        let iter = self
            .connections
            .iter_mut()
            .filter(|(_, i)| i.is_valid(self.now));
        for (&addr, con) in iter {
            match con.state {
                S::Idle | S::WaitingInfo => {
                    if con.state == S::WaitingInfo {
                        self.handler.server_timeout(addr);
                    }
                    con.time = self.now;
                    con.query_info(&self.sock, addr)?;
                    con.state = ConnectionState::WaitingInfo;
                }
                S::ProtocolDetection => {
                    con.query_info(&self.sock, addr)?;
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

        for (&addr, _) in iter {
            self.handler.server_remove(addr);
        }

        self.connections.retain(|_, i| i.is_valid(self.now));

        Ok(())
    }

    fn receive(&mut self, buf: &mut [u8]) -> io::Result<bool> {
        let time = self.first_event_time();
        while self.now < time {
            if self.handler.stop_observer() {
                // stop the main loop
                return Ok(false);
            }

            let dur = time.duration_since(self.now);
            self.sock.set_read_timeout(Some(dur))?;
            match self.sock.recv_from(buf) {
                Ok((n, from)) => self.handle_packet(&buf[..n], from)?,
                Err(e) => match e.kind() {
                    io::ErrorKind::AddrInUse | io::ErrorKind::WouldBlock => break,
                    _ => return Err(e),
                },
            }
        }
        Ok(true)
    }

    fn handle_packet(&mut self, buf: &[u8], from: SocketAddr) -> io::Result<()> {
        self.update_now();

        if let Some(master) = self.get_master(from) {
            self.handle_master_packet(buf, from, master.key)
        } else {
            self.handle_server_packet(buf, from)
        }
    }

    fn handle_server_from_master(
        &mut self,
        master: SocketAddr,
        server: SocketAddr,
    ) -> io::Result<()> {
        if !self.handler.query_info_for_server(master, server) {
            // User handler do not want to query info for this server.
            self.connections.remove(&server);
            return Ok(());
        }

        if let Entry::Vacant(e) = self.connections.entry(server) {
            let mut c = Connection::new(self.now);
            c.query_info(&self.sock, server)?;
            e.insert(c);
        }

        Ok(())
    }

    fn handle_master_packet(&mut self, buf: &[u8], from: SocketAddr, key: u32) -> io::Result<()> {
        match proto::master::QueryServersResponse::decode(buf) {
            Ok(packet) => {
                if packet.key != Some(key) {
                    // ignore if invalid or missing challenge key in the response
                    return Ok(());
                }

                if from.is_ipv6() {
                    for addr in packet.iter().map(SocketAddr::V6) {
                        self.handle_server_from_master(from, addr)?;
                    }
                } else {
                    for addr in packet.iter().map(SocketAddr::V4) {
                        self.handle_server_from_master(from, addr)?;
                    }
                }
            }
            Err(err) => {
                // The master server can respond with a fake server at same address. It's used
                // for update messages.
                if self.handle_server_packet(buf, from).is_err() {
                    self.handler.master_invalid_packet(from, buf, err);
                }
            }
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
                            let ping = con.ping(self.now);
                            if con.is_changed(buf) {
                                let is_new = con.state == S::ProtocolDetection;
                                self.handler.server_update(from, &packet, is_new, ping);
                            } else {
                                self.handler.server_update_ping(from, ping);
                            }
                            con.state = S::Idle;
                        }
                        S::Idle => {}
                    }
                } else {
                    // TODO: unexpected server response
                }
            }
            Err(proto::Error::InvalidProtocolVersion) => {
                if let Some(con) = self.connections.get_mut(&from) {
                    if con.state == S::ProtocolDetection && con.protocol == proto::PROTOCOL_VERSION
                    {
                        // try previous protocol version
                        con.protocol -= 1;
                        con.query_info(&self.sock, from)?;
                    } else {
                        let ping = con.ping(self.now);
                        self.handler.server_invalid_protocol(from, ping);
                        self.connections.remove(&from);
                    }
                }
            }
            Err(err) => {
                if let Some(con) = self.connections.get_mut(&from) {
                    let ping = con.ping(self.now);
                    self.handler.server_invalid_packet(from, ping, buf, err);
                }
            }
        }
        Ok(())
    }

    pub fn run(&mut self) -> io::Result<()> {
        let mut buffer = [0; 2048];

        loop {
            self.update_now();

            if self.master_time <= self.now {
                self.query_servers(&mut buffer)?;
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

            if !self.receive(&mut buffer)? {
                break;
            }
        }

        for (&addr, connection) in self.connections.iter() {
            if connection.state == ConnectionState::ProtocolDetection {
                self.handler.server_timeout(addr);
            }
        }

        Ok(())
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
