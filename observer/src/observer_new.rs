use std::{
    cmp,
    collections::{hash_map::Entry, HashMap},
    fmt, io,
    net::{Ipv4Addr, SocketAddr, SocketAddrV4},
    time::{Duration, Instant},
};

use xash3d_protocol::{
    game::QueryServers,
    master::QueryServersResponse,
    server::{GetServerInfoResponse, Region},
};

use crate::{
    connection::{Connection, ConnectionState},
    event::{Event, InternalEvent, ServerInfo, ServerList},
    filter::Filter,
    net::Socket,
};

#[allow(deprecated)]
use crate::observer_old::Handler;

pub(crate) const MASTER_INTERVAL: Duration = Duration::from_secs(8);
pub(crate) const SERVER_INTERVAL: Duration = Duration::from_secs(2);
pub(crate) const SERVER_TIMEOUT: Duration = Duration::from_secs(16);
pub(crate) const SERVER_CLEAN_INTERVAL: Duration = Duration::from_secs(16);

pub struct Master {
    addr: SocketAddr,
    key: u32,
}

impl Master {
    pub fn new(addr: SocketAddr) -> Self {
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

        let packet = QueryServers {
            region: Region::RestOfTheWorld,
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

pub struct Server {
    addr: SocketAddr,
    players: bool,
}

impl Server {
    pub fn new(addr: SocketAddr) -> Self {
        Self {
            addr,
            players: false,
        }
    }

    pub fn with_players(mut self, players: bool) -> Self {
        self.players = players;
        self
    }
}

enum DelayedEvent {
    ServerTimeout(SocketAddr),
    ServerRemove(SocketAddr),
}

impl<'a> From<DelayedEvent> for InternalEvent<'a> {
    fn from(value: DelayedEvent) -> Self {
        match value {
            DelayedEvent::ServerTimeout(addr) => Event::ServerInfoTimeout(addr).into(),
            DelayedEvent::ServerRemove(addr) => Event::ServerRemove(addr).into(),
        }
    }
}

pub struct Buffer {
    data: [u8; 2048],
}

impl Buffer {
    pub fn new() -> Self {
        Self { data: [0; 2048] }
    }
}

impl Default for Buffer {
    fn default() -> Self {
        Self::new()
    }
}

struct Task {
    time: Instant,
    interval: Duration,
}

impl Task {
    fn new(time: Instant, interval: Duration) -> Self {
        Self { time, interval }
    }

    fn time(&self) -> Instant {
        self.time
    }

    fn update_time(&mut self, now: Instant) -> bool {
        if self.time <= now {
            self.time += self.interval;
            if self.time <= now {
                self.time = now + self.interval
            }
            true
        } else {
            false
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum Pending {
    Master(SocketAddr),
    Server(SocketAddr),
}

pub struct ObserverNew {
    pub(crate) sock: Socket,
    filter: String,
    masters: Vec<Master>,
    query_servers_task: Task,
    query_info_task: Task,
    cleanup_task: Task,
    pub(crate) connections: HashMap<SocketAddr, Connection>,
    delayed_events: Vec<DelayedEvent>,
    pending: Vec<Pending>,
}

// FIXME: compatibility with old api
#[allow(deprecated)]
impl ObserverNew {
    pub fn bind(addr: SocketAddr) -> io::Result<Self> {
        let sock = Socket::bind(addr)?;
        let connections = HashMap::new();
        let now = Instant::now();

        Ok(Self {
            sock,
            filter: String::new(),
            masters: Vec::new(),
            query_servers_task: Task::new(now, MASTER_INTERVAL),
            query_info_task: Task::new(now, SERVER_INTERVAL),
            cleanup_task: Task::new(now, SERVER_CLEAN_INTERVAL),
            connections,
            delayed_events: Vec::new(),
            pending: Vec::new(),
        })
    }

    pub fn local_addr(&self) -> io::Result<SocketAddr> {
        self.sock.local_addr()
    }

    pub fn set_filter_raw(&mut self, filter: String) {
        self.filter = filter;
    }

    pub fn set_filter(&mut self, filter: &Filter) {
        self.set_filter_raw(filter.to_raw_string());
    }

    fn remove_pending(&mut self, pending: Pending) {
        if let Some(i) = self.pending.iter().position(|&i| i == pending) {
            self.pending.swap_remove(i);
        }
    }

    pub fn insert_master(&mut self, master: Master) {
        if self.get_master(&master.addr).is_none() {
            self.pending.push(Pending::Master(master.addr));
            self.masters.push(master);
        }
    }

    pub fn remove_master(&mut self, addr: &SocketAddr) -> Option<Master> {
        self.remove_pending(Pending::Master(*addr));
        match self.masters.iter().position(|i| i.addr == *addr) {
            Some(i) => Some(self.masters.swap_remove(i)),
            None => None,
        }
    }

    pub fn insert_server(&mut self, server: Server) {
        if let Entry::Vacant(e) = self.connections.entry(server.addr) {
            self.pending.push(Pending::Server(server.addr));
            e.insert(Connection::new(server.addr, server.players));
        }
    }

    pub fn remove_server(&mut self, addr: &SocketAddr) {
        self.remove_pending(Pending::Server(*addr));
        self.connections.remove(addr);
    }

    fn get_master(&self, addr: &SocketAddr) -> Option<&Master> {
        self.masters.iter().find(|master| master.addr.eq(addr))
    }

    fn query_servers_from_masters<T>(&mut self, buf: &mut [u8], handler: &mut T) -> io::Result<()>
    where
        T: Handler,
    {
        for master in self.masters.iter_mut() {
            if handler.query_servers_from_master(master.addr) {
                let packet = master.encode_query_servers_packet(&self.filter, buf);

                // Do not send queries twice.
                if self.pending.contains(&Pending::Master(master.addr)) {
                    continue;
                }

                self.sock.send_to(packet, master.addr)?;
            }
        }
        Ok(())
    }

    fn query_info_from_servers<T>(&mut self, buffer: &mut [u8], handler: &mut T) -> io::Result<()>
    where
        T: Handler,
    {
        let now = Instant::now();
        for (addr, con) in self.connections.iter_mut() {
            // Invalid connections will be removed later by cleanup task. Master servers can send
            // such servers again. Servers will become invalid if no response will be received in
            // SERVER_TIMEOUT seconds.
            if !con.is_valid(now) {
                continue;
            }

            // Do not send queries twice.
            if self.pending.contains(&Pending::Server(*addr)) {
                continue;
            }

            // This server did not send a response to the last request.
            if con.state() != ConnectionState::Idle {
                self.delayed_events.push(DelayedEvent::ServerTimeout(*addr));
            }

            con.query(&self.sock, buffer)?;
        }

        // Hook for old API.
        for &addr in handler.extra_servers() {
            if let Entry::Vacant(e) = self.connections.entry(addr) {
                let mut con = Connection::new(addr, false);
                con.query(&self.sock, buffer)?;
                e.insert(con);
            }
        }

        Ok(())
    }

    fn handle_master_packet<'a>(
        &mut self,
        from: &SocketAddr,
        data: &'a [u8],
        key: u32,
    ) -> Option<InternalEvent<'a>> {
        match QueryServersResponse::decode(data) {
            Ok(response) => {
                if response.key != Some(key) {
                    // ignore if invalid or missing challenge key in the response
                    return None;
                }

                Some(Event::ServerList(ServerList::new(*from, response)).into())
            }
            Err(error) => {
                // The master server can respond with a fake server at same address. It's used
                // for update messages.
                if let Ok(response) = GetServerInfoResponse::decode(data) {
                    let info = ServerInfo {
                        server: *from,
                        ping: Duration::default(),
                        new: true,
                        changed: true,
                        response,
                    };
                    Some(Event::ServerInfo(info).into())
                } else {
                    Some(InternalEvent::MasterInvalidPacket(*from, data, error))
                }
            }
        }
    }

    fn handle_server_packet<'a>(
        &mut self,
        from: &SocketAddr,
        data: &'a [u8],
    ) -> io::Result<Option<InternalEvent<'a>>> {
        match self.connections.get_mut(from) {
            Some(con) => {
                let result = con.handle_packet(&self.sock, data);
                if let Ok(Some(InternalEvent::ServerInvalidProtocol(..))) = &result {
                    self.connections.remove(from);
                }
                result
            }
            None => Ok(None),
        }
    }

    fn handle_packet<'a>(
        &mut self,
        from: &SocketAddr,
        buffer: &'a [u8],
    ) -> io::Result<Option<InternalEvent<'a>>> {
        if let Some(master) = self.get_master(from) {
            Ok(self.handle_master_packet(from, buffer, master.key))
        } else {
            self.handle_server_packet(from, buffer)
        }
    }

    fn receive<'a, T>(
        &mut self,
        buffer: &'a mut [u8],
        user_deadline: Option<Instant>,
        handler: &mut T,
    ) -> io::Result<Option<InternalEvent<'a>>>
    where
        T: Handler,
    {
        let mut deadline = cmp::min(self.query_servers_task.time(), self.query_info_task.time());
        if let Some(user_deadline) = user_deadline {
            deadline = cmp::min(deadline, user_deadline);
        }
        let mut now = Instant::now();
        while now < deadline {
            if handler.stop_observer() {
                return Ok(Some(InternalEvent::Stop));
            }

            // FIXME: Work around limitation in current borrow checker, remove when polonius
            // will become available in MSRV.
            //
            // SAFETY: Used and returned only in this iteration.
            let buffer = unsafe { &mut *(buffer as *mut [u8]) };

            let timeout = deadline.duration_since(now);
            self.sock.set_read_timeout(Some(timeout))?;
            match self.sock.recv_from(buffer) {
                Ok((n, from)) => {
                    if let Some(event) = self.handle_packet(&from, &buffer[..n])? {
                        return Ok(Some(event));
                    }
                }
                Err(error) => match error.kind() {
                    io::ErrorKind::AddrInUse => break,
                    io::ErrorKind::WouldBlock => break,
                    _ => return Err(error),
                },
            }

            now = Instant::now();
        }

        Ok(None)
    }

    fn process_pending(&mut self, buffer: &mut [u8]) -> io::Result<()> {
        while let Some(i) = self.pending.pop() {
            match i {
                Pending::Master(addr) => {
                    for master in self.masters.iter_mut() {
                        if master.addr == addr {
                            let packet = master.encode_query_servers_packet(&self.filter, buffer);
                            self.sock.send_to(packet, master.addr)?;
                            break;
                        }
                    }
                }
                Pending::Server(addr) => {
                    if let Some(con) = self.connections.get_mut(&addr) {
                        con.query(&self.sock, buffer)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn cleanup_servers(&mut self, now: Instant) {
        self.connections.retain(|&addr, con| {
            if !con.is_valid(now) {
                self.delayed_events.push(DelayedEvent::ServerRemove(addr));
                false
            } else {
                true
            }
        });
    }

    fn process_tasks<T>(
        &mut self,
        buffer: &mut [u8],
        now: Instant,
        handler: &mut T,
    ) -> io::Result<()>
    where
        T: Handler,
    {
        if self.query_servers_task.update_time(now) {
            self.query_servers_from_masters(buffer, handler)?;
        }

        if self.query_info_task.update_time(now) {
            self.query_info_from_servers(buffer, handler)?;
        }

        if self.cleanup_task.update_time(now) {
            self.cleanup_servers(now);
        }

        Ok(())
    }

    pub(crate) fn wait_event_internal<'a, T>(
        &mut self,
        buffer: &'a mut Buffer,
        timeout: Option<Duration>,
        handler: &mut T,
    ) -> io::Result<InternalEvent<'a>>
    where
        T: Handler,
    {
        if let Some(delayed_event) = self.delayed_events.pop() {
            return Ok(delayed_event.into());
        }

        let deadline = timeout.map(|t| Instant::now() + t);

        loop {
            // FIXME: Work around limitation in current borrow checker, remove when polonius
            // will become available in MSRV.
            //
            // SAFETY: Used and returned only in this iteration.
            let buffer = unsafe { &mut *(&mut buffer.data as *mut [u8]) };

            let now = Instant::now();
            if let Some(deadline) = deadline {
                if deadline <= now {
                    return Ok(Event::Timeout.into());
                }
            }

            self.process_tasks(buffer, now, handler)?;
            self.process_pending(buffer)?;

            if let Some(delayed_event) = self.delayed_events.pop() {
                return Ok(delayed_event.into());
            }

            if let Some(event) = self.receive(buffer, deadline, handler)? {
                return Ok(event);
            }
        }
    }

    pub fn wait_event<'a>(
        &mut self,
        buffer: &'a mut Buffer,
        timeout: Option<Duration>,
    ) -> io::Result<Event<'a>> {
        struct StubHandler;
        impl Handler for StubHandler {}

        match self.wait_event_internal(buffer, timeout, &mut StubHandler)? {
            InternalEvent::Stop => unreachable!(),
            InternalEvent::Event(event) => Ok(event),
            InternalEvent::MasterInvalidPacket(address, data, _) => {
                Ok(Event::MasterInvalidPacket(address, data))
            }
            InternalEvent::ServerInvalidProtocol(address, _) => {
                Ok(Event::ServerInvalidProtocol(address))
            }
            InternalEvent::ServerInvalidPacket(address, _, data, _) => {
                Ok(Event::ServerInvalidPacket(address, data))
            }
        }
    }
}
