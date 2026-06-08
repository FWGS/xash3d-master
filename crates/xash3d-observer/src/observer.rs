use std::{
    cmp,
    collections::{hash_map::Entry, HashMap},
    fmt, io,
    net::SocketAddr,
    time::{Duration, Instant},
};

use xash3d_protocol::{
    game::QueryServers, master::QueryServersResponse, server::GetServerInfoResponse,
};

use crate::{
    event::{Event, ServerInfo, ServerList},
    filter::Filter,
    net::Socket,
    server::Server,
};

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

        let packet = QueryServers::new(FilterKey {
            filter,
            key: self.key,
        });

        // TODO: handle error, filter may not fit
        packet.encode(buf).unwrap()
    }
}

enum DelayedEvent {
    ServerTimeout(SocketAddr),
    ServerRemove(SocketAddr),
}

impl<'a> From<DelayedEvent> for Event<'a> {
    fn from(value: DelayedEvent) -> Self {
        match value {
            DelayedEvent::ServerTimeout(addr) => Event::ServerInfoTimeout(addr),
            DelayedEvent::ServerRemove(addr) => Event::ServerRemove(addr),
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

pub struct Observer {
    sock: Socket,
    filter: String,
    masters: Vec<Master>,
    query_servers_task: Task,
    query_info_task: Task,
    cleanup_task: Task,
    servers: HashMap<SocketAddr, Server>,
    delayed_events: Vec<DelayedEvent>,
    pending: Vec<Pending>,
}

impl Observer {
    // TODO: bind ipv4 and ipv6 at the same time
    pub fn bind(addr: SocketAddr) -> io::Result<Self> {
        let sock = Socket::bind(addr)?;
        let servers = HashMap::new();
        let now = Instant::now();

        Ok(Self {
            sock,
            filter: String::new(),
            masters: Vec::new(),
            query_servers_task: Task::new(now, MASTER_INTERVAL),
            query_info_task: Task::new(now, SERVER_INTERVAL),
            cleanup_task: Task::new(now, SERVER_CLEAN_INTERVAL),
            servers,
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
        let addr = *server.address();
        if let Entry::Vacant(e) = self.servers.entry(addr) {
            self.pending.push(Pending::Server(addr));
            e.insert(server);
        }
    }

    pub fn remove_server(&mut self, addr: &SocketAddr) {
        self.remove_pending(Pending::Server(*addr));
        self.servers.remove(addr);
    }

    #[inline(always)]
    pub fn masters(&self) -> &[Master] {
        &self.masters
    }

    fn get_master(&self, addr: &SocketAddr) -> Option<&Master> {
        self.masters.iter().find(|master| master.addr.eq(addr))
    }

    fn query_servers_from_masters(&mut self, buf: &mut [u8]) -> io::Result<()> {
        for master in self.masters.iter_mut() {
            let packet = master.encode_query_servers_packet(&self.filter, buf);

            // Do not send queries twice.
            if self.pending.contains(&Pending::Master(master.addr)) {
                continue;
            }

            self.sock.send_to(packet, master.addr)?;
        }
        Ok(())
    }

    fn query_info_from_servers(&mut self, buffer: &mut [u8]) -> io::Result<()> {
        let now = Instant::now();
        for (addr, server) in self.servers.iter_mut() {
            // Invalid servers will be removed later by cleanup task. Master servers can send
            // such servers again. Servers will become invalid if no response will be received in
            // SERVER_TIMEOUT seconds.
            if !server.is_valid(now) {
                continue;
            }

            // Do not send queries twice.
            if self.pending.contains(&Pending::Server(*addr)) {
                continue;
            }

            // This server did not send a response to the last request.
            if !server.is_idle() {
                self.delayed_events.push(DelayedEvent::ServerTimeout(*addr));
            }

            server.query(&self.sock, buffer)?;
        }

        Ok(())
    }

    fn handle_master_packet<'a>(
        &mut self,
        from: &SocketAddr,
        data: &'a [u8],
        key: u32,
    ) -> Option<Event<'a>> {
        match QueryServersResponse::decode(data) {
            Ok(response) => {
                if response.key != Some(key) {
                    // ignore if invalid or missing challenge key in the response
                    return None;
                }

                Some(Event::ServerList(ServerList::new(*from, response)))
            }
            Err(_) => {
                // The master server can respond with a fake server at same address. It's used
                // for update messages.
                if let Ok(response) = GetServerInfoResponse::decode(data) {
                    let info = ServerInfo {
                        server: *from,
                        ping: Duration::default(),
                        changed: true,
                        response,
                    };
                    Some(Event::ServerInfo(info))
                } else {
                    Some(Event::MasterInvalidPacket(*from, data))
                }
            }
        }
    }

    fn handle_server_packet<'a>(
        &mut self,
        from: &SocketAddr,
        data: &'a [u8],
    ) -> io::Result<Option<Event<'a>>> {
        match self.servers.get_mut(from) {
            Some(server) => {
                let result = server.handle_packet(&self.sock, data);
                if let Ok(Some(Event::ServerInvalidProtocol(..))) = &result {
                    self.servers.remove(from);
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
    ) -> io::Result<Option<Event<'a>>> {
        if let Some(master) = self.get_master(from) {
            Ok(self.handle_master_packet(from, buffer, master.key))
        } else {
            self.handle_server_packet(from, buffer)
        }
    }

    fn receive<'a>(
        &mut self,
        buffer: &'a mut [u8],
        user_deadline: Option<Instant>,
    ) -> io::Result<Option<Event<'a>>> {
        let mut deadline = cmp::min(self.query_servers_task.time(), self.query_info_task.time());
        if let Some(user_deadline) = user_deadline {
            deadline = cmp::min(deadline, user_deadline);
        }
        let mut now = Instant::now();
        while now < deadline {
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
                    if let Some(server) = self.servers.get_mut(&addr) {
                        server.query(&self.sock, buffer)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn cleanup_servers(&mut self, now: Instant) {
        self.servers.retain(|&addr, server| {
            if !server.is_valid(now) {
                self.delayed_events.push(DelayedEvent::ServerRemove(addr));
                false
            } else {
                true
            }
        });
    }

    fn process_tasks(&mut self, buffer: &mut [u8], now: Instant) -> io::Result<()> {
        if self.query_servers_task.update_time(now) {
            self.query_servers_from_masters(buffer)?;
        }

        if self.query_info_task.update_time(now) {
            self.query_info_from_servers(buffer)?;
        }

        if self.cleanup_task.update_time(now) {
            self.cleanup_servers(now);
        }

        Ok(())
    }

    pub fn wait_event<'a>(
        &mut self,
        buffer: &'a mut Buffer,
        timeout: Option<Duration>,
    ) -> io::Result<Event<'a>> {
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
                    return Ok(Event::Timeout);
                }
            }

            self.process_tasks(buffer, now)?;
            self.process_pending(buffer)?;

            if let Some(delayed_event) = self.delayed_events.pop() {
                return Ok(delayed_event.into());
            }

            if let Some(event) = self.receive(buffer, deadline)? {
                return Ok(event);
            }
        }
    }
}
