use std::{
    cmp,
    collections::{hash_map::Entry, HashMap},
    io,
    net::{IpAddr, SocketAddr},
    time::{Duration, Instant},
};

use mio::{Events, Poll, Token};
use slab::Slab;

use crate::{event::Event, filter::Filter, master::Master, net::Socket, server::Server};

pub(crate) const MASTER_INTERVAL: Duration = Duration::from_secs(8);
pub(crate) const SERVER_INTERVAL: Duration = Duration::from_secs(2);
pub(crate) const SERVER_TIMEOUT: Duration = Duration::from_secs(16);
pub(crate) const SERVER_CLEAN_INTERVAL: Duration = Duration::from_secs(16);

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

struct ObserverState {
    filter: String,
    masters: Vec<Master>,
    query_servers_task: Task,
    query_info_task: Task,
    cleanup_task: Task,
    servers: HashMap<SocketAddr, Server>,
    delayed_events: Vec<DelayedEvent>,
    pending: Vec<Pending>,
}

impl ObserverState {
    fn new() -> Self {
        let now = Instant::now();
        Self {
            filter: String::new(),
            masters: Vec::new(),
            query_servers_task: Task::new(now, MASTER_INTERVAL),
            query_info_task: Task::new(now, SERVER_INTERVAL),
            cleanup_task: Task::new(now, SERVER_CLEAN_INTERVAL),
            servers: HashMap::new(),
            delayed_events: Vec::new(),
            pending: Vec::new(),
        }
    }

    fn get_master_mut(&mut self, addr: &SocketAddr) -> Option<&mut Master> {
        self.masters
            .iter_mut()
            .find(|master| master.address().eq(addr))
    }

    fn query_servers_from_masters(
        &mut self,
        sockets: &mut Sockets,
        buf: &mut [u8],
    ) -> io::Result<()> {
        for master in self.masters.iter_mut() {
            let packet = master.encode_query_servers_packet(&self.filter, buf);

            // Do not send queries twice.
            if self.pending.contains(&Pending::Master(*master.address())) {
                continue;
            }

            let sock = sockets.get_or_create_for(master.address())?;
            sock.send_to(packet, *master.address())?;
        }
        Ok(())
    }

    fn query_info_from_servers(
        &mut self,
        sockets: &mut Sockets,
        buffer: &mut [u8],
    ) -> io::Result<()> {
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

            let sock = sockets.get_or_create_for(server.address())?;
            server.query(sock, buffer)?;
        }

        Ok(())
    }

    fn process_pending(&mut self, sockets: &mut Sockets, buffer: &mut [u8]) -> io::Result<()> {
        while let Some(i) = self.pending.pop() {
            match i {
                Pending::Master(addr) => {
                    for master in self.masters.iter_mut() {
                        if *master.address() == addr {
                            let packet = master.encode_query_servers_packet(&self.filter, buffer);
                            let sock = sockets.get_or_create_for(&addr)?;
                            sock.send_to(packet, addr)?;
                            break;
                        }
                    }
                }
                Pending::Server(addr) => {
                    if let Some(server) = self.servers.get_mut(&addr) {
                        let sock = sockets.get_or_create_for(&addr)?;
                        server.query(sock, buffer)?;
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

    fn process_tasks(
        &mut self,
        sockets: &mut Sockets,
        buffer: &mut [u8],
        now: Instant,
    ) -> io::Result<()> {
        if self.query_servers_task.update_time(now) {
            self.query_servers_from_masters(sockets, buffer)?;
        }

        if self.query_info_task.update_time(now) {
            self.query_info_from_servers(sockets, buffer)?;
        }

        if self.cleanup_task.update_time(now) {
            self.cleanup_servers(now);
        }

        Ok(())
    }

    fn timeout(&self, now: Instant, user_deadline: Option<Instant>) -> Option<Duration> {
        let mut deadline = self.query_info_task.time();

        if self.masters.is_empty() {
            deadline = cmp::min(deadline, self.query_info_task.time());
        }

        if let Some(user_deadline) = user_deadline {
            deadline = cmp::min(deadline, user_deadline);
        }

        Some(deadline.duration_since(now))
    }

    fn handle_packet<'a>(
        &mut self,
        sock: &Socket,
        from: &SocketAddr,
        buffer: &'a [u8],
    ) -> io::Result<Option<Event<'a>>> {
        if let Some(master) = self.get_master_mut(from) {
            return Ok(master.handle_packet(from, buffer));
        }

        if let Some(server) = self.servers.get_mut(from) {
            return server.handle_packet(sock, buffer).inspect(|event| {
                if let Some(Event::ServerInvalidProtocol(..)) = &event {
                    self.servers.remove(from);
                }
            });
        }

        Ok(None)
    }
}

#[derive(Default)]
struct SocketsData {
    slab: Slab<Socket>,
    map: HashMap<IpAddr, usize>,
}

impl SocketsData {
    fn borrow_mut<'a>(&'a mut self, poll: &'a mut Poll) -> Sockets<'a> {
        Sockets { poll, data: self }
    }
}

struct Sockets<'a> {
    poll: &'a mut Poll,
    data: &'a mut SocketsData,
}

impl<'a> Sockets<'a> {
    fn get(&self, token: Token) -> Option<&Socket> {
        self.data.slab.get(token.0)
    }

    fn get_or_create_for(&mut self, addr: &SocketAddr) -> io::Result<&Socket> {
        match self.data.map.entry(addr.ip()) {
            Entry::Occupied(e) => Ok(&self.data.slab[*e.get()]),
            Entry::Vacant(e) => {
                trace!("creating UDP socket for {}", addr.ip());
                let s = self.data.slab.vacant_entry();
                let mut sock = Socket::bind_for(addr)?;
                sock.register(self.poll.registry(), Token(s.key()))?;
                e.insert(s.key());
                Ok(s.insert(sock))
            }
        }
    }
}

pub struct Observer {
    poll: Poll,
    net_events: Events,
    current_net_event: usize,
    sockets: SocketsData,
    state: ObserverState,
}

impl Observer {
    pub fn new() -> io::Result<Self> {
        let poll = Poll::new()?;
        let events = Events::with_capacity(2);
        let sockets = SocketsData::default();
        let state = ObserverState::new();

        Ok(Self {
            poll,
            net_events: events,
            current_net_event: 0,
            sockets,
            state,
        })
    }

    pub fn set_filter_raw(&mut self, filter: String) {
        self.state.filter = filter;
    }

    pub fn set_filter(&mut self, filter: &Filter) {
        self.set_filter_raw(filter.to_raw_string());
    }

    fn remove_pending(&mut self, pending: Pending) {
        if let Some(i) = self.state.pending.iter().position(|&i| i == pending) {
            self.state.pending.swap_remove(i);
        }
    }

    pub fn insert_master(&mut self, master: Master) {
        if self.state.get_master_mut(master.address()).is_none() {
            self.state.pending.push(Pending::Master(*master.address()));
            self.state.masters.push(master);
        }
    }

    pub fn remove_master(&mut self, addr: &SocketAddr) -> Option<Master> {
        self.remove_pending(Pending::Master(*addr));
        match self.state.masters.iter().position(|i| i.address() == addr) {
            Some(i) => Some(self.state.masters.swap_remove(i)),
            None => None,
        }
    }

    pub fn insert_server(&mut self, server: Server) {
        let addr = *server.address();
        if let Entry::Vacant(e) = self.state.servers.entry(addr) {
            self.state.pending.push(Pending::Server(addr));
            e.insert(server);
        }
    }

    pub fn remove_server(&mut self, addr: &SocketAddr) {
        self.remove_pending(Pending::Server(*addr));
        self.state.servers.remove(addr);
    }

    #[inline(always)]
    pub fn masters(&self) -> &[Master] {
        &self.state.masters
    }

    pub fn wait_event<'a>(
        &mut self,
        buffer: &'a mut Buffer,
        timeout: Option<Duration>,
    ) -> io::Result<Event<'a>> {
        if let Some(delayed_event) = self.state.delayed_events.pop() {
            return Ok(delayed_event.into());
        }

        let user_deadline = timeout.map(|t| Instant::now() + t);
        let mut sockets = self.sockets.borrow_mut(&mut self.poll);

        loop {
            // FIXME: Work around limitation in current borrow checker, remove when polonius
            // will become available in MSRV.
            //
            // SAFETY: Used and returned only in this iteration.
            let buffer = unsafe { &mut *(&mut buffer.data as *mut [u8]) };

            let now = Instant::now();
            if let Some(user_deadline) = user_deadline {
                if user_deadline <= now {
                    return Ok(Event::Timeout);
                }
            }

            self.state.process_tasks(&mut sockets, buffer, now)?;
            self.state.process_pending(&mut sockets, buffer)?;

            if let Some(delayed_event) = self.state.delayed_events.pop() {
                return Ok(delayed_event.into());
            }

            if self.net_events.is_empty() {
                let timeout = self.state.timeout(now, user_deadline);
                sockets.poll.poll(&mut self.net_events, timeout)?;
                self.current_net_event = 0;
            }

            for net_event in self.net_events.iter().skip(self.current_net_event) {
                let Some(sock) = sockets.get(net_event.token()) else {
                    self.current_net_event += 1;
                    error!("unexpected poll event");
                    continue;
                };

                if net_event.is_readable() {
                    loop {
                        // FIXME: Work around limitation in current borrow checker, remove
                        // when polonius will become available in MSRV.
                        //
                        // SAFETY: Used and returned only in this iteration.
                        let buffer = unsafe { &mut *(buffer as *mut [u8]) };

                        match sock.recv_from(buffer) {
                            Ok((n, from)) => {
                                if let Some(event) =
                                    self.state.handle_packet(sock, &from, &buffer[..n])?
                                {
                                    return Ok(event);
                                }
                            }
                            Err(e) if would_block(&e) => break,
                            Err(e) => return Err(e),
                        }
                    }
                }

                self.current_net_event += 1;
            }

            self.net_events.clear();
        }
    }
}

#[inline(always)]
fn would_block(err: &io::Error) -> bool {
    err.kind() == io::ErrorKind::WouldBlock
}
