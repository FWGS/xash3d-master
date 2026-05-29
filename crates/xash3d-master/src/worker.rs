use std::{
    fmt, io,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

use mio::{Events, Poll, Token, Waker};

use crate::{
    config::Config,
    udp_server::{UdpServer, UdpServerError},
};

const WAKER_TOKEN: Token = Token(0);
const UDP_SERVER_TOKEN: Token = Token(1);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct WorkerId(usize);

impl WorkerId {
    fn new() -> Self {
        static CURRENT: AtomicUsize = AtomicUsize::new(0);
        Self(CURRENT.fetch_add(1, Ordering::Relaxed))
    }
}

impl fmt::Display for WorkerId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "worker#{}", self.0)
    }
}

pub struct WorkerBuilder {
    poll: Poll,
    waker: Arc<Waker>,
    udp_server: Option<UdpServer>,
}

impl WorkerBuilder {
    fn new() -> io::Result<Self> {
        let poll = Poll::new()?;
        let waker = Waker::new(poll.registry(), WAKER_TOKEN)?;
        Ok(Self {
            poll,
            waker: Arc::new(waker),
            udp_server: None,
        })
    }

    pub fn udp_server(mut self, mut udp_server: UdpServer) -> io::Result<Self> {
        let registry = self.poll.registry();
        udp_server.register(registry, UDP_SERVER_TOKEN)?;
        self.udp_server = Some(udp_server);
        Ok(self)
    }

    pub fn build(self) -> Worker {
        Worker {
            id: WorkerId::new(),
            poll: self.poll,
            waker: self.waker,
            udp_server: self.udp_server.expect("UdpServer is not registered"),
        }
    }
}

pub struct Worker {
    id: WorkerId,
    poll: Poll,
    waker: Arc<Waker>,
    udp_server: UdpServer,
}

impl Worker {
    pub fn builder() -> io::Result<WorkerBuilder> {
        WorkerBuilder::new()
    }

    pub fn waker(&self) -> Arc<Waker> {
        self.waker.clone()
    }

    pub fn udp_server(&self) -> &UdpServer {
        &self.udp_server
    }

    pub fn try_clone(&self) -> Result<Self, UdpServerError> {
        let worker = Self::builder()?
            .udp_server(self.udp_server.try_clone()?)?
            .build();
        Ok(worker)
    }

    pub fn udp_server_replace(&mut self, udp_server: UdpServer) -> Result<(), UdpServerError> {
        let registry = self.poll.registry();
        self.udp_server.deregister(registry)?;
        self.udp_server = udp_server;
        self.udp_server.register(registry, UDP_SERVER_TOKEN)?;
        Ok(())
    }

    pub fn udp_server_update_config(&mut self, cfg: &Config) -> Result<(), UdpServerError> {
        // UDP server will rebind the socket if the listen address was changed.
        let registry = self.poll.registry();
        self.udp_server.deregister(registry)?;
        self.udp_server.update_config(cfg)?;
        self.udp_server.register(registry, UDP_SERVER_TOKEN)?;
        Ok(())
    }

    pub fn run(&mut self) -> Result<(), UdpServerError> {
        debug!("{}: started", self.id);
        let mut events = Events::with_capacity(1024);
        loop {
            self.poll.poll(&mut events, None)?;

            for event in events.iter() {
                match event.token() {
                    WAKER_TOKEN => {
                        debug!("{}: stop", self.id);
                        return Ok(());
                    }
                    UDP_SERVER_TOKEN => self.udp_server.run()?,
                    _ => {
                        // TODO: worker timeout
                    }
                }
            }
        }
    }
}
