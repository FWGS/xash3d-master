use std::{
    io,
    marker::PhantomData,
    net::{Ipv4Addr, SocketAddr, SocketAddrV4, ToSocketAddrs},
    time::Duration,
};

use xash3d_protocol::{wrappers::Str, Error as ProtocolError};

use crate::{
    connection::ConnectionState,
    event::{Event, InternalEvent},
    filter::{Filter, Version},
    observer_new::{Buffer, Master, ObserverNew},
    Server,
};

pub type GetServerInfoResponse<'a, T = &'a [u8]> =
    xash3d_protocol::server::GetServerInfoResponse<T>;

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
        let data = Str(packet);
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
        let data = Str(packet);
        debug!("invalid packet from server {addr}: {error} \"{data}\"");
    }
}

pub struct ObserverBuilder<'a> {
    filter: Filter,
    phantom: PhantomData<&'a ()>,
}

impl<'a> ObserverBuilder<'a> {
    /// Creates a new observer builder with the default client version.
    ///
    /// See [Self::client_version] for more information.
    pub fn with_default_client_version() -> Self {
        Self {
            filter: Filter::with_default_client_version(),
            phantom: PhantomData,
        }
    }

    /// Creates a new observer builder.
    pub fn new() -> Self {
        Self {
            filter: Filter::new(),
            phantom: PhantomData,
        }
    }

    // Sets a client version for requests sent to master servers.
    //
    // # Note
    //
    // The master server may respond with a fake server if the client version is lower than
    // what is specified in the master server's configuration file.
    pub fn client_version(mut self, version: Version) -> Self {
        self.filter.set_client_version(version);
        self
    }

    // Sets a client build number for requests sent to master servers.
    //
    // # Note
    //
    // The master server may respond with a fake server if the client build number is lower than
    // what is specified in the master server's configuration file.
    pub fn client_build_number(mut self, build_number: u32) -> Self {
        self.filter.set_client_build_number(build_number);
        self
    }

    pub fn gamedir(mut self, value: &'a str) -> Self {
        self.filter.set_gamedir(value);
        self
    }

    pub fn nat(mut self, value: bool) -> Self {
        self.filter.set_nat(value);
        self
    }

    pub fn filter(mut self, value: &'a str) -> Self {
        self.filter.set_raw(value);
        self
    }

    pub fn build<T: Handler>(
        self,
        handler: T,
        masters: &[impl AsRef<str>],
    ) -> io::Result<Observer<T>> {
        let addr = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0));
        let mut inner = ObserverNew::bind(addr)?;

        let local_addr = inner.sock.local_addr()?;
        for i in masters {
            for addr in i.as_ref().to_socket_addrs()? {
                if local_addr.is_ipv4() == addr.is_ipv4() {
                    inner.insert_master(Master::new(addr));
                    break;
                }
            }
        }

        inner.set_filter(&self.filter);

        Ok(Observer { inner, handler })
    }
}

impl<'a> Default for ObserverBuilder<'a> {
    fn default() -> Self {
        Self::with_default_client_version()
    }
}

pub struct Observer<T> {
    inner: ObserverNew,
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

    fn handle_server_from_master(&mut self, master: &SocketAddr, server: SocketAddr) {
        if self.handler.query_info_for_server(*master, server) {
            self.inner.insert_server(Server::new(server));
        } else {
            self.inner.remove_server(&server);
        }
    }

    pub fn run(&mut self) -> io::Result<()> {
        let mut buffer = Buffer::new();

        loop {
            match self
                .inner
                .wait_event_internal(&mut buffer, None, &mut self.handler)?
            {
                InternalEvent::Stop => break,
                InternalEvent::Event(event) => match event {
                    Event::ServerList(servers) => {
                        for addr in servers.iter() {
                            self.handle_server_from_master(servers.master(), addr);
                        }
                    }
                    Event::ServerInfo(info) => {
                        if info.is_changed() {
                            self.handler.server_update(
                                *info.address(),
                                &info.response,
                                info.new,
                                info.ping(),
                            );
                        } else {
                            self.handler
                                .server_update_ping(*info.address(), info.ping());
                        }
                    }
                    Event::ServerInfoTimeout(addr) => self.handler.server_timeout(addr),
                    Event::ServerRemove(addr) => self.handler.server_remove(addr),
                    _ => unreachable!(),
                },
                InternalEvent::MasterInvalidPacket(address, data, error) => {
                    self.handler.master_invalid_packet(address, data, error);
                }
                InternalEvent::ServerInvalidProtocol(address, time) => {
                    self.handler.server_invalid_protocol(address, time);
                }
                InternalEvent::ServerInvalidPacket(address, time, data, error) => {
                    self.handler
                        .server_invalid_packet(address, time, data, error);
                }
            }
        }

        for (&addr, con) in self.inner.connections.iter() {
            if con.state() == ConnectionState::ProtocolDetection {
                self.handler.server_timeout(addr);
            }
        }

        Ok(())
    }
}
