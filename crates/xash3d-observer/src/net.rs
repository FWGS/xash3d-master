use std::{io, net::SocketAddr};

use mio::{net::UdpSocket, Interest, Registry, Token};
use xash3d_protocol::wrappers::Str;

/// A simple wrapper for [UdpSocket](mio::net::UdpSocket).
pub struct Socket {
    inner: UdpSocket,
}

impl Socket {
    pub fn bind_for(addr: &SocketAddr) -> io::Result<Self> {
        let bind_addr = match addr {
            SocketAddr::V4(..) => SocketAddr::from(([0; 4], 0)),
            SocketAddr::V6(..) => SocketAddr::from(([0; 16], 0)),
        };
        let inner = UdpSocket::bind(bind_addr)?;
        Ok(Self { inner })
    }

    pub fn register(&mut self, registry: &Registry, token: Token) -> io::Result<()> {
        registry.register(&mut self.inner, token, Interest::READABLE)
    }

    #[inline(always)]
    pub fn recv_from(&self, buf: &mut [u8]) -> io::Result<(usize, SocketAddr)> {
        let result = self.inner.recv_from(buf);
        if let Ok((n, from)) = &result {
            trace!("recv {from} {:?}", Str::from(&buf[..*n]));
        }
        result
    }

    #[inline(always)]
    pub fn send_to(&self, buf: &[u8], addr: SocketAddr) -> io::Result<usize> {
        trace!("send {addr} {:?}", Str::from(buf));
        self.inner.send_to(buf, addr)
    }
}
