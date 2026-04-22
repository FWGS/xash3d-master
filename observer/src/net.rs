use std::{
    io,
    net::{SocketAddr, UdpSocket},
    time::Duration,
};

use xash3d_protocol::wrappers::Str;

/// A simple wrapper for [UdpSocket].
pub struct Socket {
    inner: UdpSocket,
}

impl Socket {
    pub fn bind(addr: SocketAddr) -> io::Result<Self> {
        let inner = UdpSocket::bind(addr)?;
        Ok(Self { inner })
    }

    pub fn local_addr(&self) -> io::Result<SocketAddr> {
        self.inner.local_addr()
    }

    pub fn set_read_timeout(&self, dur: Option<Duration>) -> io::Result<()> {
        self.inner.set_read_timeout(dur)
    }

    pub fn recv_from(&self, buf: &mut [u8]) -> io::Result<(usize, SocketAddr)> {
        let result = self.inner.recv_from(buf);
        if let Ok((n, from)) = &result {
            trace!("recv {from} {:?}", Str::from(&buf[..*n]));
        }
        result
    }

    pub fn send_to(&self, buf: &[u8], addr: SocketAddr) -> io::Result<usize> {
        trace!("send {addr} {:?}", Str::from(buf));
        self.inner.send_to(buf, addr)
    }
}
