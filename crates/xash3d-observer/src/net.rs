use std::{
    io,
    net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6},
};

use mio::{net::UdpSocket, Interest, Registry, Token};
use xash3d_protocol::wrappers::Str;

/// A simple wrapper for [UdpSocket](mio::net::UdpSocket).
pub struct Socket {
    v4: Option<UdpSocket>,
    v6: Option<UdpSocket>,
}

impl Socket {
    pub fn bind() -> io::Result<Self> {
        let addr = SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0);
        let v4 = UdpSocket::bind(addr.into())
            .inspect_err(|err| {
                warn!("failed to bind IPv4 socket: {err}");
            })
            .ok();
        let addr = SocketAddrV6::new(Ipv6Addr::UNSPECIFIED, 0, 0, 0);
        let v6 = UdpSocket::bind(addr.into())
            .inspect_err(|err| {
                warn!("failed to bind IPv6 socket: {err}");
            })
            .ok();
        Ok(Self { v4, v6 })
    }

    pub fn register(
        &mut self,
        registry: &Registry,
        token_v4: Token,
        token_v6: Token,
    ) -> io::Result<()> {
        if let Some(sock) = self.v4.as_mut() {
            registry.register(sock, token_v4, Interest::READABLE)?;
        }
        if let Some(sock) = self.v6.as_mut() {
            registry.register(sock, token_v6, Interest::READABLE)?;
        }
        Ok(())
    }

    #[inline(always)]
    pub fn socket(&self, ipv6: bool) -> Option<&UdpSocket> {
        if ipv6 {
            self.v6.as_ref()
        } else {
            self.v4.as_ref()
        }
    }

    #[inline(always)]
    pub fn recv_from(&self, buf: &mut [u8], ipv6: bool) -> io::Result<(usize, SocketAddr)> {
        if let Some(sock) = self.socket(ipv6) {
            let result = sock.recv_from(buf);
            if let Ok((n, from)) = &result {
                trace!("recv {from} {:?}", Str::from(&buf[..*n]));
            }
            result
        } else {
            Err(io::Error::from(io::ErrorKind::AddrNotAvailable))
        }
    }

    #[inline(always)]
    pub fn send_to(&self, buf: &[u8], addr: SocketAddr) -> io::Result<usize> {
        trace!("send {addr} {:?}", Str::from(buf));
        if let Some(sock) = self.socket(addr.is_ipv6()) {
            sock.send_to(buf, addr)
        } else {
            Err(io::Error::from(io::ErrorKind::AddrNotAvailable))
        }
    }
}
