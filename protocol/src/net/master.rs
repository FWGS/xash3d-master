// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

//! Master server packets.

use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6};

use crate::{
    cursor::{Cursor, CursorMut},
    Error,
};

/// Master server challenge response packet.
#[derive(Clone, Debug, PartialEq)]
pub struct ChallengeResponse {
    /// A number that a game server must send back.
    pub master_challenge: u32,
    /// A number that a master server received in challenge packet.
    pub server_challenge: Option<u32>,
}

impl ChallengeResponse {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffs\n";

    /// Creates a new `ChallengeResponse`.
    pub fn new(master_challenge: u32, server_challenge: Option<u32>) -> Self {
        Self {
            master_challenge,
            server_challenge,
        }
    }

    /// Decode packet from `src`.
    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        let master_challenge = cur.get_u32_le()?;
        let server_challenge = if cur.remaining() == 4 {
            Some(cur.get_u32_le()?)
        } else {
            None
        };
        cur.expect_empty()?;
        Ok(Self {
            master_challenge,
            server_challenge,
        })
    }

    /// Encode packet to `buf`.
    pub fn encode<const N: usize>(&self, buf: &mut [u8; N]) -> Result<usize, Error> {
        let mut cur = CursorMut::new(buf);
        cur.put_bytes(Self::HEADER)?;
        cur.put_u32_le(self.master_challenge)?;
        if let Some(server_challenge) = self.server_challenge {
            cur.put_u32_le(server_challenge)?;
        }
        Ok(cur.pos())
    }
}

/// Helper trait for dealing with server addresses.
pub trait ServerAddress: Sized {
    /// Size of IP and port in bytes.
    fn size() -> usize;

    /// Read address from a cursor.
    fn get(cur: &mut Cursor) -> Result<Self, Error>;

    /// Write address to a cursor.
    fn put(&self, cur: &mut CursorMut) -> Result<(), Error>;
}

impl ServerAddress for SocketAddrV4 {
    fn size() -> usize {
        6
    }

    fn get(cur: &mut Cursor) -> Result<Self, Error> {
        let ip = Ipv4Addr::from(cur.get_array()?);
        let port = cur.get_u16_be()?;
        Ok(SocketAddrV4::new(ip, port))
    }

    fn put(&self, cur: &mut CursorMut) -> Result<(), Error> {
        cur.put_array(&self.ip().octets())?;
        cur.put_u16_be(self.port())?;
        Ok(())
    }
}

impl ServerAddress for SocketAddrV6 {
    fn size() -> usize {
        18
    }

    fn get(cur: &mut Cursor) -> Result<Self, Error> {
        let ip = Ipv6Addr::from(cur.get_array()?);
        let port = cur.get_u16_be()?;
        Ok(SocketAddrV6::new(ip, port, 0, 0))
    }

    fn put(&self, cur: &mut CursorMut) -> Result<(), Error> {
        cur.put_array(&self.ip().octets())?;
        cur.put_u16_be(self.port())?;
        Ok(())
    }
}

/// Game server addresses list.
#[derive(Clone, Debug, PartialEq)]
pub struct QueryServersResponse<I> {
    inner: I,
    /// A challenge number received in a filter string.
    pub key: Option<u32>,
}

impl QueryServersResponse<()> {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xfff\n";
}

impl<'a> QueryServersResponse<&'a [u8]> {
    /// Decode packet from `src`.
    pub fn decode(src: &'a [u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(QueryServersResponse::HEADER)?;
        let s = cur.end();

        // extra header for key sent in QueryServers packet
        let (inner, key) = if s.len() >= 6 && s[0] == 0x7f && s[5] == 8 {
            let key = u32::from_le_bytes([s[1], s[2], s[3], s[4]]);
            (&s[6..], Some(key))
        } else {
            (s, None)
        };

        Ok(Self { inner, key })
    }

    /// Iterator over game server addresses.
    pub fn iter<A>(&self) -> impl 'a + Iterator<Item = A>
    where
        A: ServerAddress,
    {
        let mut cur = Cursor::new(self.inner);
        core::iter::from_fn(move || {
            if cur.remaining() == A::size() && cur.end().ends_with(&[0; 2]) {
                // skip last address with port 0
                return None;
            }
            A::get(&mut cur).ok()
        })
    }

    /// Returns `true` if game server addresses list is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

impl QueryServersResponse<()> {
    /// Creates a new `QueryServersResponse`.
    pub fn new(key: Option<u32>) -> Self {
        Self { inner: (), key }
    }

    /// Encode packet to `buf`.
    ///
    /// Returns number of bytes written into `buf` and how many items was written.
    pub fn encode<A>(&mut self, buf: &mut [u8], list: &[A]) -> Result<(usize, usize), Error>
    where
        A: ServerAddress,
    {
        let mut cur = CursorMut::new(buf);
        cur.put_bytes(QueryServersResponse::HEADER)?;
        if let Some(key) = self.key {
            cur.put_u8(0x7f)?;
            cur.put_u32_le(key)?;
            cur.put_u8(8)?;
        }
        let mut count = 0;
        let mut iter = list.iter();
        while cur.available() >= A::size() * 2 {
            if let Some(i) = iter.next() {
                i.put(&mut cur)?;
                count += 1;
            } else {
                break;
            }
        }
        for _ in 0..A::size() {
            cur.put_u8(0)?;
        }
        Ok((cur.pos(), count))
    }
}

/// Announce a game client to game server behind NAT.
#[derive(Clone, Debug, PartialEq)]
pub struct ClientAnnounce {
    /// Address of the client.
    pub addr: SocketAddr,
}

impl ClientAnnounce {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffc ";

    /// Creates a new `ClientAnnounce`.
    pub fn new(addr: SocketAddr) -> Self {
        Self { addr }
    }

    /// Decode packet from `src`.
    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        let addr = cur
            .get_str(cur.remaining())?
            .parse()
            .map_err(|_| Error::InvalidClientAnnounceIp)?;
        cur.expect_empty()?;
        Ok(Self { addr })
    }

    /// Encode packet to `buf`.
    pub fn encode(&self, buf: &mut [u8]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf)
            .put_bytes(Self::HEADER)?
            .put_as_str(self.addr)?
            .pos())
    }
}

/// Admin challenge response.
#[derive(Clone, Debug, PartialEq)]
pub struct AdminChallengeResponse {
    /// A number that admin must sent back to a master server.
    pub master_challenge: u32,
    /// A number with which to mix a password hash.
    pub hash_challenge: u32,
}

impl AdminChallengeResponse {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffadminchallenge";

    /// Creates a new `AdminChallengeResponse`.
    pub fn new(master_challenge: u32, hash_challenge: u32) -> Self {
        Self {
            master_challenge,
            hash_challenge,
        }
    }

    /// Decode packet from `src`.
    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        let master_challenge = cur.get_u32_le()?;
        let hash_challenge = cur.get_u32_le()?;
        cur.expect_empty()?;
        Ok(Self {
            master_challenge,
            hash_challenge,
        })
    }

    /// Encode packet to `buf`.
    pub fn encode(&self, buf: &mut [u8]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf)
            .put_bytes(Self::HEADER)?
            .put_u32_le(self.master_challenge)?
            .put_u32_le(self.hash_challenge)?
            .pos())
    }
}

/// Master server packet.
#[derive(Clone, Debug, PartialEq)]
pub enum Packet<'a> {
    /// Master server challenge response packet.
    ChallengeResponse(ChallengeResponse),
    /// Game server addresses list.
    QueryServersResponse(QueryServersResponse<&'a [u8]>),
    /// Announce a game client to game server behind NAT.
    ClientAnnounce(ClientAnnounce),
    /// Admin challenge response.
    AdminChallengeResponse(AdminChallengeResponse),
}

impl<'a> Packet<'a> {
    /// Decode packet from `src`.
    pub fn decode(src: &'a [u8]) -> Result<Option<Self>, Error> {
        if src.starts_with(ChallengeResponse::HEADER) {
            ChallengeResponse::decode(src).map(Self::ChallengeResponse)
        } else if src.starts_with(QueryServersResponse::HEADER) {
            QueryServersResponse::decode(src).map(Self::QueryServersResponse)
        } else if src.starts_with(ClientAnnounce::HEADER) {
            ClientAnnounce::decode(src).map(Self::ClientAnnounce)
        } else if src.starts_with(AdminChallengeResponse::HEADER) {
            AdminChallengeResponse::decode(src).map(Self::AdminChallengeResponse)
        } else {
            return Ok(None);
        }
        .map(Some)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn challenge_response() {
        let p = ChallengeResponse::new(0x12345678, Some(0x87654321));
        let mut buf = [0; 512];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(
            Packet::decode(&buf[..n]),
            Ok(Some(Packet::ChallengeResponse(p)))
        );
    }

    #[test]
    fn challenge_response_old() {
        let s = b"\xff\xff\xff\xffs\n\x78\x56\x34\x12";
        assert_eq!(
            ChallengeResponse::decode(s),
            Ok(ChallengeResponse::new(0x12345678, None))
        );

        let p = ChallengeResponse::new(0x12345678, None);
        let mut buf = [0; 512];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(
            Packet::decode(&buf[..n]),
            Ok(Some(Packet::ChallengeResponse(p)))
        );
    }

    #[test]
    fn query_servers_response_ipv4() {
        type Addr = SocketAddrV4;
        let servers: &[Addr] = &[
            "1.2.3.4:27001".parse().unwrap(),
            "1.2.3.4:27002".parse().unwrap(),
            "1.2.3.4:27003".parse().unwrap(),
            "1.2.3.4:27004".parse().unwrap(),
        ];
        let mut p = QueryServersResponse::new(Some(0xdeadbeef));
        let mut buf = [0; 512];
        let (n, c) = p.encode(&mut buf, servers).unwrap();
        assert_eq!(c, servers.len());
        assert_eq!(n, 12 + Addr::size() * (servers.len() + 1));
        let e = QueryServersResponse::decode(&buf[..n]).unwrap();
        assert_eq!(e.iter::<Addr>().collect::<Vec<_>>(), servers);
    }

    #[test]
    fn query_servers_response_ipv6() {
        type Addr = SocketAddrV6;
        let servers: &[Addr] = &[
            "[::1]:27001".parse().unwrap(),
            "[::2]:27002".parse().unwrap(),
            "[::3]:27003".parse().unwrap(),
            "[::4]:27004".parse().unwrap(),
        ];
        let mut p = QueryServersResponse::new(Some(0xdeadbeef));
        let mut buf = [0; 512];
        let (n, c) = p.encode(&mut buf, servers).unwrap();
        assert_eq!(c, servers.len());
        assert_eq!(n, 12 + Addr::size() * (servers.len() + 1));
        let e = QueryServersResponse::decode(&buf[..n]).unwrap();
        assert_eq!(e.iter::<Addr>().collect::<Vec<_>>(), servers);
    }

    #[test]
    fn client_announce() {
        let p = ClientAnnounce::new("1.2.3.4:12345".parse().unwrap());
        let mut buf = [0; 512];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(
            Packet::decode(&buf[..n]),
            Ok(Some(Packet::ClientAnnounce(p)))
        );
    }

    #[test]
    fn admin_challenge_response() {
        let p = AdminChallengeResponse::new(0x12345678, 0x87654321);
        let mut buf = [0; 64];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(
            Packet::decode(&buf[..n]),
            Ok(Some(Packet::AdminChallengeResponse(p)))
        );
    }
}
