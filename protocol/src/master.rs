// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

//! Master server packets.

use std::net::{Ipv4Addr, SocketAddrV4};

use super::cursor::{Cursor, CursorMut};
use super::Error;

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
        if cur.remaining() % 6 != 0 {
            return Err(Error::InvalidPacket);
        }
        let s = cur.get_bytes(cur.remaining())?;

        // extra header for key sent in QueryServers packet
        let (s, key) = if s.len() >= 6 && s[0] == 0x7f && s[5] == 8 {
            (&s[6..], Some(u32::from_le_bytes([s[1], s[2], s[3], s[4]])))
        } else {
            (s, None)
        };

        let inner = if s.ends_with(&[0; 6]) {
            &s[..s.len() - 6]
        } else {
            s
        };
        Ok(Self { inner, key })
    }

    /// Iterator over game server addresses.
    pub fn iter(&self) -> impl 'a + Iterator<Item = SocketAddrV4> {
        let mut cur = Cursor::new(self.inner);
        (0..self.inner.len() / 6).map(move |_| {
            let ip = Ipv4Addr::from(cur.get_array().unwrap());
            let port = cur.get_u16_be().unwrap();
            SocketAddrV4::new(ip, port)
        })
    }

    /// Returns `true` if game server addresses list is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

impl<I> QueryServersResponse<I>
where
    I: Iterator<Item = SocketAddrV4>,
{
    /// Creates a new `QueryServersResponse`.
    pub fn new(iter: I, key: Option<u32>) -> Self {
        Self { inner: iter, key }
    }

    /// Encode packet to `buf`.
    ///
    /// If `buf` has not enougth size to hold all addresses the method must be called
    /// multiple times until the end flag equals `true`.
    ///
    /// Returns how many bytes was written in `buf` and the end flag.
    pub fn encode(&mut self, buf: &mut [u8]) -> Result<(usize, bool), Error> {
        let mut cur = CursorMut::new(buf);
        cur.put_bytes(QueryServersResponse::HEADER)?;
        if let Some(key) = self.key {
            cur.put_u8(0x7f)?;
            cur.put_u32_le(key)?;
            cur.put_u8(8)?;
        }
        let mut is_end = false;
        while cur.remaining() >= 12 {
            match self.inner.next() {
                Some(i) => {
                    cur.put_array(&i.ip().octets())?.put_u16_be(i.port())?;
                }
                None => {
                    is_end = true;
                    break;
                }
            }
        }
        Ok((cur.put_array(&[0; 6])?.pos(), is_end))
    }
}

/// Announce a game client to game server behind NAT.
#[derive(Clone, Debug, PartialEq)]
pub struct ClientAnnounce {
    /// Address of the client.
    pub addr: SocketAddrV4,
}

impl ClientAnnounce {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffc ";

    /// Creates a new `ClientAnnounce`.
    pub fn new(addr: SocketAddrV4) -> Self {
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
    fn query_servers_response() {
        let servers: &[SocketAddrV4] = &[
            "1.2.3.4:27001".parse().unwrap(),
            "1.2.3.4:27002".parse().unwrap(),
            "1.2.3.4:27003".parse().unwrap(),
            "1.2.3.4:27004".parse().unwrap(),
        ];
        let mut p = QueryServersResponse::new(servers.iter().cloned(), Some(0xdeadbeef));
        let mut buf = [0; 512];
        let (n, _) = p.encode(&mut buf).unwrap();
        let e = QueryServersResponse::decode(&buf[..n]).unwrap();
        assert_eq!(e.iter().collect::<Vec<_>>(), servers);
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
