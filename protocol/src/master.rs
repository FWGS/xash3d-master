// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::net::{Ipv4Addr, SocketAddrV4};

use super::cursor::{Cursor, CursorMut};
use super::Error;

#[derive(Clone, Debug, PartialEq)]
pub struct ChallengeResponse {
    pub master_challenge: u32,
    pub server_challenge: u32,
}

impl ChallengeResponse {
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffs\n";

    pub fn new(master_challenge: u32, server_challenge: u32) -> Self {
        Self {
            master_challenge,
            server_challenge,
        }
    }

    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        let master_challenge = cur.get_u32_le()?;
        let server_challenge = cur.get_u32_le()?;
        cur.expect_empty()?;
        Ok(Self {
            master_challenge,
            server_challenge,
        })
    }

    pub fn encode<const N: usize>(&self, buf: &mut [u8; N]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf)
            .put_bytes(Self::HEADER)?
            .put_u32_le(self.master_challenge)?
            .put_u32_le(self.server_challenge)?
            .pos())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct QueryServersResponse<I> {
    inner: I,
}

impl QueryServersResponse<()> {
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xfff\n";
}

impl<'a> QueryServersResponse<&'a [u8]> {
    pub fn decode(src: &'a [u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(QueryServersResponse::HEADER)?;
        if cur.remaining() % 6 != 0 {
            return Err(Error::InvalidPacket);
        }
        let s = cur.get_bytes(cur.remaining())?;
        let inner = if s.ends_with(&[0; 6]) {
            &s[..s.len() - 6]
        } else {
            s
        };
        Ok(Self { inner })
    }

    pub fn iter(&self) -> impl 'a + Iterator<Item = SocketAddrV4> {
        let mut cur = Cursor::new(self.inner);
        (0..self.inner.len() / 6).map(move |_| {
            let ip = Ipv4Addr::from(cur.get_array().unwrap());
            let port = cur.get_u16_be().unwrap();
            SocketAddrV4::new(ip, port)
        })
    }
}

impl<I> QueryServersResponse<I>
where
    I: Iterator<Item = SocketAddrV4>,
{
    pub fn new(iter: I) -> Self {
        Self { inner: iter }
    }

    pub fn encode(&mut self, buf: &mut [u8]) -> Result<(usize, bool), Error> {
        let mut cur = CursorMut::new(buf);
        cur.put_bytes(QueryServersResponse::HEADER)?;
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

#[derive(Clone, Debug, PartialEq)]
pub struct AdminChallengeResponse {
    pub master_challenge: u32,
    pub hash_challenge: u32,
}

impl AdminChallengeResponse {
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffadminchallenge";

    pub fn new(master_challenge: u32, hash_challenge: u32) -> Self {
        Self {
            master_challenge,
            hash_challenge,
        }
    }

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

    pub fn encode(&self, buf: &mut [u8]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf)
            .put_bytes(Self::HEADER)?
            .put_u32_le(self.master_challenge)?
            .put_u32_le(self.hash_challenge)?
            .pos())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Packet<'a> {
    ChallengeResponse(ChallengeResponse),
    QueryServersResponse(QueryServersResponse<&'a [u8]>),
    AdminChallengeResponse(AdminChallengeResponse),
}

impl<'a> Packet<'a> {
    pub fn decode(src: &'a [u8]) -> Result<Self, Error> {
        if let Ok(p) = ChallengeResponse::decode(src) {
            return Ok(Self::ChallengeResponse(p));
        }

        if let Ok(p) = QueryServersResponse::decode(src) {
            return Ok(Self::QueryServersResponse(p));
        }

        if let Ok(p) = AdminChallengeResponse::decode(src) {
            return Ok(Self::AdminChallengeResponse(p));
        }

        Err(Error::InvalidPacket)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn challenge_response() {
        let p = ChallengeResponse::new(0x12345678, 0x87654321);
        let mut buf = [0; 512];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(ChallengeResponse::decode(&buf[..n]), Ok(p));
    }

    #[test]
    fn query_servers_response() {
        let servers: &[SocketAddrV4] = &[
            "1.2.3.4:27001".parse().unwrap(),
            "1.2.3.4:27002".parse().unwrap(),
            "1.2.3.4:27003".parse().unwrap(),
            "1.2.3.4:27004".parse().unwrap(),
        ];
        let mut p = QueryServersResponse::new(servers.iter().cloned());
        let mut buf = [0; 512];
        let (n, _) = p.encode(&mut buf).unwrap();
        let e = QueryServersResponse::decode(&buf[..n]).unwrap();
        assert_eq!(e.iter().collect::<Vec<_>>(), servers);
    }

    #[test]
    fn admin_challenge_response() {
        let p = AdminChallengeResponse::new(0x12345678, 0x87654321);
        let mut buf = [0; 64];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(AdminChallengeResponse::decode(&buf[..n]), Ok(p));
    }
}
