// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

//! Game client packets.

use std::{fmt, net::SocketAddr};

use crate::{
    cursor::{Cursor, CursorMut},
    filter::Filter,
    net::server::Region,
    Error,
};

/// Request a list of server addresses from master servers.
#[derive(Clone, Debug, PartialEq)]
pub struct QueryServers<T> {
    /// Servers must be from the `region`.
    pub region: Region,
    /// Last received server address __(not used)__.
    pub last: SocketAddr,
    /// Select only servers that match the `filter`.
    pub filter: T,
}

impl QueryServers<()> {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"1";
}

impl<'a, T: 'a> QueryServers<T>
where
    T: TryFrom<&'a [u8], Error = Error>,
{
    /// Decode packet from `src`.
    pub fn decode(src: &'a [u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(QueryServers::HEADER)?;
        let region = cur.get_u8()?.try_into().map_err(|_| Error::InvalidRegion)?;
        let last = cur.get_cstr_as_str()?;
        let filter = match cur.get_bytes(cur.remaining())? {
            // some clients may have bug and filter will be with zero at the end
            [x @ .., 0] => x,
            x => x,
        };
        Ok(Self {
            region,
            last: last.parse().map_err(|_| Error::InvalidQueryServersLast)?,
            filter: T::try_from(filter)?,
        })
    }
}

impl<T> QueryServers<T>
where
    for<'b> &'b T: fmt::Display,
{
    /// Encode packet to `buf`.
    pub fn encode<'a>(&self, buf: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let n = CursorMut::new(buf)
            .put_bytes(QueryServers::HEADER)?
            .put_u8(self.region as u8)?
            .put_as_str(self.last)?
            .put_u8(0)?
            .put_as_str(&self.filter)?
            .put_u8(0)?
            .pos();
        Ok(&buf[..n])
    }
}

/// Request an information from a game server.
#[derive(Clone, Debug, PartialEq)]
pub struct GetServerInfo {
    /// Client protocol version.
    pub protocol: u8,
}

impl GetServerInfo {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffinfo ";

    /// Creates a new `GetServerInfo`.
    pub fn new(protocol: u8) -> Self {
        Self { protocol }
    }

    /// Decode packet from `src`.
    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        let protocol = cur
            .get_str(cur.remaining())?
            .parse()
            .map_err(|_| Error::InvalidPacket)?;
        Ok(Self { protocol })
    }

    /// Encode packet to `buf`.
    pub fn encode<'a>(&self, buf: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let n = CursorMut::new(buf)
            .put_bytes(Self::HEADER)?
            .put_as_str(self.protocol)?
            .pos();
        Ok(&buf[..n])
    }
}

/// Request a challenge number from a game server.
///
/// See [GetChallengeResponse](super::server::GetChallengeResponse).
///
/// # Note
///
/// `GetChallenge` overlaps with [GetPlayers]. Try to decode this packet before decoding
/// [GetPlayers].
#[derive(Clone, Debug, PartialEq)]
pub struct GetChallenge(());

impl GetChallenge {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffU\xff\xff\xff\xff";

    /// Creates a new `GetChallenge`.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self(())
    }

    /// Decode packet from `src`.
    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        cur.expect_empty()?;
        Ok(Self(()))
    }

    /// Encode packet to `buf`.
    pub fn encode<'a>(&self, buf: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let mut cur = CursorMut::new(buf);
        cur.put_bytes(Self::HEADER)?;
        let n = cur.pos();
        Ok(&buf[..n])
    }
}

/// Request an information from a game server.
///
/// The game server may send [GetChallengeResponse](super::server::GetChallengeResponse)
/// instead of [GetServerInfo2Response](super::server::GetServerInfo2Response). Repeat
/// this query with a challenge number taken from the challenge response.
///
/// See [GetServerInfo2Response](super::server::GetServerInfo2Response) and
/// [GetChallengeResponse](super::server::GetChallengeResponse).
#[derive(Clone, Debug, PartialEq)]
pub struct GetServerInfo2 {
    /// A challenge number from
    /// [GetChallengeResponse](super::server::GetChallengeResponse) packet.
    pub challenge: Option<u32>,
}

impl GetServerInfo2 {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffTSource Engine Query\0";

    /// Creates a new `GetServerInfo2`.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self { challenge: None }
    }

    /// Creates a new `GetServerInfo2` with challenge number.
    pub fn with_challenge(challenge: u32) -> Self {
        Self {
            challenge: Some(challenge),
        }
    }

    /// Decode packet from `src`.
    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        let mut challenge = None;
        if cur.has_remaining() {
            challenge = Some(cur.get_u32_le()?);
        }
        cur.expect_empty()?;
        Ok(Self { challenge })
    }

    /// Encode packet to `buf`.
    pub fn encode<'a>(&self, buf: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let mut cur = CursorMut::new(buf);
        cur.put_bytes(Self::HEADER)?;
        if let Some(challenge) = self.challenge {
            cur.put_u32_le(challenge)?;
        }
        let n = cur.pos();
        Ok(&buf[..n])
    }
}

/// Request player list from a game server.
///
/// See [GetPlayersResponse](super::server::GetPlayersResponse).
///
/// # Note
///
/// [GetChallenge] packet uses the same header but with a challenge number equals to `u32::MAX`.
#[derive(Clone, Debug, PartialEq)]
pub struct GetPlayers {
    challenge: u32,
}

impl GetPlayers {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffU";

    /// Create a new `GetPlayers`.
    ///
    /// Returns `None` if the challenge number equals to `u32::MAX`.
    pub fn new(challenge: u32) -> Option<Self> {
        if challenge != u32::MAX {
            Some(Self { challenge })
        } else {
            None
        }
    }

    /// A challenge number.
    pub fn challenge(&self) -> u32 {
        self.challenge
    }

    /// Decode packet from `src`.
    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        let challenge = cur.get_u32_le()?;
        if challenge == u32::MAX {
            // It is a GetChallenge packet.
            return Err(Error::InvalidPacket);
        }
        cur.expect_empty()?;
        Ok(Self { challenge })
    }

    /// Encode packet to `buf`.
    pub fn encode<'a>(&self, buf: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let mut cur = CursorMut::new(buf);
        cur.put_bytes(Self::HEADER)?;
        cur.put_u32_le(self.challenge)?;
        let n = cur.pos();
        Ok(&buf[..n])
    }
}

/// Game client packets.
#[derive(Clone, Debug, PartialEq)]
#[non_exhaustive]
pub enum Packet<'a> {
    /// Request a list of server addresses from master servers.
    QueryServers(QueryServers<Filter<'a>>),

    /// Request a challenge number from a game server.
    GetChallenge(GetChallenge),
    /// Request an information from a game server.
    GetServerInfo(GetServerInfo),
    /// Request an information from a game server.
    GetServerInfo2(GetServerInfo2),
    /// Request player list from a game server.
    GetPlayers(GetPlayers),
}

impl<'a> Packet<'a> {
    /// Decode packet from `src`.
    pub fn decode(src: &'a [u8]) -> Result<Option<Self>, Error> {
        if src.starts_with(QueryServers::HEADER) {
            QueryServers::decode(src).map(Self::QueryServers)
        } else if src.starts_with(GetChallenge::HEADER) {
            // NOTE: must be above GetPlayers
            GetChallenge::decode(src).map(Self::GetChallenge)
        } else if src.starts_with(GetServerInfo::HEADER) {
            GetServerInfo::decode(src).map(Self::GetServerInfo)
        } else if src.starts_with(GetServerInfo2::HEADER) {
            GetServerInfo2::decode(src).map(Self::GetServerInfo2)
        } else if src.starts_with(GetPlayers::HEADER) {
            GetPlayers::decode(src).map(Self::GetPlayers)
        } else {
            return Ok(None);
        }
        .map(Some)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::net::{IpAddr, Ipv4Addr};

    use crate::{
        filter::{FilterFlags, Version},
        wrappers::Str,
    };

    #[test]
    fn query_servers() {
        let p = QueryServers {
            region: Region::RestOfTheWorld,
            last: SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0),
            filter: Filter {
                gamedir: Some(Str(&b"valve"[..])),
                map: Some(Str(&b"crossfire"[..])),
                key: Some(0xdeadbeef),
                protocol: Some(49),
                clver: Some(Version::new(0, 20)),
                flags: FilterFlags::all(),
                flags_mask: FilterFlags::all(),
                ..Filter::default()
            },
        };
        let mut buf = [0; 512];
        let t = p.encode(&mut buf).unwrap();
        assert_eq!(Packet::decode(t), Ok(Some(Packet::QueryServers(p))));
    }

    #[test]
    fn query_servers_filter_bug() {
        let p = QueryServers {
            region: Region::RestOfTheWorld,
            last: SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0),
            filter: Filter {
                gamedir: None,
                protocol: Some(48),
                map: None,
                key: None,
                clver: Some(Version::new(0, 20)),
                flags: FilterFlags::empty(),
                flags_mask: FilterFlags::NAT,
                ..Filter::default()
            },
        };

        let s = b"1\xff0.0.0.0:0\x00\\protocol\\48\\clver\\0.20\\nat\\0\0";
        assert_eq!(Packet::decode(s), Ok(Some(Packet::QueryServers(p.clone()))));

        let s = b"1\xff0.0.0.0:0\x00\\protocol\\48\\clver\\0.20\\nat\\0";
        assert_eq!(Packet::decode(s), Ok(Some(Packet::QueryServers(p))));
    }

    #[test]
    fn get_challenge() {
        let mut buf = [0; 32];
        let p = GetChallenge::new();
        let t = p.encode(&mut buf).unwrap();
        assert_eq!(Packet::decode(t), Ok(Some(Packet::GetChallenge(p))));
    }

    #[test]
    fn get_server_info() {
        let p = GetServerInfo::new(49);
        let mut buf = [0; 512];
        let t = p.encode(&mut buf).unwrap();
        assert_eq!(Packet::decode(t), Ok(Some(Packet::GetServerInfo(p))));
    }

    #[test]
    fn get_server_info2() {
        let p = GetServerInfo2::new();
        let mut buf = [0; 64];
        let t = p.encode(&mut buf).unwrap();
        assert_eq!(Packet::decode(t), Ok(Some(Packet::GetServerInfo2(p))));
    }

    #[test]
    fn get_server_info2_challenge() {
        let p = GetServerInfo2::with_challenge(0xdeadbeef);
        let mut buf = [0; 64];
        let t = p.encode(&mut buf).unwrap();
        assert_eq!(Packet::decode(t), Ok(Some(Packet::GetServerInfo2(p))));
    }

    #[test]
    fn get_players() {
        let p = GetPlayers::new(0x12345678).unwrap();
        let mut buf = [0; 32];
        let t = p.encode(&mut buf).unwrap();
        assert_eq!(Packet::decode(t), Ok(Some(Packet::GetPlayers(p))));
    }
}
