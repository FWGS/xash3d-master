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
    pub fn encode(&self, buf: &mut [u8]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf)
            .put_bytes(QueryServers::HEADER)?
            .put_u8(self.region as u8)?
            .put_as_str(self.last)?
            .put_u8(0)?
            .put_as_str(&self.filter)?
            .put_u8(0)?
            .pos())
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
    pub fn encode(&self, buf: &mut [u8]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf)
            .put_bytes(Self::HEADER)?
            .put_as_str(self.protocol)?
            .pos())
    }
}

/// Game client packets.
#[derive(Clone, Debug, PartialEq)]
pub enum Packet<'a> {
    /// Request a list of server addresses from master servers.
    QueryServers(QueryServers<Filter<'a>>),
    /// Request an information from a game server.
    GetServerInfo(GetServerInfo),
}

impl<'a> Packet<'a> {
    /// Decode packet from `src`.
    pub fn decode(src: &'a [u8]) -> Result<Option<Self>, Error> {
        if src.starts_with(QueryServers::HEADER) {
            QueryServers::decode(src).map(Self::QueryServers)
        } else if src.starts_with(GetServerInfo::HEADER) {
            GetServerInfo::decode(src).map(Self::GetServerInfo)
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
            },
        };
        let mut buf = [0; 512];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(Packet::decode(&buf[..n]), Ok(Some(Packet::QueryServers(p))));
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
            },
        };

        let s = b"1\xff0.0.0.0:0\x00\\protocol\\48\\clver\\0.20\\nat\\0\0";
        assert_eq!(Packet::decode(s), Ok(Some(Packet::QueryServers(p.clone()))));

        let s = b"1\xff0.0.0.0:0\x00\\protocol\\48\\clver\\0.20\\nat\\0";
        assert_eq!(Packet::decode(s), Ok(Some(Packet::QueryServers(p))));
    }

    #[test]
    fn get_server_info() {
        let p = GetServerInfo::new(49);
        let mut buf = [0; 512];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(
            Packet::decode(&buf[..n]),
            Ok(Some(Packet::GetServerInfo(p)))
        );
    }
}
