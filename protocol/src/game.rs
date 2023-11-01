// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

//! Game client packets.

use std::fmt;
use std::net::SocketAddrV4;

use crate::cursor::{Cursor, CursorMut};
use crate::filter::Filter;
use crate::server::Region;
use crate::Error;

/// Request a list of server addresses from master servers.
#[derive(Clone, Debug, PartialEq)]
pub struct QueryServers<T> {
    /// Servers must be from the `region`.
    pub region: Region,
    /// Last received server address __(not used)__.
    pub last: SocketAddrV4,
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
        let region = cur.get_u8()?.try_into().map_err(|_| Error::InvalidPacket)?;
        let last = cur.get_cstr_as_str()?;
        let filter = match cur.get_bytes(cur.remaining())? {
            // some clients may have bug and filter will be with zero at the end
            [x @ .., 0] => x,
            x => x,
        };
        Ok(Self {
            region,
            last: last.parse().map_err(|_| Error::InvalidPacket)?,
            filter: T::try_from(filter)?,
        })
    }
}

impl<'a, T: 'a> QueryServers<T>
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
    pub fn decode(src: &'a [u8]) -> Result<Self, Error> {
        if let Ok(p) = QueryServers::decode(src) {
            return Ok(Self::QueryServers(p));
        }

        if let Ok(p) = GetServerInfo::decode(src) {
            return Ok(Self::GetServerInfo(p));
        }

        Err(Error::InvalidPacket)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::filter::{FilterFlags, Version};
    use crate::types::Str;
    use std::net::Ipv4Addr;

    #[test]
    fn query_servers() {
        let p = QueryServers {
            region: Region::RestOfTheWorld,
            last: SocketAddrV4::new(Ipv4Addr::new(0, 0, 0, 0), 0),
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
        assert_eq!(QueryServers::decode(&buf[..n]), Ok(p));
    }

    #[test]
    fn query_servers_filter_bug() {
        let p = QueryServers {
            region: Region::RestOfTheWorld,
            last: SocketAddrV4::new(Ipv4Addr::new(0, 0, 0, 0), 0),
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
        assert_eq!(QueryServers::decode(s), Ok(p.clone()));

        let s = b"1\xff0.0.0.0:0\x00\\protocol\\48\\clver\\0.20\\nat\\0";
        assert_eq!(QueryServers::decode(s), Ok(p));
    }

    #[test]
    fn get_server_info() {
        let p = GetServerInfo::new(49);
        let mut buf = [0; 512];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(GetServerInfo::decode(&buf[..n]), Ok(p));
    }
}
