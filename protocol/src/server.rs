// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::fmt;

use bitflags::bitflags;
use log::debug;

use super::cursor::{Cursor, CursorMut, GetKeyValue, PutKeyValue};
use super::filter::Version;
use super::types::Str;
use super::Error;

#[derive(Clone, Debug, PartialEq)]
pub struct Challenge {
    pub server_challenge: u32,
}

impl Challenge {
    pub const HEADER: &'static [u8] = b"q\xff";

    pub fn new(server_challenge: u32) -> Self {
        Self { server_challenge }
    }

    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        let server_challenge = cur.get_u32_le()?;
        cur.expect_empty()?;
        Ok(Self { server_challenge })
    }

    pub fn encode<const N: usize>(&self, buf: &mut [u8; N]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf)
            .put_bytes(Self::HEADER)?
            .put_u32_le(self.server_challenge)?
            .pos())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Os {
    Linux,
    Windows,
    Mac,
    Unknown,
}

impl Default for Os {
    fn default() -> Os {
        Os::Unknown
    }
}

impl TryFrom<&[u8]> for Os {
    type Error = Error;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        match value {
            b"l" => Ok(Os::Linux),
            b"w" => Ok(Os::Windows),
            b"m" => Ok(Os::Mac),
            _ => Ok(Os::Unknown),
        }
    }
}

impl GetKeyValue<'_> for Os {
    fn get_key_value(cur: &mut Cursor) -> Result<Self, Error> {
        cur.get_key_value_raw()?.try_into()
    }
}

impl PutKeyValue for Os {
    fn put_key_value<'a, 'b>(
        &self,
        cur: &'b mut CursorMut<'a>,
    ) -> Result<&'b mut CursorMut<'a>, Error> {
        match self {
            Self::Linux => cur.put_str("l"),
            Self::Windows => cur.put_str("w"),
            Self::Mac => cur.put_str("m"),
            Self::Unknown => cur.put_str("?"),
        }
    }
}

impl fmt::Display for Os {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            Os::Linux => "Linux",
            Os::Windows => "Windows",
            Os::Mac => "Mac",
            Os::Unknown => "Unknown",
        };
        write!(fmt, "{}", s)
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(u8)]
pub enum ServerType {
    Dedicated,
    Local,
    Proxy,
    Unknown,
}

impl Default for ServerType {
    fn default() -> Self {
        Self::Unknown
    }
}

impl TryFrom<&[u8]> for ServerType {
    type Error = Error;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        match value {
            b"d" => Ok(Self::Dedicated),
            b"l" => Ok(Self::Local),
            b"p" => Ok(Self::Proxy),
            _ => Ok(Self::Unknown),
        }
    }
}

impl GetKeyValue<'_> for ServerType {
    fn get_key_value(cur: &mut Cursor) -> Result<Self, Error> {
        cur.get_key_value_raw()?.try_into()
    }
}

impl PutKeyValue for ServerType {
    fn put_key_value<'a, 'b>(
        &self,
        cur: &'b mut CursorMut<'a>,
    ) -> Result<&'b mut CursorMut<'a>, Error> {
        match self {
            Self::Dedicated => cur.put_str("d"),
            Self::Local => cur.put_str("l"),
            Self::Proxy => cur.put_str("p"),
            Self::Unknown => cur.put_str("?"),
        }
    }
}

impl fmt::Display for ServerType {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        use ServerType as E;

        let s = match self {
            E::Dedicated => "dedicated",
            E::Local => "local",
            E::Proxy => "proxy",
            E::Unknown => "unknown",
        };

        write!(fmt, "{}", s)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Region {
    USEastCoast = 0x00,
    USWestCoast = 0x01,
    SouthAmerica = 0x02,
    Europe = 0x03,
    Asia = 0x04,
    Australia = 0x05,
    MiddleEast = 0x06,
    Africa = 0x07,
    RestOfTheWorld = 0xff,
}

impl Default for Region {
    fn default() -> Self {
        Self::RestOfTheWorld
    }
}

impl TryFrom<u8> for Region {
    type Error = Error;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0x00 => Ok(Region::USEastCoast),
            0x01 => Ok(Region::USWestCoast),
            0x02 => Ok(Region::SouthAmerica),
            0x03 => Ok(Region::Europe),
            0x04 => Ok(Region::Asia),
            0x05 => Ok(Region::Australia),
            0x06 => Ok(Region::MiddleEast),
            0x07 => Ok(Region::Africa),
            0xff => Ok(Region::RestOfTheWorld),
            _ => Err(Error::InvalidPacket),
        }
    }
}

impl GetKeyValue<'_> for Region {
    fn get_key_value(cur: &mut Cursor) -> Result<Self, Error> {
        cur.get_key_value::<u8>()?.try_into()
    }
}

bitflags! {
    #[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
    pub struct ServerFlags: u8 {
        const BOTS      = 1 << 0;
        const PASSWORD  = 1 << 1;
        const SECURE    = 1 << 2;
        const LAN       = 1 << 3;
        const NAT       = 1 << 4;
    }
}

#[derive(Clone, Debug, PartialEq, Default)]
pub struct ServerAdd<T> {
    pub gamedir: T,
    pub map: T,
    pub version: Version,
    pub product: T,
    pub challenge: u32,
    pub server_type: ServerType,
    pub os: Os,
    pub region: Region,
    pub protocol: u8,
    pub players: u8,
    pub max: u8,
    pub flags: ServerFlags,
}

impl ServerAdd<()> {
    pub const HEADER: &'static [u8] = b"0\n";
}

impl<'a, T> ServerAdd<T>
where
    T: 'a + Default + GetKeyValue<'a>,
{
    pub fn decode(src: &'a [u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(ServerAdd::HEADER)?;

        let mut ret = Self::default();
        let mut challenge = None;
        loop {
            let key = match cur.get_key_raw() {
                Ok(s) => s,
                Err(Error::UnexpectedEnd) => break,
                Err(e) => return Err(e),
            };

            match key {
                b"protocol" => ret.protocol = cur.get_key_value()?,
                b"challenge" => challenge = Some(cur.get_key_value()?),
                b"players" => ret.players = cur.get_key_value()?,
                b"max" => ret.max = cur.get_key_value()?,
                b"gamedir" => ret.gamedir = cur.get_key_value()?,
                b"map" => ret.map = cur.get_key_value()?,
                b"type" => ret.server_type = cur.get_key_value()?,
                b"os" => ret.os = cur.get_key_value()?,
                b"version" => ret.version = cur.get_key_value()?,
                b"region" => ret.region = cur.get_key_value()?,
                b"product" => ret.product = cur.get_key_value()?,
                b"bots" => ret.flags.set(ServerFlags::BOTS, cur.get_key_value()?),
                b"password" => ret.flags.set(ServerFlags::PASSWORD, cur.get_key_value()?),
                b"secure" => ret.flags.set(ServerFlags::SECURE, cur.get_key_value()?),
                b"lan" => ret.flags.set(ServerFlags::LAN, cur.get_key_value()?),
                b"nat" => ret.flags.set(ServerFlags::NAT, cur.get_key_value()?),
                _ => {
                    // skip unknown fields
                    let value = cur.get_key_value::<Str<&[u8]>>()?;
                    debug!("Invalid ServerInfo field \"{}\" = \"{}\"", Str(key), value);
                }
            }
        }

        match challenge {
            Some(c) => {
                ret.challenge = c;
                Ok(ret)
            }
            None => Err(Error::InvalidPacket),
        }
    }
}

impl<T> ServerAdd<T>
where
    T: PutKeyValue + Clone,
{
    pub fn encode(&self, buf: &mut [u8]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf)
            .put_bytes(ServerAdd::HEADER)?
            .put_key("protocol", self.protocol)?
            .put_key("challenge", self.challenge)?
            .put_key("players", self.players)?
            .put_key("max", self.max)?
            .put_key("gamedir", self.gamedir.clone())?
            .put_key("map", self.map.clone())?
            .put_key("type", self.server_type)?
            .put_key("os", self.os)?
            .put_key("version", self.version)?
            .put_key("region", self.region as u8)?
            .put_key("product", self.product.clone())?
            .put_key("bots", self.flags.contains(ServerFlags::BOTS))?
            .put_key("password", self.flags.contains(ServerFlags::PASSWORD))?
            .put_key("secure", self.flags.contains(ServerFlags::SECURE))?
            .put_key("lan", self.flags.contains(ServerFlags::LAN))?
            .put_key("nat", self.flags.contains(ServerFlags::NAT))?
            .pos())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ServerRemove;

impl ServerRemove {
    pub const HEADER: &'static [u8] = b"b\n";

    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        cur.expect_empty()?;
        Ok(Self)
    }

    pub fn encode<const N: usize>(&self, buf: &mut [u8; N]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf).put_bytes(Self::HEADER)?.pos())
    }
}

#[derive(Clone, Debug, PartialEq, Default)]
pub struct GetServerInfoResponse<T> {
    pub gamedir: T,
    pub map: T,
    pub host: T,
    pub protocol: u8,
    pub numcl: u8,
    pub maxcl: u8,
    pub dm: bool,
    pub team: bool,
    pub coop: bool,
    pub password: bool,
}

impl GetServerInfoResponse<()> {
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffinfo\n";
}

impl<'a, T> GetServerInfoResponse<T>
where
    T: 'a + Default + GetKeyValue<'a>,
{
    pub fn decode(src: &'a [u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(GetServerInfoResponse::HEADER)?;

        if !cur.as_slice().starts_with(b"\\") {
            let s = cur.get_str(cur.remaining())?;
            let p = s.rfind(':').ok_or(Error::InvalidPacket)?;
            let msg = &s[p + 1..];
            match msg.trim() {
                "wrong version" => return Err(Error::InvalidProtocolVersion),
                _ => return Err(Error::InvalidPacket),
            }
        }

        let mut ret = Self::default();
        loop {
            let key = match cur.get_key_raw() {
                Ok(s) => s,
                Err(Error::UnexpectedEnd) => break,
                Err(e) => return Err(e),
            };

            match key {
                b"p" => ret.protocol = cur.get_key_value()?,
                b"map" => ret.map = cur.get_key_value()?,
                b"dm" => ret.dm = cur.get_key_value()?,
                b"team" => ret.team = cur.get_key_value()?,
                b"coop" => ret.coop = cur.get_key_value()?,
                b"numcl" => ret.numcl = cur.get_key_value()?,
                b"maxcl" => ret.maxcl = cur.get_key_value()?,
                b"gamedir" => ret.gamedir = cur.get_key_value()?,
                b"password" => ret.password = cur.get_key_value()?,
                b"host" => ret.host = cur.get_key_value()?,
                _ => {
                    // skip unknown fields
                    let value = cur.get_key_value::<Str<&[u8]>>()?;
                    debug!(
                        "Invalid GetServerInfo field \"{}\" = \"{}\"",
                        Str(key),
                        value
                    );
                }
            }
        }

        Ok(ret)
    }
}

impl<'a> GetServerInfoResponse<&'a str> {
    pub fn encode(&self, buf: &mut [u8]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf)
            .put_bytes(GetServerInfoResponse::HEADER)?
            .put_key("p", self.protocol)?
            .put_key("map", self.map)?
            .put_key("dm", self.dm)?
            .put_key("team", self.team)?
            .put_key("coop", self.coop)?
            .put_key("numcl", self.numcl)?
            .put_key("maxcl", self.maxcl)?
            .put_key("gamedir", self.gamedir)?
            .put_key("password", self.password)?
            .put_key("host", self.host)?
            .pos())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Packet<'a> {
    Challenge(Challenge),
    ServerAdd(ServerAdd<Str<&'a [u8]>>),
    ServerRemove,
    GetServerInfoResponse(GetServerInfoResponse<Str<&'a [u8]>>),
}

impl<'a> Packet<'a> {
    pub fn decode(src: &'a [u8]) -> Result<Self, Error> {
        if let Ok(p) = Challenge::decode(src) {
            return Ok(Self::Challenge(p));
        }

        if let Ok(p) = ServerAdd::decode(src) {
            return Ok(Self::ServerAdd(p));
        }

        if ServerRemove::decode(src).is_ok() {
            return Ok(Self::ServerRemove);
        }

        if let Ok(p) = GetServerInfoResponse::decode(src) {
            return Ok(Self::GetServerInfoResponse(p));
        }

        Err(Error::InvalidPacket)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn challenge() {
        let p = Challenge::new(0x12345678);
        let mut buf = [0; 128];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(Challenge::decode(&buf[..n]), Ok(p));
    }

    #[test]
    fn server_add() {
        let p = ServerAdd {
            gamedir: "valve",
            map: "crossfire",
            version: Version::new(0, 20),
            product: "foobar",
            challenge: 0x12345678,
            server_type: ServerType::Dedicated,
            os: Os::Linux,
            region: Region::RestOfTheWorld,
            protocol: 49,
            players: 4,
            max: 32,
            flags: ServerFlags::all(),
        };
        let mut buf = [0; 512];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(ServerAdd::decode(&buf[..n]), Ok(p));
    }

    #[test]
    fn server_remove() {
        let p = ServerRemove;
        let mut buf = [0; 64];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(ServerRemove::decode(&buf[..n]), Ok(p));
    }

    #[test]
    fn get_server_info_response() {
        let p = GetServerInfoResponse {
            protocol: 49,
            map: "crossfire",
            dm: true,
            team: true,
            coop: true,
            numcl: 4,
            maxcl: 32,
            gamedir: "valve",
            password: true,
            host: "Test",
        };
        let mut buf = [0; 512];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(GetServerInfoResponse::decode(&buf[..n]), Ok(p));
    }
}
