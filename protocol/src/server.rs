// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

//! Game server packets.

use std::fmt;

use bitflags::bitflags;
use log::debug;

use super::cursor::{Cursor, CursorMut, GetKeyValue, PutKeyValue};
use super::filter::Version;
use super::types::Str;
use super::Error;

/// Sended to a master server before `ServerAdd` packet.
#[derive(Clone, Debug, PartialEq)]
pub struct Challenge {
    /// A number that the server must return in response.
    pub server_challenge: Option<u32>,
}

impl Challenge {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"q\xff";

    /// Creates a new `Challenge`.
    pub fn new(server_challenge: Option<u32>) -> Self {
        Self { server_challenge }
    }

    /// Decode packet from `src`.
    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        let server_challenge = if cur.remaining() == 4 {
            Some(cur.get_u32_le()?)
        } else {
            None
        };
        cur.expect_empty()?;
        Ok(Self { server_challenge })
    }

    /// Encode packet to `buf`.
    pub fn encode<const N: usize>(&self, buf: &mut [u8; N]) -> Result<usize, Error> {
        let mut cur = CursorMut::new(buf);
        cur.put_bytes(Self::HEADER)?;
        if let Some(server_challenge) = self.server_challenge {
            cur.put_u32_le(server_challenge)?;
        }
        Ok(cur.pos())
    }
}

/// The operating system on which the game server runs.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Os {
    /// GNU/Linux.
    Linux,
    /// Microsoft Windows
    Windows,
    /// Apple macOS, OS X, Mac OS X
    Mac,
    /// Unknown
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

/// Game server type.
#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(u8)]
pub enum ServerType {
    /// Dedicated server.
    Dedicated,
    /// Game client.
    Local,
    /// Spectator proxy.
    Proxy,
    /// Unknown.
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

/// The region of the world in which the server is located.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Region {
    /// US East coast.
    USEastCoast = 0x00,
    /// US West coast.
    USWestCoast = 0x01,
    /// South America.
    SouthAmerica = 0x02,
    /// Europe.
    Europe = 0x03,
    /// Asia.
    Asia = 0x04,
    /// Australia.
    Australia = 0x05,
    /// Middle East.
    MiddleEast = 0x06,
    /// Africa.
    Africa = 0x07,
    /// Rest of the world.
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
    /// Additional server flags.
    #[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
    pub struct ServerFlags: u8 {
        /// Server has bots.
        const BOTS      = 1 << 0;
        /// Server is behind a password.
        const PASSWORD  = 1 << 1;
        /// Server using anti-cheat.
        const SECURE    = 1 << 2;
        /// Server is LAN.
        const LAN       = 1 << 3;
        /// Server behind NAT.
        const NAT       = 1 << 4;
    }
}

/// Add/update game server information on the master server.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct ServerAdd<T> {
    /// Server is running the specified modification.
    ///
    /// ## Examples:
    ///
    /// * valve - Half-Life
    /// * cstrike - Counter-Strike 1.6
    /// * portal - Portal
    /// * dod - Day of Defeat
    /// * left4dead - Left 4 Dead
    pub gamedir: T,
    /// Server is running `map`.
    pub map: T,
    /// Server version.
    pub version: Version,
    /// Master server challenge number.
    pub challenge: u32,
    /// Server type.
    pub server_type: ServerType,
    /// Server is running on an operating system.
    pub os: Os,
    /// Server is located in a `region`.
    pub region: Region,
    /// Server protocol version.
    pub protocol: u8,
    /// Current number of players on the server.
    pub players: u8,
    /// Maximum number of players on the server.
    pub max: u8,
    /// See `ServerFalgs`.
    pub flags: ServerFlags,
}

impl ServerAdd<()> {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"0\n";
}

impl<'a, T> ServerAdd<T>
where
    T: 'a + Default + GetKeyValue<'a>,
{
    /// Decode packet from `src`.
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
                b"product" => { let _ = cur.get_key_value::<Str<&[u8]>>()?; }, // legacy key, ignore
                b"map" => ret.map = cur.get_key_value()?,
                b"type" => ret.server_type = cur.get_key_value()?,
                b"os" => ret.os = cur.get_key_value()?,
                b"version" => {
                    ret.version = cur
                        .get_key_value()
                        .map_err(|e| {
                            debug!("invalid server version");
                            e
                        })
                        .unwrap_or_default()
                }
                b"region" => ret.region = cur.get_key_value()?,
                b"bots" => ret.flags.set(ServerFlags::BOTS, cur.get_key_value::<u8>()? != 0),
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
    /// Encode packet to `buf`.
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
            .put_key("bots", self.flags.contains(ServerFlags::BOTS))?
            .put_key("password", self.flags.contains(ServerFlags::PASSWORD))?
            .put_key("secure", self.flags.contains(ServerFlags::SECURE))?
            .put_key("lan", self.flags.contains(ServerFlags::LAN))?
            .put_key("nat", self.flags.contains(ServerFlags::NAT))?
            .pos())
    }
}

/// Remove the game server from a list.
#[derive(Clone, Debug, PartialEq)]
pub struct ServerRemove;

impl ServerRemove {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"b\n";

    /// Decode packet from `src`.
    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        cur.expect_empty()?;
        Ok(Self)
    }

    /// Encode packet to `buf`.
    pub fn encode<const N: usize>(&self, buf: &mut [u8; N]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf).put_bytes(Self::HEADER)?.pos())
    }
}

/// Game server information to game clients.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct GetServerInfoResponse<T> {
    /// Server is running the specified modification.
    ///
    /// ## Examples:
    ///
    /// * valve - Half-Life
    /// * cstrike - Counter-Strike 1.6
    /// * portal - Portal
    /// * dod - Day of Defeat
    /// * left4dead - Left 4 Dead
    pub gamedir: T,
    /// Server is running `map`.
    pub map: T,
    /// Server title.
    pub host: T,
    /// Server protocol version.
    pub protocol: u8,
    /// Current number of players on the server.
    pub numcl: u8,
    /// Maximum number of players on the server.
    pub maxcl: u8,
    /// Server is running a deathmatch game mode.
    pub dm: bool,
    /// Players are grouped into teams.
    pub team: bool,
    /// Server is running in a co-op game mode.
    pub coop: bool,
    /// Server is behind a password.
    pub password: bool,
}

impl GetServerInfoResponse<()> {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffinfo\n";
}

impl<'a, T> GetServerInfoResponse<T>
where
    T: 'a + Default + GetKeyValue<'a>,
{
    /// Decode packet from `src`.
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
    /// Encode packet to `buf`.
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

/// Game server packet.
#[derive(Clone, Debug, PartialEq)]
pub enum Packet<'a> {
    /// Sended to a master server before `ServerAdd` packet.
    Challenge(Challenge),
    /// Add/update game server information on the master server.
    ServerAdd(ServerAdd<Str<&'a [u8]>>),
    /// Remove the game server from a list.
    ServerRemove,
    /// Game server information to game clients.
    GetServerInfoResponse(GetServerInfoResponse<Str<&'a [u8]>>),
}

impl<'a> Packet<'a> {
    /// Decode packet from `src`.
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
        let p = Challenge::new(Some(0x12345678));
        let mut buf = [0; 128];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(Challenge::decode(&buf[..n]), Ok(p));
    }

    #[test]
    fn challenge_old() {
        let s = b"q\xff";
        assert_eq!(Challenge::decode(s), Ok(Challenge::new(None)));

        let p = Challenge::new(None);
        let mut buf = [0; 128];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(&buf[..n], b"q\xff");
    }

    #[test]
    fn server_add() {
        let p = ServerAdd {
            gamedir: "valve",
            map: "crossfire",
            version: Version::new(0, 20),
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

    #[test]
    fn server_add_bots_is_a_number() {
        let s = b"0\n\\protocol\\48\\challenge\\4161802725\\players\\0\\max\\32\\bots\\3\\gamedir\\valve\\map\\rats_bathroom\\type\\d\\password\\0\\os\\l\\secure\\0\\lan\\0\\version\\0.19.4\\region\\255\\product\\valve\\nat\\0";
        ServerAdd::<&[u8]>::decode(s).unwrap();
    }
}
