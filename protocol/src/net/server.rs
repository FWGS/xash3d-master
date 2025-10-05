// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

//! Game server packets.

use crate::{
    cursor::{Cursor, CursorMut, GetKeyValue, PutKeyValue},
    filter::Version,
    wrappers::Str,
    {CursorError, Error},
};

#[deprecated(since = "0.2.1", note = "use server_info::Region instead")]
pub use crate::server_info::Region;

#[deprecated(since = "0.2.1", note = "use server_info::ServerType instead")]
pub use crate::server_info::ServerType;

#[deprecated(since = "0.2.1", note = "use server_info::ServerFlags instead")]
pub use crate::server_info::ServerFlags;

#[deprecated(since = "0.2.1", note = "use server_info::Os instead")]
pub use crate::server_info::Os;

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
    pub fn encode<'a>(&self, buf: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let mut cur = CursorMut::new(buf);
        cur.put_bytes(Self::HEADER)?;
        if let Some(server_challenge) = self.server_challenge {
            cur.put_u32_le(server_challenge)?;
        }
        let n = cur.pos();
        Ok(&buf[..n])
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
    /// Current number of bots on the server.
    pub bots: u8,
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
        trait Helper<'a> {
            fn get<T: GetKeyValue<'a>>(&mut self, key: &'static str) -> Result<T, Error>;
        }

        impl<'a> Helper<'a> for Cursor<'a> {
            fn get<T: GetKeyValue<'a>>(&mut self, key: &'static str) -> Result<T, Error> {
                T::get_key_value(self).map_err(|e| Error::InvalidServerValue(key, e))
            }
        }

        let mut cur = Cursor::new(src);
        cur.expect(ServerAdd::HEADER)?;

        let mut ret = Self::default();
        let mut challenge = None;
        loop {
            let key = match cur.get_key_raw() {
                Ok(s) => s,
                Err(CursorError::TableEnd) => break,
                Err(e) => Err(e)?,
            };

            match key {
                b"protocol" => ret.protocol = cur.get("protocol")?,
                b"challenge" => challenge = Some(cur.get("challenge")?),
                b"players" => ret.players = cur.get("players")?,
                b"max" => ret.max = cur.get("max")?,
                b"gamedir" => ret.gamedir = cur.get("gamedir")?,
                b"product" => cur.skip_key_value::<&[u8]>()?, // legacy key, ignore
                b"map" => ret.map = cur.get("map")?,
                b"type" => ret.server_type = cur.get("type")?,
                b"os" => ret.os = cur.get("os")?,
                b"version" => {
                    ret.version = cur
                        .get_key_value()
                        .map_err(|e| {
                            debug!("invalid server version");
                            e
                        })
                        .unwrap_or_default()
                }
                b"region" => ret.region = cur.get("region")?,
                b"bots" => {
                    ret.bots = cur.get("bots")?;
                    ret.flags.set(ServerFlags::BOTS, ret.bots != 0);
                }
                b"password" => ret.flags.set(ServerFlags::PASSWORD, cur.get("password")?),
                b"secure" => ret.flags.set(ServerFlags::SECURE, cur.get("secure")?),
                b"lan" => ret.flags.set(ServerFlags::LAN, cur.get("lan")?),
                b"nat" => ret.flags.set(ServerFlags::NAT, cur.get("nat")?),
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
            None => Err(Error::InvalidServerValue("challenge", CursorError::Expect)),
        }
    }
}

impl<T> ServerAdd<T>
where
    T: PutKeyValue,
{
    /// Encode packet to `buf`.
    pub fn encode<'a>(&self, buf: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let n = CursorMut::new(buf)
            .put_bytes(ServerAdd::HEADER)?
            .put_key("protocol", self.protocol)?
            .put_key("challenge", self.challenge)?
            .put_key("players", self.players)?
            .put_key("max", self.max)?
            .put_key("gamedir", &self.gamedir)?
            .put_key("map", &self.map)?
            .put_key("type", self.server_type)?
            .put_key("os", self.os)?
            .put_key("version", self.version)?
            .put_key("region", self.region as u8)?
            .put_key("bots", self.bots)?
            .put_key("password", self.flags.contains(ServerFlags::PASSWORD))?
            .put_key("secure", self.flags.contains(ServerFlags::SECURE))?
            .put_key("lan", self.flags.contains(ServerFlags::LAN))?
            .put_key("nat", self.flags.contains(ServerFlags::NAT))?
            .pos();
        Ok(&buf[..n])
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
    pub fn encode<'a>(&self, buf: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let n = CursorMut::new(buf).put_bytes(Self::HEADER)?.pos();
        Ok(&buf[..n])
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
    /// Server is dedicated.
    pub dedicated: bool,
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
            let s = cur.get_bytes(cur.remaining())?;
            let p = s
                .iter()
                .rev()
                .position(|c| *c == b':')
                .ok_or(Error::InvalidPacket)?;
            let msg = &s[s.len() - p..];
            return match msg {
                b" wrong version\n" => Err(Error::InvalidProtocolVersion),
                _ => Err(Error::InvalidPacket),
            };
        }

        let mut ret = Self::default();
        loop {
            let key = match cur.get_key_raw() {
                Ok(s) => s,
                Err(CursorError::TableEnd) => break,
                Err(e) => Err(e)?,
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
                b"dedicated" => ret.dedicated = cur.get_key_value()?,
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

impl<T> GetServerInfoResponse<T>
where
    T: PutKeyValue,
{
    /// Encode packet to `buf`.
    pub fn encode<'a>(&self, buf: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let n = CursorMut::new(buf)
            .put_bytes(GetServerInfoResponse::HEADER)?
            .put_key("p", self.protocol)?
            .put_key("map", &self.map)?
            .put_key("dm", self.dm)?
            .put_key("team", self.team)?
            .put_key("coop", self.coop)?
            .put_key("numcl", self.numcl)?
            .put_key("maxcl", self.maxcl)?
            .put_key("gamedir", &self.gamedir)?
            .put_key("password", self.password)?
            .put_key("dedicated", self.dedicated)?
            .put_key("host", &self.host)?
            .pos();
        Ok(&buf[..n])
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
    pub fn decode(src: &'a [u8]) -> Result<Option<Self>, Error> {
        if src.starts_with(Challenge::HEADER) {
            Challenge::decode(src).map(Self::Challenge)
        } else if src.starts_with(ServerAdd::HEADER) {
            ServerAdd::decode(src).map(Self::ServerAdd)
        } else if src.starts_with(ServerRemove::HEADER) {
            ServerRemove::decode(src).map(|_| Self::ServerRemove)
        } else if src.starts_with(GetServerInfoResponse::HEADER) {
            GetServerInfoResponse::decode(src).map(Self::GetServerInfoResponse)
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
    fn challenge() {
        let p = Challenge::new(Some(0x12345678));
        let mut buf = [0; 128];
        let t = p.encode(&mut buf).unwrap();
        assert_eq!(Packet::decode(t), Ok(Some(Packet::Challenge(p))));
    }

    #[test]
    fn challenge_old() {
        let s = b"q\xff";
        assert_eq!(
            Packet::decode(s),
            Ok(Some(Packet::Challenge(Challenge::new(None))))
        );

        let p = Challenge::new(None);
        let mut buf = [0; 128];
        let t = p.encode(&mut buf).unwrap();
        assert_eq!(t, b"q\xff");
    }

    #[test]
    fn server_add() {
        let p = ServerAdd {
            gamedir: Str(&b"valve"[..]),
            map: Str(&b"crossfire"[..]),
            version: Version::new(0, 20),
            challenge: 0x12345678,
            server_type: ServerType::Dedicated,
            os: Os::Linux,
            region: Region::RestOfTheWorld,
            protocol: 49,
            players: 4,
            max: 32,
            bots: 8,
            flags: ServerFlags::all(),
        };
        let mut buf = [0; 512];
        let t = p.encode(&mut buf).unwrap();
        assert_eq!(Packet::decode(t), Ok(Some(Packet::ServerAdd(p))));
    }

    #[test]
    fn server_remove() {
        let p = ServerRemove;
        let mut buf = [0; 64];
        let t = p.encode(&mut buf).unwrap();
        assert_eq!(Packet::decode(t), Ok(Some(Packet::ServerRemove)));
    }

    #[test]
    fn get_server_info_response() {
        let p = GetServerInfoResponse {
            protocol: 49,
            map: Str("crossfire".as_bytes()),
            dm: true,
            team: true,
            coop: true,
            numcl: 4,
            maxcl: 32,
            gamedir: Str("valve".as_bytes()),
            password: true,
            dedicated: true,
            host: Str("Test".as_bytes()),
        };
        let mut buf = [0; 512];
        let t = p.encode(&mut buf).unwrap();
        assert_eq!(
            Packet::decode(t),
            Ok(Some(Packet::GetServerInfoResponse(p)))
        );
    }

    #[test]
    fn get_server_info_response_wrong_version() {
        let s = b"\xff\xff\xff\xffinfo\nfoobar: wrong version\n";
        assert_eq!(Packet::decode(s), Err(Error::InvalidProtocolVersion));

        let s = b"\xff\xff\xff\xffinfo\nfoobar\xff: wrong version\n";
        assert_eq!(Packet::decode(s), Err(Error::InvalidProtocolVersion));
    }

    #[test]
    fn server_add_bots_is_a_number() {
        let s = b"0\n\\protocol\\48\\challenge\\4161802725\\players\\0\\max\\32\\bots\\3\\gamedir\\valve\\map\\rats_bathroom\\type\\d\\password\\0\\os\\l\\secure\\0\\lan\\0\\version\\0.19.4\\region\\255\\product\\valve\\nat\\0";
        ServerAdd::<&[u8]>::decode(s).unwrap();
    }

    #[test]
    fn server_add_legacy() {
        let s = b"0\n\\protocol\\48\\challenge\\1680337211\\players\\1\\max\\8\\bots\\0\\gamedir\\cstrike\\map\\cs_assault\\type\\d\\password\\0\\os\\l\\secure\\0\\lan\\0\\version\\0.17.1\\region\\255\\product\\cstrike\n";
        ServerAdd::<&[u8]>::decode(s).unwrap();
    }
}
