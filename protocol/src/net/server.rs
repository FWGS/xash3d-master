// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

//! Game server packets.

use crate::{
    cursor::{Cursor, CursorMut, GetKeyValue, PutKeyValue},
    filter::Version,
    wrappers::Str,
    {CursorError, Error},
};

use bitflags::bitflags;

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

        // HACK: Some buggy servers send a response with a nul-byte at the end.
        if cur.as_slice().ends_with(b"\0") {
            let tail = cur.end();
            cur = Cursor::new(&tail[..tail.len() - 1]);
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

/// Response to [GetServerInfo2](super::game::GetServerInfo2) request.
#[derive(Clone, Debug, PartialEq)]
pub struct GetServerInfo2ResponseChallenge {
    /// A challenge number.
    pub challenge: u32,
}

impl GetServerInfo2ResponseChallenge {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffA";

    /// Creates a new `GetServerInfo2ResponseChallenge`.
    pub fn new(challenge: u32) -> Self {
        Self { challenge }
    }

    /// Decode packet from `src`.
    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        let challenge = cur.get_u32_le()?;
        cur.expect_empty()?;
        Ok(Self { challenge })
    }

    /// Encode packet to `buf`.
    pub fn encode<'b>(&self, buf: &'b mut [u8]) -> Result<&'b [u8], Error> {
        let n = CursorMut::new(buf)
            .put_bytes(Self::HEADER)?
            .put_u32_le(self.challenge)?
            .pos();
        Ok(&buf[..n])
    }
}

bitflags! {
    #[derive(Copy, Clone)]
    struct ServerInfoExtra: u8 {
        const APP_ID        = 0x01;
        const STEAM_ID      = 0x10;
        const KEYWORDS      = 0x20;
        const SOURCE_TV     = 0x40;
        const PORT          = 0x80;
    }
}

/// SourceTV information.
#[derive(Clone, Debug, PartialEq)]
pub struct SourceTv<'a> {
    /// Spectator port number.
    pub port: u16,
    /// Name of the spectator server.
    pub name: Str<&'a [u8]>,
}

/// Response to [GetServerInfo2](super::game::GetServerInfo2) request.
#[derive(Clone, Debug, PartialEq)]
pub struct GetServerInfo2Response<'a> {
    /// Protocol version used by the server.
    pub protocol: u8,
    /// Name of the server.
    pub host: Str<&'a [u8]>,
    /// Map the server has currently loaded.
    pub map: Str<&'a [u8]>,
    /// Name of the directory containing the game files.
    pub gamedir: Str<&'a [u8]>,
    /// Full name of the game.
    pub game: Str<&'a [u8]>,
    /// Steam AppID of the game.
    pub app_id: u64,
    /// Current number of players.
    pub players: u8,
    /// Maximum number of players.
    pub max_players: u8,
    /// Current number of bots.
    pub bots: u8,
    /// Server type.
    pub ty: ServerType,
    /// Server running on OS.
    pub os: Os,
    /// Server requires a password.
    pub password: bool,
    /// Server is protected by an anti-cheat.
    pub secure: bool,
    /// Server version.
    pub version: Str<&'a [u8]>,
    /// The server's game port number.
    pub port: Option<u16>,
    /// Server's SteamID.
    pub steam_id: Option<u64>,
    /// SourceTV port and name.
    pub source_tv: Option<SourceTv<'a>>,
    /// Tags that describe the game according to the server.
    pub keywords: Option<Str<&'a [u8]>>,
}

impl<'a> GetServerInfo2Response<'a> {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffI";

    /// Decode packet from `src`.
    pub fn decode(src: &'a [u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        let protocol = cur.get_u8()?;
        let host = cur.get_cstr()?;
        let map = cur.get_cstr()?;
        let gamedir = cur.get_cstr()?;
        let game = cur.get_cstr()?;
        let mut app_id = cur.get_u16_le()? as u64;
        let clients = cur.get_u8()?;
        let max_players = cur.get_u8()?;
        let bots = cur.get_u8()?;
        // The number of clients is a sum of players and bots.
        let players = clients.checked_sub(bots).ok_or(Error::InvalidPacket)?;
        let ty = cur.get_u8()?.into();
        let os = cur.get_u8()?.into();
        let password = cur.get_u8()? != 0;
        let secure = cur.get_u8()? != 0;

        // TODO: server info extra for The Ship: Murder Party game
        // if gamedir == Str(b"ship") {
        //     let mode = cur.get_u8()?;
        //     let witnesses = cur.get_u8()?;
        //     let duration = cur.get_u8()?;
        // }

        let version = cur.get_cstr()?;
        let mut port = None;
        let mut steam_id = None;
        let mut source_tv = None;
        let mut keywords = None;

        if cur.has_remaining() {
            let extra = ServerInfoExtra::from_bits_retain(cur.get_u8()?);

            if extra.intersects(ServerInfoExtra::PORT) {
                port = Some(cur.get_u16_le()?);
            }

            if extra.intersects(ServerInfoExtra::STEAM_ID) {
                steam_id = Some(cur.get_u64_le()?);
            }

            if extra.intersects(ServerInfoExtra::SOURCE_TV) {
                source_tv = Some(SourceTv {
                    port: cur.get_u16_le()?,
                    name: cur.get_cstr()?,
                });
            }

            if extra.intersects(ServerInfoExtra::KEYWORDS) {
                keywords = Some(cur.get_cstr()?);
            }

            if extra.intersects(ServerInfoExtra::APP_ID) {
                app_id = cur.get_u64_le()?;
            }
        }

        cur.expect_empty()?;

        Ok(Self {
            protocol,
            host,
            map,
            gamedir,
            game,
            app_id,
            players,
            max_players,
            bots,
            ty,
            os,
            password,
            secure,
            version,
            port,
            steam_id,
            source_tv,
            keywords,
        })
    }

    /// Encode packet to `buf`.
    pub fn encode<'b>(&self, buf: &'b mut [u8]) -> Result<&'b [u8], Error> {
        debug_assert!(self.players.checked_add(self.bots).is_some());

        let mut cur = CursorMut::new(buf);
        cur.put_bytes(Self::HEADER)?
            .put_u8(self.protocol)?
            .put_cstr(self.host)?
            .put_cstr(self.map)?
            .put_cstr(self.gamedir)?
            .put_cstr(self.game)?
            .put_u16_le(self.app_id as u16)?
            // The number of clients is a sum of players and bots.
            .put_u8(self.players + self.bots)?
            .put_u8(self.max_players)?
            .put_u8(self.bots)?
            .put_u8(self.ty.into())?
            .put_u8(self.os.into())?
            .put_u8(self.password as u8)?
            .put_u8(self.secure as u8)?;

        // TODO: server info extra for The Ship: Murder Party game
        // if self.gamedir == Str(b"ship") {
        //     cur.put_u8(0)?; // mode
        //     cur.put_u8(0)?; // witnesses
        //     cur.put_u8(0)?; // duration
        // }

        let mut n = cur.put_cstr(self.version)?.pos();

        let (mut head, mut tail) = cur.split(1)?;
        let mut extra = ServerInfoExtra::empty();

        if let Some(port) = self.port {
            extra.insert(ServerInfoExtra::PORT);
            tail.put_u16_le(port)?;
        }

        if let Some(steam_id) = self.steam_id {
            extra.insert(ServerInfoExtra::STEAM_ID);
            tail.put_u64_le(steam_id)?;
        }

        if let Some(source_tv) = &self.source_tv {
            extra.insert(ServerInfoExtra::SOURCE_TV);
            tail.put_u16_le(source_tv.port)?;
            tail.put_cstr(source_tv.name)?;
        }

        if let Some(keywords) = self.keywords {
            extra.insert(ServerInfoExtra::KEYWORDS);
            tail.put_cstr(keywords)?;
        }

        if u16::try_from(self.app_id).is_err() {
            extra.insert(ServerInfoExtra::APP_ID);
            tail.put_u64_le(self.app_id)?;
        }

        if !extra.is_empty() {
            head.put_u8(extra.bits())?;
            head.expect_full().expect("must be full");
            n = tail.pos();
        }

        Ok(&buf[..n])
    }
}

/// A player info.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct PlayerInfo<'a> {
    /// The player id.
    pub id: u8,
    /// The player name.
    pub name: Str<&'a [u8]>,
    /// Frags made by the player.
    pub frags: i32,
    /// The player time.
    pub time: f32,
}

impl<'a> PlayerInfo<'a> {
    /// Creates a `PlayerInfo`.
    pub fn new(id: u8, name: &'a str, frags: i32, time: f32) -> Self {
        Self {
            id,
            name: Str(name.as_bytes()),
            frags,
            time,
        }
    }

    /// Returns `true` is it is a player.
    pub fn is_player(&self) -> bool {
        self.time >= 0.0
    }

    /// Returns `true` is it is a bot.
    pub fn is_bot(&self) -> bool {
        self.time == -1.0
    }
}

/// Response to [GetPlayers](super::game::GetPlayers) request.
#[derive(Clone, Debug, PartialEq)]
pub struct GetPlayersResponse<T> {
    count: u8,
    players: T,
}

impl GetPlayersResponse<()> {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"\xff\xff\xff\xffD";
}

impl<'a> GetPlayersResponse<&'a [u8]> {
    /// Decode packet from `src`.
    pub fn decode(src: &'a [u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(GetPlayersResponse::HEADER)?;
        let count = cur.get_u8()?;
        let players = cur.end();
        Ok(Self { count, players })
    }

    /// Returns the number of players.
    pub fn players_count(&self) -> u8 {
        self.count
    }

    /// Returns an iterator over players.
    pub fn players(&self) -> impl Iterator<Item = Result<PlayerInfo<'a>, Error>> {
        let mut cur = Cursor::new(self.players);
        (0..self.count).map(move |_| {
            Ok(PlayerInfo {
                id: cur.get_u8()?,
                name: cur.get_cstr()?,
                frags: cur.get_i32_le()?,
                time: cur.get_f32_le()?,
            })
        })
    }
}

impl<'a, I> GetPlayersResponse<I>
where
    I: IntoIterator<Item = PlayerInfo<'a>>,
{
    /// Creates a new `GetPlayersResponse`.
    pub fn new(players: I) -> Self {
        Self { count: 0, players }
    }

    /// Encode packet to `buf`.
    ///
    /// # Panics
    ///
    /// This function will panic if players count is greater than 255.
    pub fn encode(self, buf: &mut [u8]) -> Result<&[u8], Error> {
        let mut cur = CursorMut::new(buf);
        cur.put_bytes(GetPlayersResponse::HEADER)?;
        let (mut head, mut tail) = cur.split(1)?;
        let mut count = 0;
        for info in self.players {
            assert!(count != 255);
            count += 1;
            tail.put_u8(info.id)?
                .put_cstr(info.name.as_ref())?
                .put_i32_le(info.frags)?
                .put_f32_le(info.time)?;
        }
        head.put_u8(count)?;
        head.expect_full().expect("must be filled with data");
        let n = tail.pos();
        Ok(&buf[..n])
    }
}

/// Game server packet.
#[derive(Clone, Debug, PartialEq)]
#[non_exhaustive]
pub enum Packet<'a> {
    /// Sended to a master server before `ServerAdd` packet.
    Challenge(Challenge),
    /// Add/update game server information on the master server.
    ServerAdd(ServerAdd<Str<&'a [u8]>>),
    /// Remove the game server from a list.
    ServerRemove,
    /// Game server information to game clients.
    GetServerInfoResponse(GetServerInfoResponse<Str<&'a [u8]>>),
    /// Game server information challenge.
    GetServerInfo2ResponseChallenge(GetServerInfo2ResponseChallenge),
    /// Game server information.
    GetServerInfo2Response(GetServerInfo2Response<'a>),
    /// Player list to game clients.
    GetPlayersResponse(GetPlayersResponse<&'a [u8]>),
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
        } else if src.starts_with(GetServerInfo2ResponseChallenge::HEADER) {
            GetServerInfo2ResponseChallenge::decode(src).map(Self::GetServerInfo2ResponseChallenge)
        } else if src.starts_with(GetServerInfo2Response::HEADER) {
            GetServerInfo2Response::decode(src).map(Self::GetServerInfo2Response)
        } else if src.starts_with(GetPlayersResponse::HEADER) {
            GetPlayersResponse::decode(src).map(Self::GetPlayersResponse)
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
    fn get_server_info2_response_challenge() {
        let p = GetServerInfo2ResponseChallenge::new(0xdeadbeef);
        let mut buf = [0; 64];
        let t = p.encode(&mut buf).unwrap();
        assert_eq!(
            Packet::decode(t),
            Ok(Some(Packet::GetServerInfo2ResponseChallenge(p)))
        );
    }

    #[test]
    fn get_server_info2_response() {
        let mut buf = [0; 512];

        let base = GetServerInfo2Response {
            protocol: 49,
            host: "Test".into(),
            map: "crossfire".into(),
            gamedir: "valve".into(),
            game: "Test server".into(),
            app_id: 1200,
            players: 4,
            max_players: 32,
            bots: 2,
            ty: ServerType::Dedicated,
            os: Os::Linux,
            password: true,
            secure: false,
            version: "0.21".into(),
            port: None,
            steam_id: None,
            source_tv: None,
            keywords: None,
        };
        assert_eq!(
            Packet::decode(base.encode(&mut buf).unwrap()),
            Ok(Some(Packet::GetServerInfo2Response(base.clone())))
        );

        let extra_port = GetServerInfo2Response {
            port: Some(27015),
            ..base.clone()
        };
        assert_eq!(
            Packet::decode(extra_port.encode(&mut buf).unwrap()),
            Ok(Some(Packet::GetServerInfo2Response(extra_port.clone())))
        );

        let extra_steam_id = GetServerInfo2Response {
            steam_id: Some(12345678),
            ..base.clone()
        };
        assert_eq!(
            Packet::decode(extra_steam_id.encode(&mut buf).unwrap()),
            Ok(Some(Packet::GetServerInfo2Response(extra_steam_id.clone())))
        );

        let extra_tv = GetServerInfo2Response {
            source_tv: Some(SourceTv {
                port: 27020,
                name: "Test Source TV".into(),
            }),
            ..base.clone()
        };
        assert_eq!(
            Packet::decode(extra_tv.encode(&mut buf).unwrap()),
            Ok(Some(Packet::GetServerInfo2Response(extra_tv.clone())))
        );

        let extra_keywords = GetServerInfo2Response {
            keywords: Some("some keywords".into()),
            ..base.clone()
        };
        assert_eq!(
            Packet::decode(extra_keywords.encode(&mut buf).unwrap()),
            Ok(Some(Packet::GetServerInfo2Response(extra_keywords.clone())))
        );

        let extra_app_id = GetServerInfo2Response {
            app_id: 12345678,
            ..base.clone()
        };
        assert_eq!(
            Packet::decode(extra_app_id.encode(&mut buf).unwrap()),
            Ok(Some(Packet::GetServerInfo2Response(extra_app_id.clone())))
        );

        let extra_all = GetServerInfo2Response {
            app_id: 12345678,
            port: Some(27016),
            steam_id: Some(87654321),
            source_tv: Some(SourceTv {
                port: 12345,
                name: "Test TV".into(),
            }),
            keywords: Some("keywords...".into()),
            ..base.clone()
        };
        assert_eq!(
            Packet::decode(extra_all.encode(&mut buf).unwrap()),
            Ok(Some(Packet::GetServerInfo2Response(extra_all.clone())))
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

    #[test]
    fn get_players_response() {
        let players = [
            PlayerInfo::new(0, "freeman", 999, 999.0),
            PlayerInfo::new(1, "crab", 0, 888.0),
        ];
        let packet = GetPlayersResponse::new(players.into_iter());
        let mut buf = [0; 512];
        let encoded = packet.encode(&mut buf).unwrap();
        let decoded = Packet::decode(encoded).unwrap().unwrap();
        let Packet::GetPlayersResponse(response) = decoded else {
            panic!();
        };
        assert_eq!(response.players_count(), 2);
        for (a, b) in players.iter().zip(response.players()) {
            assert_eq!(Ok(a), b.as_ref());
        }
    }
}
