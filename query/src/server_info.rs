use std::{
    fmt,
    ops::{Deref, DerefMut},
};

use serde::{Serialize, Serializer};
use xash3d_protocol::color;

use crate::{cli::Cli, color::Colored};

#[derive(Clone, Debug, Serialize)]
pub struct PlayerInfo {
    pub id: u8,
    pub name: String,
    pub frags: i32,
    pub time: f32,
}

impl From<xash3d_observer::event::PlayerInfo<'_>> for PlayerInfo {
    fn from(info: xash3d_observer::event::PlayerInfo) -> Self {
        Self {
            id: info.id,
            name: String::from_utf8_lossy(info.name.0).to_string(),
            frags: info.frags,
            time: info.time,
        }
    }
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct Players {
    players: Vec<PlayerInfo>,
}

impl Deref for Players {
    type Target = Vec<PlayerInfo>;

    fn deref(&self) -> &Self::Target {
        &self.players
    }
}

impl DerefMut for Players {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.players
    }
}

impl From<xash3d_observer::event::ServerPlayers<'_>> for Players {
    fn from(value: xash3d_observer::event::ServerPlayers<'_>) -> Self {
        let mut players = Vec::with_capacity(value.len());
        for i in value.iter().filter_map(|i| i.ok()) {
            players.push(i.into());
        }
        Self { players }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct ServerInfo {
    pub gamedir: String,
    pub map: String,
    #[serde(serialize_with = "serialize_colored")]
    pub host: String,
    pub protocol: u8,
    pub numcl: u8,
    pub maxcl: u8,
    pub dm: bool,
    pub team: bool,
    pub coop: bool,
    pub password: bool,
    pub dedicated: bool,
}

impl ServerInfo {
    pub fn printer<'a>(&'a self, cli: &'a Cli) -> ServerInfoPrinter<'a> {
        ServerInfoPrinter { info: self, cli }
    }
}

impl From<&xash3d_observer::event::ServerInfo<'_>> for ServerInfo {
    fn from(other: &xash3d_observer::event::ServerInfo<'_>) -> Self {
        ServerInfo {
            gamedir: String::from_utf8_lossy(other.gamedir()).to_string(),
            map: String::from_utf8_lossy(other.map()).to_string(),
            host: String::from_utf8_lossy(other.host()).to_string(),
            protocol: other.protocol(),
            numcl: other.clients_count(),
            maxcl: other.clients_max(),
            dm: other.is_deathmatch(),
            team: other.has_teams(),
            coop: other.is_coop(),
            password: other.has_password(),
            dedicated: other.is_dedicated(),
        }
    }
}

pub struct ServerInfoPrinter<'a> {
    cli: &'a Cli,
    info: &'a ServerInfo,
}

impl fmt::Display for ServerInfoPrinter<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fn flag(c: char, cond: bool) -> char {
            if cond {
                c
            } else {
                '-'
            }
        }

        write!(
            fmt,
            "{}{}{}{}{} {:>2}/{:<2} {:8} {:18} \"{}\"",
            flag('d', self.info.dm),
            flag('t', self.info.team),
            flag('c', self.info.coop),
            flag('p', self.info.password),
            flag('D', self.info.dedicated),
            self.info.numcl,
            self.info.maxcl,
            self.info.gamedir.trim(),
            self.info.map.trim(),
            Colored::new(self.info.host.trim(), self.cli.colored_output()),
        )
    }
}

fn serialize_colored<S>(s: &str, ser: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    ser.serialize_str(color::trim_color(s).as_ref())
}
