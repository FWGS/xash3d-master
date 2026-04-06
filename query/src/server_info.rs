use std::fmt;

use serde::{Serialize, Serializer};
use xash3d_protocol::{color, server::GetServerInfoResponse};

use crate::{cli::Cli, color::Colored};

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

impl From<&GetServerInfoResponse<&[u8]>> for ServerInfo {
    fn from(other: &GetServerInfoResponse<&[u8]>) -> Self {
        ServerInfo {
            gamedir: String::from_utf8_lossy(other.gamedir).to_string(),
            map: String::from_utf8_lossy(other.map).to_string(),
            host: String::from_utf8_lossy(other.host).to_string(),
            protocol: other.protocol,
            numcl: other.numcl,
            maxcl: other.maxcl,
            dm: other.dm,
            team: other.team,
            coop: other.coop,
            password: other.password,
            dedicated: other.dedicated,
        }
    }
}

impl From<GetServerInfoResponse<&str>> for ServerInfo {
    fn from(other: GetServerInfoResponse<&str>) -> Self {
        Self {
            gamedir: other.gamedir.to_owned(),
            map: other.map.to_owned(),
            host: other.host.to_owned(),
            protocol: other.protocol,
            numcl: other.numcl,
            maxcl: other.maxcl,
            dm: other.dm,
            team: other.team,
            coop: other.coop,
            password: other.password,
            dedicated: other.dedicated,
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
            self.info.gamedir,
            self.info.map,
            Colored::new(&self.info.host, self.cli.force_color),
        )
    }
}

fn serialize_colored<S>(s: &str, ser: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    ser.serialize_str(color::trim_color(s).as_ref())
}
