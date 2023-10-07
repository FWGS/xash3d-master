// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::fmt;

use bitflags::bitflags;
use log::{debug, log_enabled, Level};
use thiserror::Error;

use crate::parser::{Error as ParserError, ParseValue, Parser};

#[derive(Copy, Clone, Error, Debug, PartialEq, Eq)]
pub enum Error {
    #[error("Invalid region")]
    InvalidRegion,
    #[error(transparent)]
    Parser(#[from] ParserError),
}

pub type Result<T, E = Error> = std::result::Result<T, E>;

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

impl ParseValue<'_> for Os {
    type Err = Error;

    fn parse(p: &mut Parser) -> Result<Self, Self::Err> {
        match p.parse_bytes()? {
            b"l" => Ok(Os::Linux),
            b"w" => Ok(Os::Windows),
            b"m" => Ok(Os::Mac),
            _ => Ok(Os::Unknown),
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

impl ParseValue<'_> for ServerType {
    type Err = Error;

    fn parse(p: &mut Parser) -> Result<Self, Self::Err> {
        match p.parse_bytes()? {
            b"d" => Ok(Self::Dedicated),
            b"l" => Ok(Self::Local),
            b"p" => Ok(Self::Proxy),
            _ => Ok(Self::Unknown),
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
    type Error = ();

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
            _ => Err(()),
        }
    }
}

impl ParseValue<'_> for Region {
    type Err = Error;

    fn parse(p: &mut Parser<'_>) -> Result<Self, Self::Err> {
        let value = p.parse::<u8>()?;
        Self::try_from(value).map_err(|_| Error::InvalidRegion)
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

#[derive(Clone, Debug, Default, PartialEq)]
pub struct ServerInfo<T = Box<str>> {
    pub gamedir: T,
    pub map: T,
    pub version: T,
    pub product: T,
    pub server_type: ServerType,
    pub os: Os,
    pub region: Region,
    pub protocol: u8,
    pub players: u8,
    pub max: u8,
    pub flags: ServerFlags,
}

impl<'a, T> ServerInfo<T>
where
    T: 'a + Default + ParseValue<'a, Err = ParserError>,
{
    pub fn from_bytes(src: &'a [u8]) -> Result<(Option<u32>, Self, &'a [u8]), Error> {
        let mut parser = Parser::new(src);
        let (challenge, info) = parser.parse()?;
        let tail = match parser.end() {
            [b'\n', tail @ ..] => tail,
            tail => tail,
        };
        Ok((challenge, info, tail))
    }
}

impl<'a, T> ParseValue<'a> for (Option<u32>, ServerInfo<T>)
where
    T: 'a + Default + ParseValue<'a, Err = ParserError>,
{
    type Err = Error;

    fn parse(p: &mut Parser<'a>) -> Result<Self, Self::Err> {
        let mut info = ServerInfo::default();
        let mut challenge = None;

        loop {
            let name = match p.parse_bytes() {
                Ok(s) => s,
                Err(ParserError::End) => break,
                Err(e) => return Err(e.into()),
            };

            match name {
                b"protocol" => info.protocol = p.parse()?,
                b"challenge" => challenge = Some(p.parse()?),
                b"players" => info.players = p.parse()?,
                b"max" => info.max = p.parse()?,
                b"gamedir" => info.gamedir = p.parse()?,
                b"map" => info.map = p.parse()?,
                b"type" => info.server_type = p.parse()?,
                b"os" => info.os = p.parse()?,
                b"version" => info.version = p.parse()?,
                b"region" => info.region = p.parse()?,
                b"product" => info.product = p.parse()?,
                b"bots" => info.flags.set(ServerFlags::BOTS, p.parse()?),
                b"password" => info.flags.set(ServerFlags::PASSWORD, p.parse()?),
                b"secure" => info.flags.set(ServerFlags::SECURE, p.parse()?),
                b"lan" => info.flags.set(ServerFlags::LAN, p.parse()?),
                b"nat" => info.flags.set(ServerFlags::NAT, p.parse()?),
                _ => {
                    // skip unknown fields
                    let value = p.parse_bytes()?;
                    if log_enabled!(Level::Debug) {
                        let name = String::from_utf8_lossy(name);
                        let value = String::from_utf8_lossy(value);
                        debug!("Invalid ServerInfo field \"{}\" = \"{}\"", name, value);
                    }
                }
            }
        }

        Ok((challenge, info))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    #[test]
    fn parse_os() {
        assert_eq!(parse(b"\\l\\"), Ok(Os::Linux));
        assert_eq!(parse(b"\\w\\"), Ok(Os::Windows));
        assert_eq!(parse(b"\\m\\"), Ok(Os::Mac));
        assert_eq!(parse::<Os>(b"\\u\\"), Ok(Os::Unknown));
    }

    #[test]
    fn parse_server_type() {
        use ServerType as E;

        assert_eq!(parse(b"\\d\\"), Ok(E::Dedicated));
        assert_eq!(parse(b"\\l\\"), Ok(E::Local));
        assert_eq!(parse(b"\\p\\"), Ok(E::Proxy));
        assert_eq!(parse::<E>(b"\\u\\"), Ok(E::Unknown));
    }

    #[test]
    fn parse_region() {
        assert_eq!(parse(b"\\0\\"), Ok(Region::USEastCoast));
        assert_eq!(parse(b"\\1\\"), Ok(Region::USWestCoast));
        assert_eq!(parse(b"\\2\\"), Ok(Region::SouthAmerica));
        assert_eq!(parse(b"\\3\\"), Ok(Region::Europe));
        assert_eq!(parse(b"\\4\\"), Ok(Region::Asia));
        assert_eq!(parse(b"\\5\\"), Ok(Region::Australia));
        assert_eq!(parse(b"\\6\\"), Ok(Region::MiddleEast));
        assert_eq!(parse(b"\\7\\"), Ok(Region::Africa));
        assert_eq!(parse(b"\\-1\\"), Ok(Region::RestOfTheWorld));
        assert_eq!(parse::<Region>(b"\\-2\\"), Err(Error::InvalidRegion));
        assert_eq!(
            parse::<Region>(b"\\u\\"),
            Err(Error::Parser(ParserError::InvalidInteger))
        );
    }

    #[test]
    fn parse_server_info() {
        let buf = b"\
            \\protocol\\47\
            \\challenge\\12345678\
            \\players\\16\
            \\max\\32\
            \\bots\\1\
            \\invalid_field\\field_value\
            \\gamedir\\cstrike\
            \\map\\de_dust\
            \\type\\d\
            \\password\\1\
            \\os\\l\
            \\secure\\1\
            \\lan\\1\
            \\version\\1.1.2.5\
            \\region\\-1\
            \\product\\cstrike\
            \\nat\\1\
            \ntail\
        ";

        assert_eq!(
            ServerInfo::from_bytes(&buf[..]),
            Ok((
                Some(12345678),
                ServerInfo::<&str> {
                    protocol: 47,
                    players: 16,
                    max: 32,
                    gamedir: "cstrike",
                    map: "de_dust",
                    server_type: ServerType::Dedicated,
                    os: Os::Linux,
                    version: "1.1.2.5",
                    region: Region::RestOfTheWorld,
                    product: "cstrike",
                    flags: ServerFlags::all(),
                },
                &b"tail"[..]
            ))
        );
    }
}
