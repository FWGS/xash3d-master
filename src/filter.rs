// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

//! Server query filter
//!
//! # Supported filters:
//!
//! | Filter    | Type | Description                    | Examples |
//! | --------- | ---- | ------------------------------ | -------- |
//! | map       | str  | Map name                       | `crossfire`, `de_dust` |
//! | gamedir   | str  | Game directory                 | `valve`, `cstrike` |
//! | dedicated | bool | Server running dedicated       | `0`, `1` |
//! | lan       | bool | Server is LAN                  | `0`, `1` |
//! | nat       | bool | Server behind NAT              | `0`, `1` |
//! | noplayers | bool | Server is empty                | `0`, `1` |
//! | empty     | bool | Server is not empty            | `0`, `1` |
//! | full      | bool | Server is not full             | `0`, `1` |
//! | password  | bool | Server is password prodected   | `0`, `1` |
//! | secure    | bool | Server using anti-cheat        | `0`, `1` |
//! | bots      | bool | Server has bots                | `0`, `1` |
//!
//! # Examples:
//!
//! Filter `\gamedir\valve\full\1\bots\0\password\0` will select server if:
//!
//! * It is Half-Life server
//! * Is not full
//! * Do not have bots
//! * Is not protected by a password

use std::net::SocketAddrV4;

use bitflags::bitflags;
use log::{debug, log_enabled, Level};

use crate::parser::{Error as ParserError, ParseValue, Parser};
use crate::server::Server;
use crate::server_info::{ServerFlags, ServerInfo, ServerType};

bitflags! {
    #[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
    pub struct FilterFlags: u16 {
        /// Servers running dedicated
        const DEDICATED     = 1 << 0;
        /// Servers using anti-cheat technology (VAC, but potentially others as well)
        const SECURE        = 1 << 1;
        /// Servers that are not password protected
        const PASSWORD      = 1 << 2;
        /// Servers that are not empty
        const NOT_EMPTY     = 1 << 3;
        /// Servers that are not full
        const FULL          = 1 << 4;
        /// Servers that are empty
        const NOPLAYERS     = 1 << 5;
        /// Servers that are behind NAT
        const NAT           = 1 << 6;
        /// Servers that are LAN
        const LAN           = 1 << 7;
        /// Servers that has bots
        const BOTS          = 1 << 8;
    }
}

impl<T> From<&ServerInfo<T>> for FilterFlags {
    fn from(info: &ServerInfo<T>) -> Self {
        let mut flags = Self::empty();

        flags.set(Self::DEDICATED, info.server_type == ServerType::Dedicated);
        flags.set(Self::SECURE, info.flags.contains(ServerFlags::SECURE));
        flags.set(Self::PASSWORD, info.flags.contains(ServerFlags::PASSWORD));
        flags.set(Self::NOT_EMPTY, info.players > 0); // XXX: and not full?
        flags.set(Self::FULL, info.players >= info.max);
        flags.set(Self::NOPLAYERS, info.players == 0);
        flags.set(Self::NAT, info.flags.contains(ServerFlags::NAT));
        flags.set(Self::LAN, info.flags.contains(ServerFlags::LAN));
        flags.set(Self::BOTS, info.flags.contains(ServerFlags::BOTS));

        flags
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Filter<'a> {
    /// Servers running the specified modification (ex. cstrike)
    pub gamedir: Option<&'a str>,
    /// Servers running the specified map (ex. cs_italy)
    pub map: Option<&'a str>,
    /// Servers with their hostname matching \[hostname\] (can use * as a wildcard)
    pub name_match: Option<&'a str>,
    /// Servers running version \[version\] (can use * as a wildcard)
    pub version_match: Option<&'a str>,
    /// Return only servers on the specified IP address (port supported and optional)
    pub gameaddr: Option<SocketAddrV4>,
    /// Client version.
    pub clver: Option<&'a str>,

    pub flags: FilterFlags,
    pub flags_mask: FilterFlags,
}

impl Filter<'_> {
    pub fn insert_flag(&mut self, flag: FilterFlags, value: bool) {
        self.flags.set(flag, value);
        self.flags_mask.insert(flag);
    }

    pub fn matches(&self, addr: SocketAddrV4, server: &Server) -> bool {
        if (server.flags & self.flags_mask) != self.flags {
            return false;
        }
        if self.gamedir.map_or(false, |i| &*server.gamedir != i) {
            return false;
        }
        if self.map.map_or(false, |i| &*server.map != i) {
            return false;
        }
        if self.version_match.map_or(false, |i| &*server.version != i) {
            return false;
        }
        if let Some(a) = self.gameaddr {
            if addr.ip() != a.ip() {
                return false;
            }
            if a.port() != 0 && addr.port() != a.port() {
                return false;
            }
        }
        true
    }
}

impl<'a> Filter<'a> {
    pub fn from_bytes(src: &'a [u8]) -> Result<Self, ParserError> {
        let mut parser = Parser::new(src);
        let filter = parser.parse()?;
        Ok(filter)
    }
}

impl<'a> ParseValue<'a> for Filter<'a> {
    type Err = ParserError;

    fn parse(p: &mut Parser<'a>) -> Result<Self, Self::Err> {
        let mut filter = Self::default();

        loop {
            let name = match p.parse_bytes() {
                Ok(s) => s,
                Err(ParserError::End) => break,
                Err(e) => return Err(e),
            };

            match name {
                b"dedicated" => filter.insert_flag(FilterFlags::DEDICATED, p.parse()?),
                b"secure" => filter.insert_flag(FilterFlags::SECURE, p.parse()?),
                b"gamedir" => filter.gamedir = Some(p.parse()?),
                b"map" => filter.map = Some(p.parse()?),
                b"empty" => filter.insert_flag(FilterFlags::NOT_EMPTY, p.parse()?),
                b"full" => filter.insert_flag(FilterFlags::FULL, p.parse()?),
                b"password" => filter.insert_flag(FilterFlags::PASSWORD, p.parse()?),
                b"noplayers" => filter.insert_flag(FilterFlags::NOPLAYERS, p.parse()?),
                b"name_match" => filter.name_match = Some(p.parse()?),
                b"version_match" => filter.version_match = Some(p.parse()?),
                b"gameaddr" => {
                    let s = p.parse::<&str>()?;
                    if let Ok(addr) = s.parse() {
                        filter.gameaddr = Some(addr);
                    } else if let Ok(ip) = s.parse() {
                        filter.gameaddr = Some(SocketAddrV4::new(ip, 0));
                    }
                }
                b"clver" => filter.clver = Some(p.parse()?),
                b"nat" => filter.insert_flag(FilterFlags::NAT, p.parse()?),
                b"lan" => filter.insert_flag(FilterFlags::LAN, p.parse()?),
                b"bots" => filter.insert_flag(FilterFlags::BOTS, p.parse()?),
                _ => {
                    // skip unknown fields
                    let value = p.parse_bytes()?;
                    if log_enabled!(Level::Debug) {
                        let name = String::from_utf8_lossy(name);
                        let value = String::from_utf8_lossy(value);
                        debug!("Invalid Filter field \"{}\" = \"{}\"", name, value);
                    }
                }
            }
        }

        Ok(filter)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::net::Ipv4Addr;

    macro_rules! tests {
        ($($name:ident$(($($predefined_f:ident: $predefined_v:expr),+ $(,)?))? {
            $($src:expr => {
                $($field:ident: $value:expr),* $(,)?
            })+
        })+) => {
            $(#[test]
            fn $name() {
                let predefined = Filter {
                    $($($predefined_f: $predefined_v,)+)?
                    .. Filter::default()
                };
                $(assert_eq!(
                    Filter::from_bytes($src),
                    Ok(Filter {
                        $($field: $value,)*
                        ..predefined
                    })
                );)+
            })+
        };
    }

    tests! {
        parse_gamedir {
            b"\\gamedir\\valve" => {
                gamedir: Some("valve"),
            }
        }
        parse_map {
            b"\\map\\crossfire" => {
                map: Some("crossfire"),
            }
        }
        parse_name_match {
            b"\\name_match\\localhost" => {
                name_match: Some("localhost"),
            }
        }
        parse_version_match {
            b"\\version_match\\1.2.3.4" => {
                version_match: Some("1.2.3.4"),
            }
        }
        parse_gameaddr {
            b"\\gameaddr\\192.168.1.100" => {
                gameaddr: Some(SocketAddrV4::new(Ipv4Addr::new(192, 168, 1, 100), 0)),
            }
            b"\\gameaddr\\192.168.1.100:27015" => {
                gameaddr: Some(SocketAddrV4::new(Ipv4Addr::new(192, 168, 1, 100), 27015)),
            }
        }
        parse_clver {
            b"\\clver\\0.20" => {
                clver: Some("0.20"),
            }
        }
        parse_dedicated(flags_mask: FilterFlags::DEDICATED) {
            b"\\dedicated\\0" => {}
            b"\\dedicated\\1" => {
                flags: FilterFlags::DEDICATED,
            }
        }
        parse_secure(flags_mask: FilterFlags::SECURE) {
            b"\\secure\\0" => {}
            b"\\secure\\1" => {
                flags: FilterFlags::SECURE,
            }
        }
        parse_password(flags_mask: FilterFlags::PASSWORD) {
            b"\\password\\0" => {}
            b"\\password\\1" => {
                flags: FilterFlags::PASSWORD,
            }
        }
        parse_empty(flags_mask: FilterFlags::NOT_EMPTY) {
            b"\\empty\\0" => {}
            b"\\empty\\1" => {
                flags: FilterFlags::NOT_EMPTY,
            }
        }
        parse_full(flags_mask: FilterFlags::FULL) {
            b"\\full\\0" => {}
            b"\\full\\1" => {
                flags: FilterFlags::FULL,
            }
        }
        parse_noplayers(flags_mask: FilterFlags::NOPLAYERS) {
            b"\\noplayers\\0" => {}
            b"\\noplayers\\1" => {
                flags: FilterFlags::NOPLAYERS,
            }
        }
        parse_nat(flags_mask: FilterFlags::NAT) {
            b"\\nat\\0" => {}
            b"\\nat\\1" => {
                flags: FilterFlags::NAT,
            }
        }
        parse_lan(flags_mask: FilterFlags::LAN) {
            b"\\lan\\0" => {}
            b"\\lan\\1" => {
                flags: FilterFlags::LAN,
            }
        }
        parse_bots(flags_mask: FilterFlags::BOTS) {
            b"\\bots\\0" => {}
            b"\\bots\\1" => {
                flags: FilterFlags::BOTS,
            }
        }

        parse_all {
            b"\
              \\bots\\1\
              \\clver\\0.20\
              \\dedicated\\1\
              \\empty\\1\
              \\full\\1\
              \\gameaddr\\192.168.1.100\
              \\gamedir\\valve\
              \\lan\\1\
              \\map\\crossfire\
              \\name_match\\localhost\
              \\nat\\1\
              \\noplayers\\1\
              \\password\\1\
              \\secure\\1\
              \\version_match\\1.2.3.4\
            " => {
                gamedir: Some("valve"),
                map: Some("crossfire"),
                name_match: Some("localhost"),
                version_match: Some("1.2.3.4"),
                gameaddr: Some(SocketAddrV4::new(Ipv4Addr::new(192, 168, 1, 100), 0)),
                clver: Some("0.20"),
                flags: FilterFlags::all(),
                flags_mask: FilterFlags::all(),
            }
        }
    }

    macro_rules! servers {
        ($($addr:expr => $info:expr $(=> $func:expr)?)+) => (
            [$({
                let addr = $addr.parse::<SocketAddrV4>().unwrap();
                let (_, info, _) = ServerInfo::<&str>::from_bytes($info).unwrap();
                let server = Server::new(&info);
                $(
                    let mut server = server;
                    let func: fn(&mut Server) = $func;
                    func(&mut server);
                )?
                (addr, server)
            }),+]
        );
    }

    macro_rules! matches {
        ($servers:expr, $filter:expr$(, $expected:expr)*) => (
            let servers = &$servers;
            let filter = Filter::from_bytes($filter).unwrap();
            let iter = servers
                .iter()
                .enumerate()
                .filter(|(_, (addr, server))| filter.matches(*addr, &server))
                .map(|(i, _)| i);
            assert_eq!(iter.collect::<Vec<_>>(), [$($expected),*])
        );
    }

    #[test]
    fn match_dedicated() {
        let s = servers! {
            "0.0.0.0:0" => b""
            "0.0.0.0:0" => b"\\type\\d"
            "0.0.0.0:0" => b"\\type\\p"
            "0.0.0.0:0" => b"\\type\\l"
        };
        matches!(s, b"", 0, 1, 2, 3);
        matches!(s, b"\\dedicated\\0", 0, 2, 3);
        matches!(s, b"\\dedicated\\1", 1);
    }

    #[test]
    fn match_password() {
        let s = servers! {
            "0.0.0.0:0" => b""
            "0.0.0.0:0" => b"\\password\\0"
            "0.0.0.0:0" => b"\\password\\1"
        };
        matches!(s, b"", 0, 1, 2);
        matches!(s, b"\\password\\0", 0, 1);
        matches!(s, b"\\password\\1", 2);
    }

    #[test]
    fn match_not_empty() {
        let servers = servers! {
            "0.0.0.0:0" => b"\\players\\0\\max\\8"
            "0.0.0.0:0" => b"\\players\\4\\max\\8"
            "0.0.0.0:0" => b"\\players\\8\\max\\8"
        };
        matches!(servers, b"", 0, 1, 2);
        matches!(servers, b"\\empty\\0", 0);
        matches!(servers, b"\\empty\\1", 1, 2);
    }

    #[test]
    fn match_full() {
        let servers = servers! {
            "0.0.0.0:0" => b"\\players\\0\\max\\8"
            "0.0.0.0:0" => b"\\players\\4\\max\\8"
            "0.0.0.0:0" => b"\\players\\8\\max\\8"
        };
        matches!(servers, b"", 0, 1, 2);
        matches!(servers, b"\\full\\0", 0, 1);
        matches!(servers, b"\\full\\1", 2);
    }

    #[test]
    fn match_noplayers() {
        let servers = servers! {
            "0.0.0.0:0" => b"\\players\\0\\max\\8"
            "0.0.0.0:0" => b"\\players\\4\\max\\8"
            "0.0.0.0:0" => b"\\players\\8\\max\\8"
        };
        matches!(servers, b"", 0, 1, 2);
        matches!(servers, b"\\noplayers\\0", 1, 2);
        matches!(servers, b"\\noplayers\\1", 0);
    }

    #[test]
    fn match_nat() {
        let servers = servers! {
            "0.0.0.0:0" => b""
            "0.0.0.0:0" => b"\\nat\\0"
            "0.0.0.0:0" => b"\\nat\\1"
        };
        matches!(servers, b"", 0, 1, 2);
        matches!(servers, b"\\nat\\0", 0, 1);
        matches!(servers, b"\\nat\\1", 2);
    }

    #[test]
    fn match_lan() {
        let servers = servers! {
            "0.0.0.0:0" => b""
            "0.0.0.0:0" => b"\\lan\\0"
            "0.0.0.0:0" => b"\\lan\\1"
        };
        matches!(servers, b"", 0, 1, 2);
        matches!(servers, b"\\lan\\0", 0, 1);
        matches!(servers, b"\\lan\\1", 2);
    }

    #[test]
    fn match_bots() {
        let servers = servers! {
            "0.0.0.0:0" => b""
            "0.0.0.0:0" => b"\\bots\\0"
            "0.0.0.0:0" => b"\\bots\\1"
        };
        matches!(servers, b"", 0, 1, 2);
        matches!(servers, b"\\bots\\0", 0, 1);
        matches!(servers, b"\\bots\\1", 2);
    }

    #[test]
    fn match_gamedir() {
        let servers = servers! {
            "0.0.0.0:0" => b"\\gamedir\\valve"
            "0.0.0.0:0" => b"\\gamedir\\cstrike"
            "0.0.0.0:0" => b"\\gamedir\\dod"
            "0.0.0.0:0" => b"\\gamedir\\portal"
            "0.0.0.0:0" => b"\\gamedir\\left4dead"
        };
        matches!(servers, b"", 0, 1, 2, 3, 4);
        matches!(servers, b"\\gamedir\\valve", 0);
        matches!(servers, b"\\gamedir\\portal", 3);
        matches!(servers, b"\\gamedir\\left4dead", 4);
    }

    #[test]
    fn match_map() {
        let servers = servers! {
            "0.0.0.0:0" => b"\\map\\crossfire"
            "0.0.0.0:0" => b"\\map\\boot_camp"
            "0.0.0.0:0" => b"\\map\\de_dust"
            "0.0.0.0:0" => b"\\map\\cs_office"
        };
        matches!(servers, b"", 0, 1, 2, 3);
        matches!(servers, b"\\map\\crossfire", 0);
        matches!(servers, b"\\map\\de_dust", 2);
        matches!(servers, b"\\map\\cs_office", 3);
    }
}
