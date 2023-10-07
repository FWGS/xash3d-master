// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::net::SocketAddrV4;

use bitflags::bitflags;
use log::{debug, log_enabled, Level};

use crate::parser::{Error as ParserError, ParseValue, Parser};
use crate::server::Server;
use crate::server_info::{Os, ServerFlags, ServerInfo, ServerType};

bitflags! {
    #[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
    pub struct FilterFlags: u16 {
        /// Servers running dedicated
        const DEDICATED     = 1 << 0;
        /// Servers that are spectator proxies
        const PROXY         = 1 << 1;
        /// Servers using anti-cheat technology (VAC, but potentially others as well)
        const SECURE        = 1 << 2;
        /// Servers running on a Linux platform
        const LINUX         = 1 << 3;
        /// Servers that are not password protected
        const PASSWORD      = 1 << 4;
        /// Servers that are not empty
        const NOT_EMPTY     = 1 << 5;
        /// Servers that are not full
        const FULL          = 1 << 6;
        /// Servers that are empty
        const NOPLAYERS     = 1 << 7;
        /// Servers that are whitelisted
        const WHITE         = 1 << 8;
        /// Servers that are behind NAT
        const NAT           = 1 << 9;
        /// Servers that are LAN
        const LAN           = 1 << 11;
        /// Servers that has bots
        const BOTS          = 1 << 12;
    }
}

impl<T> From<&ServerInfo<T>> for FilterFlags {
    fn from(info: &ServerInfo<T>) -> Self {
        let mut flags = Self::empty();

        flags.set(Self::DEDICATED, info.server_type == ServerType::Dedicated);
        flags.set(Self::PROXY, info.server_type == ServerType::Proxy);
        flags.set(Self::SECURE, info.flags.contains(ServerFlags::SECURE));
        flags.set(Self::LINUX, info.os == Os::Linux);
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
    // A special filter, specifies that servers matching any of the following [x] conditions should not be returned
    // TODO: \nor\[x]
    // A special filter, specifies that servers matching all of the following [x] conditions should not be returned
    // TODO: \nand\[x]
    /// Servers running the specified modification (ex. cstrike)
    pub gamedir: Option<&'a str>,
    /// Servers running the specified map (ex. cs_italy)
    pub map: Option<&'a str>,
    /// Servers with all of the given tag(s) in sv_tags
    pub gametype: Option<&'a str>,
    /// Servers with all of the given tag(s) in their 'hidden' tags (L4D2)
    pub gamedata: Option<&'a str>,
    /// Servers with any of the given tag(s) in their 'hidden' tags (L4D2)
    pub gamedataor: Option<&'a str>,
    /// Servers with their hostname matching [hostname] (can use * as a wildcard)
    pub name_match: Option<&'a str>,
    /// Servers running version [version] (can use * as a wildcard)
    pub version_match: Option<&'a str>,
    /// Return only servers on the specified IP address (port supported and optional)
    pub gameaddr: Option<SocketAddrV4>,
    /// Servers that are running game [appid]
    pub appid: Option<u32>,
    /// Servers that are NOT running game [appid] (This was introduced to block Left 4 Dead games from the Steam Server Browser)
    pub napp: Option<u32>,
    /// Return only one server for each unique IP address matched
    pub collapse_addr_hash: bool,
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
                b"linux" => filter.insert_flag(FilterFlags::LINUX, p.parse()?),
                b"password" => filter.insert_flag(FilterFlags::PASSWORD, p.parse()?),
                b"proxy" => filter.insert_flag(FilterFlags::PROXY, p.parse()?),
                b"appid" => filter.appid = Some(p.parse()?),
                b"napp" => filter.napp = Some(p.parse()?),
                b"noplayers" => filter.insert_flag(FilterFlags::NOPLAYERS, p.parse()?),
                b"white" => filter.insert_flag(FilterFlags::WHITE, p.parse()?),
                b"gametype" => filter.gametype = Some(p.parse()?),
                b"gamedata" => filter.gamedata = Some(p.parse()?),
                b"gamedataor" => filter.gamedataor = Some(p.parse()?),
                b"name_match" => filter.name_match = Some(p.parse()?),
                b"version_match" => filter.version_match = Some(p.parse()?),
                b"collapse_addr_hash" => filter.collapse_addr_hash = p.parse()?,
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
        parse_appid {
            b"\\appid\\70" => {
                appid: Some(70),
            }
        }
        parse_napp {
            b"\\napp\\70" => {
                napp: Some(70),
            }
        }
        parse_gametype {
            b"\\gametype\\a,b,c,d" => {
                gametype: Some("a,b,c,d"),
            }
        }
        parse_gamedata {
            b"\\gamedata\\a,b,c,d" => {
                gamedata: Some("a,b,c,d"),
            }
        }
        parse_gamedataor {
            b"\\gamedataor\\a,b,c,d" => {
                gamedataor: Some("a,b,c,d"),
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
        parse_collapse_addr_hash {
            b"\\collapse_addr_hash\\1" => {
                collapse_addr_hash: true,
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
        parse_linux(flags_mask: FilterFlags::LINUX) {
            b"\\linux\\0" => {}
            b"\\linux\\1" => {
                flags: FilterFlags::LINUX,
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
        parse_proxy(flags_mask: FilterFlags::PROXY) {
            b"\\proxy\\0" => {}
            b"\\proxy\\1" => {
                flags: FilterFlags::PROXY,
            }
        }
        parse_noplayers(flags_mask: FilterFlags::NOPLAYERS) {
            b"\\noplayers\\0" => {}
            b"\\noplayers\\1" => {
                flags: FilterFlags::NOPLAYERS,
            }
        }
        parse_white(flags_mask: FilterFlags::WHITE) {
            b"\\white\\0" => {}
            b"\\white\\1" => {
                flags: FilterFlags::WHITE,
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
              \\appid\\70\
              \\bots\\1\
              \\clver\\0.20\
              \\collapse_addr_hash\\1\
              \\dedicated\\1\
              \\empty\\1\
              \\full\\1\
              \\gameaddr\\192.168.1.100\
              \\gamedata\\a,b,c,d\
              \\gamedataor\\a,b,c,d\
              \\gamedir\\valve\
              \\gametype\\a,b,c,d\
              \\lan\\1\
              \\linux\\1\
              \\map\\crossfire\
              \\name_match\\localhost\
              \\napp\\60\
              \\nat\\1\
              \\noplayers\\1\
              \\password\\1\
              \\proxy\\1\
              \\secure\\1\
              \\version_match\\1.2.3.4\
              \\white\\1\
            " => {
                gamedir: Some("valve"),
                map: Some("crossfire"),
                appid: Some(70),
                napp: Some(60),
                gametype: Some("a,b,c,d"),
                gamedata: Some("a,b,c,d"),
                gamedataor: Some("a,b,c,d"),
                name_match: Some("localhost"),
                version_match: Some("1.2.3.4"),
                collapse_addr_hash: true,
                gameaddr: Some(SocketAddrV4::new(Ipv4Addr::new(192, 168, 1, 100), 0)),
                clver: Some("0.20"),
                flags: FilterFlags::all(),
                flags_mask: FilterFlags::all(),
            }
        }
    }
}
