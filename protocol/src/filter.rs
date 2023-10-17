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

use std::fmt;
use std::net::SocketAddrV4;
use std::num::ParseIntError;
use std::str::FromStr;

use bitflags::bitflags;
use log::debug;

use crate::cursor::{Cursor, GetKeyValue, PutKeyValue};
use crate::server::{ServerAdd, ServerFlags, ServerType};
use crate::types::Str;
use crate::{Error, ServerInfo};

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

impl<T> From<&ServerAdd<T>> for FilterFlags {
    fn from(info: &ServerAdd<T>) -> Self {
        let mut flags = Self::empty();

        flags.set(Self::DEDICATED, info.server_type == ServerType::Dedicated);
        flags.set(Self::SECURE, info.flags.contains(ServerFlags::SECURE));
        flags.set(Self::PASSWORD, info.flags.contains(ServerFlags::PASSWORD));
        flags.set(Self::NOT_EMPTY, info.players > 0);
        flags.set(Self::FULL, info.players >= info.max);
        flags.set(Self::NOPLAYERS, info.players == 0);
        flags.set(Self::NAT, info.flags.contains(ServerFlags::NAT));
        flags.set(Self::LAN, info.flags.contains(ServerFlags::LAN));
        flags.set(Self::BOTS, info.flags.contains(ServerFlags::BOTS));

        flags
    }
}

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Version {
    pub major: u8,
    pub minor: u8,
}

impl Version {
    pub fn new(major: u8, minor: u8) -> Self {
        Self { major, minor }
    }
}

impl fmt::Debug for Version {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}.{}", self.major, self.minor)
    }
}

impl fmt::Display for Version {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}.{}", self.major, self.minor)
    }
}

impl FromStr for Version {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (major, minor) = s.split_once('.').unwrap_or((s, "0"));
        Ok(Self::new(major.parse()?, minor.parse()?))
    }
}

impl GetKeyValue<'_> for Version {
    fn get_key_value(cur: &mut Cursor) -> Result<Self, Error> {
        Self::from_str(cur.get_key_value()?).map_err(|_| Error::InvalidPacket)
    }
}

impl PutKeyValue for Version {
    fn put_key_value<'a, 'b>(
        &self,
        cur: &'b mut crate::cursor::CursorMut<'a>,
    ) -> Result<&'b mut crate::cursor::CursorMut<'a>, Error> {
        cur.put_key_value(self.major)?
            .put_u8(b'.')?
            .put_key_value(self.minor)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Filter<'a> {
    /// Servers running the specified modification (ex. cstrike)
    pub gamedir: &'a [u8],
    /// Servers running the specified map (ex. cs_italy)
    pub map: &'a [u8],
    /// Client version.
    pub clver: Version,

    pub flags: FilterFlags,
    pub flags_mask: FilterFlags,
}

impl Filter<'_> {
    pub fn insert_flag(&mut self, flag: FilterFlags, value: bool) {
        self.flags.set(flag, value);
        self.flags_mask.insert(flag);
    }

    pub fn matches(&self, _addr: SocketAddrV4, info: &ServerInfo) -> bool {
        !((info.flags & self.flags_mask) != self.flags
            || (!self.gamedir.is_empty() && self.gamedir != &*info.gamedir)
            || (!self.map.is_empty() && self.map != &*info.map))
    }
}

impl<'a> Filter<'a> {
    pub fn from_bytes(src: &'a [u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        let mut filter = Self::default();

        loop {
            let key = match cur.get_key_raw().map(Str) {
                Ok(s) => s,
                Err(Error::UnexpectedEnd) => break,
                Err(e) => return Err(e),
            };

            match *key {
                b"dedicated" => filter.insert_flag(FilterFlags::DEDICATED, cur.get_key_value()?),
                b"secure" => filter.insert_flag(FilterFlags::SECURE, cur.get_key_value()?),
                b"gamedir" => filter.gamedir = cur.get_key_value()?,
                b"map" => filter.map = cur.get_key_value()?,
                b"empty" => filter.insert_flag(FilterFlags::NOT_EMPTY, cur.get_key_value()?),
                b"full" => filter.insert_flag(FilterFlags::FULL, cur.get_key_value()?),
                b"password" => filter.insert_flag(FilterFlags::PASSWORD, cur.get_key_value()?),
                b"noplayers" => filter.insert_flag(FilterFlags::NOPLAYERS, cur.get_key_value()?),
                b"clver" => {
                    filter.clver = cur
                        .get_key_value::<&str>()?
                        .parse()
                        .map_err(|_| Error::InvalidPacket)?
                }
                b"nat" => filter.insert_flag(FilterFlags::NAT, cur.get_key_value()?),
                b"lan" => filter.insert_flag(FilterFlags::LAN, cur.get_key_value()?),
                b"bots" => filter.insert_flag(FilterFlags::BOTS, cur.get_key_value()?),
                _ => {
                    // skip unknown fields
                    let value = Str(cur.get_key_value_raw()?);
                    debug!("Invalid Filter field \"{}\" = \"{}\"", key, value);
                }
            }
        }

        Ok(filter)
    }
}

impl fmt::Display for &Filter<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        macro_rules! display_flag {
            ($n:expr, $f:expr) => {
                if self.flags_mask.contains($f) {
                    let flag = if self.flags.contains($f) { '1' } else { '0' };
                    write!(fmt, "\\{}\\{}", $n, flag)?;
                }
            };
        }

        display_flag!("dedicated", FilterFlags::DEDICATED);
        display_flag!("secure", FilterFlags::SECURE);
        if !self.gamedir.is_empty() {
            write!(fmt, "\\gamedir\\{}", Str(self.gamedir))?;
        }
        display_flag!("secure", FilterFlags::SECURE);
        if !self.map.is_empty() {
            write!(fmt, "\\map\\{}", Str(self.map))?;
        }
        display_flag!("empty", FilterFlags::NOT_EMPTY);
        display_flag!("full", FilterFlags::FULL);
        display_flag!("password", FilterFlags::PASSWORD);
        display_flag!("noplayers", FilterFlags::NOPLAYERS);
        write!(fmt, "\\clver\\{}", self.clver)?;
        display_flag!("nat", FilterFlags::NAT);
        display_flag!("lan", FilterFlags::LAN);
        display_flag!("bots", FilterFlags::BOTS);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::cursor::CursorMut;
    use super::super::types::Str;
    use super::*;

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
                gamedir: &b"valve"[..],
            }
        }
        parse_map {
            b"\\map\\crossfire" => {
                map: &b"crossfire"[..],
            }
        }
        parse_clver {
            b"\\clver\\0.20" => {
                clver: Version::new(0, 20),
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
              \\gamedir\\valve\
              \\lan\\1\
              \\map\\crossfire\
              \\nat\\1\
              \\noplayers\\1\
              \\password\\1\
              \\secure\\1\
            " => {
                gamedir: &b"valve"[..],
                map: &b"crossfire"[..],
                clver: Version::new(0, 20),
                flags: FilterFlags::all(),
                flags_mask: FilterFlags::all(),
            }
        }
    }

    macro_rules! servers {
        ($($addr:expr => $info:expr $(=> $func:expr)?)+) => (
            [$({
                let addr = $addr.parse::<SocketAddrV4>().unwrap();
                let mut buf = [0; 512];
                let n = CursorMut::new(&mut buf)
                    .put_bytes(ServerAdd::HEADER).unwrap()
                    .put_key("challenge", 0).unwrap()
                    .put_bytes($info).unwrap()
                    .pos();
                let p = ServerAdd::<Str<&[u8]>>::decode(&buf[..n]).unwrap();
                let server = ServerInfo::new(&p);
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
