// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

//! Server query filter.
//!
//! # Supported filters:
//!
//! | Filter    | Type | Description                    | Examples |
//! | --------- | ---- | ------------------------------ | -------- |
//! | map       | str  | Map name                       | `crossfire`, `de_dust` |
//! | gamedir   | str  | Game directory                 | `valve`, `cstrike` |
//! | protocol  | u8   | Game directory                 | `48`, `49` |
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
use std::str::FromStr;

use bitflags::bitflags;

use crate::cursor::{Cursor, GetKeyValue, PutKeyValue};
use crate::server::{ServerAdd, ServerFlags, ServerType};
use crate::wrappers::Str;
use crate::{CursorError, Error, ServerInfo};

bitflags! {
    /// Additional filter flags.
    #[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
    pub struct FilterFlags: u16 {
        /// Servers running dedicated
        const DEDICATED     = 1 << 0;
        /// Servers using anti-cheat technology (VAC, but potentially others as well)
        const SECURE        = 1 << 1;
        /// Servers that are not password protected
        const PASSWORD      = 1 << 2;
        /// Servers that are empty
        const EMPTY         = 1 << 3;
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
        flags.set(Self::EMPTY, info.players == 0);
        flags.set(Self::FULL, info.players >= info.max);
        flags.set(Self::NOPLAYERS, info.players == 0);
        flags.set(Self::NAT, info.flags.contains(ServerFlags::NAT));
        flags.set(Self::LAN, info.flags.contains(ServerFlags::LAN));
        flags.set(Self::BOTS, info.flags.contains(ServerFlags::BOTS));

        flags
    }
}

/// Client or server version.
#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Version {
    /// MAJOR version.
    pub major: u8,
    /// MINOR version.
    pub minor: u8,
    /// PATCH version.
    pub patch: u8,
}

impl Version {
    /// Creates a new `Version`.
    pub const fn new(major: u8, minor: u8) -> Self {
        Self::with_patch(major, minor, 0)
    }

    /// Creates a new `Version` with the specified `patch` version.
    pub const fn with_patch(major: u8, minor: u8, patch: u8) -> Self {
        Self {
            major,
            minor,
            patch,
        }
    }
}

impl fmt::Debug for Version {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}.{}", self.major, self.minor)?;
        if self.patch != 0 {
            write!(fmt, ".{}", self.patch)?;
        }
        Ok(())
    }
}

impl fmt::Display for Version {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        <Self as fmt::Debug>::fmt(self, fmt)
    }
}

impl FromStr for Version {
    type Err = CursorError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (major, tail) = s.split_once('.').unwrap_or((s, "0"));
        let (minor, patch) = tail.split_once('.').unwrap_or((tail, "0"));
        let major = major.parse().map_err(|_| CursorError::InvalidNumber)?;
        let minor = minor.parse().map_err(|_| CursorError::InvalidNumber)?;
        let patch = patch.parse().map_err(|_| CursorError::InvalidNumber)?;
        Ok(Self::with_patch(major, minor, patch))
    }
}

impl GetKeyValue<'_> for Version {
    fn get_key_value(cur: &mut Cursor) -> Result<Self, CursorError> {
        cur.get_key_value().and_then(Self::from_str)
    }
}

impl PutKeyValue for Version {
    fn put_key_value<'a, 'b>(
        &self,
        cur: &'b mut crate::cursor::CursorMut<'a>,
    ) -> Result<&'b mut crate::cursor::CursorMut<'a>, CursorError> {
        cur.put_key_value(self.major)?
            .put_u8(b'.')?
            .put_key_value(self.minor)?;
        if self.patch > 0 {
            cur.put_u8(b'.')?.put_key_value(self.patch)?;
        }
        Ok(cur)
    }
}

/// Server filter.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Filter<'a> {
    /// Servers running the specified modification (ex. cstrike)
    pub gamedir: Option<Str<&'a [u8]>>,
    /// Servers running the specified map (ex. cs_italy)
    pub map: Option<Str<&'a [u8]>>,
    /// Client version.
    pub clver: Option<Version>,
    /// Protocol version
    pub protocol: Option<u8>,
    /// A number that master must sent back to game client.
    pub key: Option<u32>,
    /// Additional filter flags.
    pub flags: FilterFlags,
    /// Filter flags mask.
    pub flags_mask: FilterFlags,
}

impl Filter<'_> {
    /// Insert filter flag.
    pub fn insert_flag(&mut self, flag: FilterFlags, value: bool) {
        self.flags.set(flag, value);
        self.flags_mask.insert(flag);
    }

    /// Test if all `other` flags are set in `flags_mask` and in `flags`.
    pub fn contains_flags(&self, other: FilterFlags) -> Option<bool> {
        if self.flags_mask.contains(other) {
            Some(self.flags.contains(other))
        } else {
            None
        }
    }

    /// Returns `true` if a server matches the filter.
    pub fn matches(&self, _addr: SocketAddrV4, info: &ServerInfo) -> bool {
        !((info.flags & self.flags_mask) != self.flags
            || self.gamedir.map_or(false, |s| *s != &*info.gamedir)
            || self.map.map_or(false, |s| *s != &*info.map)
            || self.protocol.map_or(false, |s| s != info.protocol))
    }
}

impl<'a> TryFrom<&'a [u8]> for Filter<'a> {
    type Error = Error;

    fn try_from(src: &'a [u8]) -> Result<Self, Self::Error> {
        trait Helper<'a> {
            fn get<T: GetKeyValue<'a>>(&mut self, key: &'static str) -> Result<T, Error>;
        }

        impl<'a> Helper<'a> for Cursor<'a> {
            fn get<T: GetKeyValue<'a>>(&mut self, key: &'static str) -> Result<T, Error> {
                T::get_key_value(self).map_err(|e| Error::InvalidFilterValue(key, e))
            }
        }

        let mut cur = Cursor::new(src);
        let mut filter = Self::default();

        loop {
            let key = match cur.get_key_raw().map(Str) {
                Ok(s) => s,
                Err(CursorError::TableEnd) => break,
                Err(e) => Err(e)?,
            };

            match *key {
                b"dedicated" => filter.insert_flag(FilterFlags::DEDICATED, cur.get("dedicated")?),
                b"secure" => filter.insert_flag(FilterFlags::SECURE, cur.get("secure")?),
                b"gamedir" => filter.gamedir = Some(cur.get("gamedir")?),
                b"map" => filter.map = Some(cur.get("map")?),
                b"protocol" => filter.protocol = Some(cur.get("protocol")?),
                b"empty" => filter.insert_flag(FilterFlags::EMPTY, cur.get("empty")?),
                b"full" => filter.insert_flag(FilterFlags::FULL, cur.get("full")?),
                b"password" => filter.insert_flag(FilterFlags::PASSWORD, cur.get("password")?),
                b"noplayers" => filter.insert_flag(FilterFlags::NOPLAYERS, cur.get("noplayers")?),
                b"clver" => filter.clver = Some(cur.get("clver")?),
                b"nat" => filter.insert_flag(FilterFlags::NAT, cur.get("nat")?),
                b"lan" => filter.insert_flag(FilterFlags::LAN, cur.get("lan")?),
                b"bots" => filter.insert_flag(FilterFlags::BOTS, cur.get("bots")?),
                b"key" => {
                    filter.key = Some(
                        cur.get_key_value::<&str>()
                            .and_then(|s| {
                                u32::from_str_radix(s, 16).map_err(|_| CursorError::InvalidNumber)
                            })
                            .map_err(|e| Error::InvalidFilterValue("key", e))?,
                    )
                }
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
        if let Some(s) = self.gamedir {
            write!(fmt, "\\gamedir\\{}", s)?;
        }
        display_flag!("secure", FilterFlags::SECURE);
        if let Some(s) = self.map {
            write!(fmt, "\\map\\{}", s)?;
        }
        display_flag!("empty", FilterFlags::EMPTY);
        display_flag!("full", FilterFlags::FULL);
        display_flag!("password", FilterFlags::PASSWORD);
        display_flag!("noplayers", FilterFlags::NOPLAYERS);
        if let Some(v) = self.clver {
            write!(fmt, "\\clver\\{}", v)?;
        }
        display_flag!("nat", FilterFlags::NAT);
        display_flag!("lan", FilterFlags::LAN);
        display_flag!("bots", FilterFlags::BOTS);
        if let Some(x) = self.key {
            write!(fmt, "\\key\\{:x}", x)?;
        }
        if let Some(x) = self.protocol {
            write!(fmt, "\\protocol\\{}", x)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cursor::CursorMut;
    use crate::wrappers::Str;

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
                    Filter::try_from($src as &[u8]),
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
                gamedir: Some(Str(&b"valve"[..])),
            }
        }
        parse_map {
            b"\\map\\crossfire" => {
                map: Some(Str(&b"crossfire"[..])),
            }
        }
        parse_clver {
            b"\\clver\\0.20" => {
                clver: Some(Version::new(0, 20)),
            }
            b"\\clver\\0.19.3" => {
                clver: Some(Version::with_patch(0, 19, 3)),
            }
        }
        parse_protocol {
            b"\\protocol\\48" => {
                protocol: Some(48)
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
        parse_empty(flags_mask: FilterFlags::EMPTY) {
            b"\\empty\\0" => {}
            b"\\empty\\1" => {
                flags: FilterFlags::EMPTY,
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
              \\protocol\\49\
            " => {
                gamedir: Some(Str(&b"valve"[..])),
                map: Some(Str(&b"crossfire"[..])),
                protocol: Some(49),
                clver: Some(Version::new(0, 20)),
                flags: FilterFlags::all(),
                flags_mask: FilterFlags::all(),
            }
        }
    }

    #[test]
    fn version_to_key_value() {
        let mut buf = [0; 64];
        let n = CursorMut::new(&mut buf[..])
            .put_key_value(Version::with_patch(0, 19, 3))
            .unwrap()
            .pos();
        assert_eq!(&buf[..n], b"0.19.3");
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
            let filter = Filter::try_from($filter as &[u8]).unwrap();
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
        matches!(servers, b"\\empty\\0", 1, 2);
        matches!(servers, b"\\empty\\1", 0);
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

    #[test]
    fn match_protocol() {
        let s = servers! {
            "0.0.0.0:0" => b"\\protocol\\47"
            "0.0.0.0:0" => b"\\protocol\\48"
            "0.0.0.0:0" => b"\\protocol\\49"
        };
        matches!(s, b"", 0, 1, 2);
        matches!(s, b"\\protocol\\48", 1);
        matches!(s, b"\\protocol\\49", 2);
    }
}
