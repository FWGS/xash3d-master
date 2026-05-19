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

use core::{
    ffi::CStr,
    fmt::{self, Write},
    str::FromStr,
};

use bitflags::bitflags;

use crate::{
    cursor::{Cursor, CursorError, GetKeyValue, PutKeyValue},
    map::{MapIter, MapStr},
    server_info::ServerInfo,
    wrappers::Str,
    Error,
};

#[cfg(feature = "net")]
use crate::{
    net::server::ServerAdd,
    server_info::{ServerFlags, ServerType},
};

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

#[cfg(feature = "net")]
impl From<&ServerAdd<'_>> for FilterFlags {
    fn from(info: &ServerAdd<'_>) -> Self {
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
    /// Client protocol version.
    pub protocol: Option<u8>,
    /// Client OS.
    pub client_os: Option<Str<&'a [u8]>>,
    /// Client CPU architecture.
    pub client_arch: Option<Str<&'a [u8]>>,
    /// Client branch.
    pub client_branch: Option<Str<&'a [u8]>>,
    /// Client commit.
    pub client_commit: Option<Str<&'a [u8]>>,
    /// Client buildnum.
    pub client_buildnum: Option<u32>,
    /// A number that master must sent back to game client.
    pub key: Option<u32>,
    /// Additional filter flags.
    pub flags: FilterFlags,
    /// Filter flags mask.
    pub flags_mask: FilterFlags,
}

impl<'a> Filter<'a> {
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
    pub fn matches<T>(&self, info: &ServerInfo<T>) -> bool
    where
        T: AsRef<[u8]>,
    {
        !((info.flags & self.flags_mask) != self.flags
            || self.gamedir.is_some_and(|s| *s != info.gamedir.as_ref())
            || self.map.is_some_and(|s| *s != info.map.as_ref())
            || self.protocol.is_some_and(|s| s != info.protocol))
    }

    fn set_flag(&mut self, flag: FilterFlags, value: &MapStr) -> Result<(), CursorError> {
        self.insert_flag(flag, value.parse_bool()?);
        Ok(())
    }

    fn set(&mut self, key: &MapStr, value: &'a MapStr) -> Result<bool, CursorError> {
        match key.as_bytes() {
            b"dedicated" => self.set_flag(FilterFlags::DEDICATED, value)?,
            b"secure" => self.set_flag(FilterFlags::SECURE, value)?,
            b"gamedir" => self.gamedir = Some(Str(value.as_bytes())),
            b"map" => self.map = Some(Str(value.as_bytes())),
            b"protocol" => self.protocol = Some(value.parse()?),
            b"empty" => self.set_flag(FilterFlags::EMPTY, value)?,
            b"full" => self.set_flag(FilterFlags::FULL, value)?,
            b"password" => self.set_flag(FilterFlags::PASSWORD, value)?,
            b"noplayers" => self.set_flag(FilterFlags::NOPLAYERS, value)?,
            b"clver" => self.clver = Some(value.parse()?),
            b"os" => self.client_os = Some(Str(value.as_bytes())),
            b"arch" => self.client_arch = Some(Str(value.as_bytes())),
            b"branch" => self.client_branch = Some(Str(value.as_bytes())),
            b"commit" => self.client_commit = Some(Str(value.as_bytes())),
            b"buildnum" => self.client_buildnum = Some(value.parse()?),
            b"nat" => self.set_flag(FilterFlags::NAT, value)?,
            b"lan" => self.set_flag(FilterFlags::LAN, value)?,
            b"bots" => self.set_flag(FilterFlags::BOTS, value)?,
            b"key" => self.key = Some(u32::from_str_radix(value.to_str()?, 16)?),
            _ => return Ok(false),
        }
        Ok(true)
    }

    pub fn from_map_iter(iter: MapIter<'a>) -> Result<Self, Error> {
        let mut filter = Self::default();
        for entry in iter {
            let (key, value) = entry?;
            match filter.set(key, value) {
                Ok(true) => {}
                Ok(false) => {
                    trace!("unexpected Filter field {key:?} = {value:?}");
                }
                Err(err) => {
                    let name = filter_key_name_str(key);
                    return Err(Error::InvalidFilterValue(name, err));
                }
            }
        }
        Ok(filter)
    }

    pub fn from_cstr(src: &'a CStr) -> Result<Self, Error> {
        Self::from_map_iter(MapIter::from_cstr(src)?)
    }

    pub fn from_slice(src: &'a [u8]) -> Result<Self, Error> {
        Self::from_map_iter(MapIter::from_slice(src)?)
    }
}

#[inline(never)]
#[cold]
fn filter_key_name_str(key: &MapStr) -> &'static str {
    match key.as_bytes() {
        b"dedicated" => "dedicated",
        b"secure" => "secure",
        b"gamedir" => "gamedir",
        b"map" => "map",
        b"protocol" => "protocol",
        b"empty" => "empty",
        b"full" => "full",
        b"password" => "password",
        b"noplayers" => "noplayers",
        b"clver" => "clver",
        b"os" => "os",
        b"arch" => "arch",
        b"branch" => "branch",
        b"commit" => "commit",
        b"buildnum" => "buildnum",
        b"nat" => "nat",
        b"lan" => "lan",
        b"bots" => "bots",
        b"key" => "key",
        _ => "unknown",
    }
}

impl<'a> TryFrom<&'a CStr> for Filter<'a> {
    type Error = Error;

    fn try_from(src: &'a CStr) -> Result<Self, Self::Error> {
        Self::from_cstr(src)
    }
}

impl<'a> TryFrom<&'a [u8]> for Filter<'a> {
    type Error = Error;

    fn try_from(src: &'a [u8]) -> Result<Self, Self::Error> {
        Self::from_slice(src)
    }
}

impl fmt::Display for Filter<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        macro_rules! display_name {
            ($name:expr) => {
                fmt.write_str(concat!("\\", $name, "\\"))?;
            };
        }

        macro_rules! display_some {
            ($name:expr, $value:expr) => {
                display_some!($name, $value, Display);
            };
            ($name:expr, $value:expr, $trait:ident) => {
                if let Some(s) = $value.as_ref() {
                    display_name!($name);
                    fmt::$trait::fmt(s, fmt)?;
                }
            };
        }

        macro_rules! display_flag {
            ($name:expr, $flag:expr) => {
                if self.flags_mask.contains($flag) {
                    display_name!($name);
                    let c = if self.flags.contains($flag) { '1' } else { '0' };
                    fmt.write_char(c)?;
                }
            };
        }

        display_flag!("dedicated", FilterFlags::DEDICATED);
        display_flag!("secure", FilterFlags::SECURE);
        display_some!("gamedir", self.gamedir);
        display_flag!("secure", FilterFlags::SECURE);
        display_some!("map", self.map);
        display_flag!("empty", FilterFlags::EMPTY);
        display_flag!("full", FilterFlags::FULL);
        display_flag!("password", FilterFlags::PASSWORD);
        display_flag!("noplayers", FilterFlags::NOPLAYERS);
        display_some!("clver", self.clver);
        display_flag!("nat", FilterFlags::NAT);
        display_flag!("lan", FilterFlags::LAN);
        display_flag!("bots", FilterFlags::BOTS);
        display_some!("key", self.key, LowerHex);
        display_some!("protocol", self.protocol);
        display_some!("buildnum", self.client_buildnum);
        display_some!("os", self.client_os);
        display_some!("arch", self.client_arch);
        display_some!("branch", self.client_branch);
        display_some!("commit", self.client_commit);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{cursor::CursorMut, wrappers::Str};

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
        parse_os {
            b"\\os\\linux" => {
                client_os: Some(Str(b"linux")),
            }
            b"\\os\\win32" => {
                client_os: Some(Str(b"win32")),
            }
        }
        parse_arch {
            b"\\arch\\i386" => {
                client_arch: Some(Str(b"i386")),
            }
            b"\\arch\\riscv64" => {
                client_arch: Some(Str(b"riscv64")),
            }
        }
        parse_branch {
            b"\\branch\\master" => {
                client_branch: Some(Str(b"master")),
            }
        }
        parse_commit {
            b"\\commit\\1234abcd" => {
                client_commit: Some(Str(b"1234abcd")),
            }
        }
        parse_buildnum {
            b"\\buildnum\\1234" => {
                client_buildnum: Some(1234),
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
}

#[cfg(all(test, feature = "net"))]
mod match_tests {
    use std::net::SocketAddr;

    use crate::cursor::CursorMut;

    use super::*;

    type ServerInfo = crate::ServerInfo<Box<[u8]>>;

    macro_rules! servers {
        ($($addr:expr => $info:expr $(=> $func:expr)?)+) => (
            [$({
                let addr = $addr.parse::<SocketAddr>().unwrap();
                let mut buf = [0; 512];
                let n = CursorMut::new(&mut buf)
                    .put_bytes(ServerAdd::HEADER).unwrap()
                    .put_key("challenge", 0).unwrap()
                    .put_bytes($info).unwrap()
                    .put_u8(b'\n').unwrap()
                    .pos();
                let p = ServerAdd::decode(&buf[..n]).unwrap();
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
                .filter(|(_, (_addr, server))| filter.matches(&server))
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
