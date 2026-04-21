// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

//! Server info structures used in filter.

use core::fmt;

#[cfg(all(feature = "alloc", feature = "net"))]
use alloc::boxed::Box;

use bitflags::bitflags;

use crate::{
    cursor::CursorError,
    filter::{FilterFlags, Version},
};

#[cfg(feature = "net")]
use crate::{net::server::ServerAdd, wrappers::Str};

/// The region of the world in which the server is located.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
#[derive(Default)]
pub enum Region {
    /// US East coast.
    USEastCoast = 0x00,
    /// US West coast.
    USWestCoast = 0x01,
    /// South America.
    SouthAmerica = 0x02,
    /// Europe.
    Europe = 0x03,
    /// Asia.
    Asia = 0x04,
    /// Australia.
    Australia = 0x05,
    /// Middle East.
    MiddleEast = 0x06,
    /// Africa.
    Africa = 0x07,
    /// Rest of the world.
    #[default]
    RestOfTheWorld = 0xff,
}

impl TryFrom<u8> for Region {
    type Error = CursorError;

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
            _ => Err(CursorError::InvalidNumber),
        }
    }
}

/// Game server type.
#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(u8)]
#[derive(Default)]
pub enum ServerType {
    /// Dedicated server.
    Dedicated,
    /// Game client.
    Local,
    /// Spectator proxy.
    Proxy,
    /// Unknown.
    #[default]
    Unknown,
}

impl From<u8> for ServerType {
    fn from(value: u8) -> Self {
        match value {
            b'd' => Self::Dedicated,
            b'l' => Self::Local,
            b'p' => Self::Proxy,
            _ => Self::Unknown,
        }
    }
}

impl From<ServerType> for u8 {
    fn from(value: ServerType) -> Self {
        match value {
            ServerType::Dedicated => b'd',
            ServerType::Local => b'l',
            ServerType::Proxy => b'p',
            ServerType::Unknown => 0,
        }
    }
}

impl TryFrom<&[u8]> for ServerType {
    type Error = CursorError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        if let &[c] = value {
            Ok(Self::from(c))
        } else {
            Ok(Self::Unknown)
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

        write!(fmt, "{s}")
    }
}

bitflags! {
    /// Additional server flags.
    #[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
    pub struct ServerFlags: u8 {
        /// Server has bots.
        const BOTS      = 1 << 0;
        /// Server is behind a password.
        const PASSWORD  = 1 << 1;
        /// Server using anti-cheat.
        const SECURE    = 1 << 2;
        /// Server is LAN.
        const LAN       = 1 << 3;
        /// Server behind NAT.
        const NAT       = 1 << 4;
    }
}

/// The operating system on which the game server runs.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
#[repr(u8)]
pub enum Os {
    /// Unknown
    #[default]
    Unknown,
    /// GNU/Linux.
    Linux,
    /// Microsoft Windows
    Windows,
    /// Apple macOS, OS X, Mac OS X
    Mac,
}

impl From<u8> for Os {
    fn from(value: u8) -> Self {
        match value {
            b'l' => Os::Linux,
            b'w' => Os::Windows,
            b'm' => Os::Mac,
            _ => Os::Unknown,
        }
    }
}

impl From<Os> for u8 {
    fn from(value: Os) -> Self {
        match value {
            Os::Unknown => 0,
            Os::Linux => b'l',
            Os::Windows => b'w',
            Os::Mac => b'm',
        }
    }
}

impl TryFrom<&[u8]> for Os {
    type Error = CursorError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        if let &[c] = value {
            Ok(Self::from(c))
        } else {
            Ok(Self::Unknown)
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
        write!(fmt, "{s}")
    }
}

/// Game server information.
#[derive(Clone, Debug)]
pub struct ServerInfo<T> {
    /// Server version.
    pub version: Version,
    /// Server protocol version.
    pub protocol: u8,
    /// Server midification.
    pub gamedir: T,
    /// Server map.
    pub map: T,
    /// Server additional filter flags.
    pub flags: FilterFlags,
    /// Server region.
    pub region: Region,
}

#[cfg(feature = "net")]
impl<'a> ServerInfo<&'a [u8]> {
    /// Creates a new `ServerInfo`.
    pub fn new(info: &ServerAdd<Str<&'a [u8]>>) -> Self {
        Self {
            version: info.version,
            protocol: info.protocol,
            gamedir: &info.gamedir,
            map: &info.map,
            flags: FilterFlags::from(info),
            region: info.region,
        }
    }
}

#[cfg(feature = "net")]
#[cfg(any(feature = "alloc", test))]
impl ServerInfo<Box<[u8]>> {
    /// Creates a new `ServerInfo`.
    pub fn new(info: &ServerAdd<Str<&[u8]>>) -> Self {
        Self {
            version: info.version,
            protocol: info.protocol,
            gamedir: info.gamedir.to_vec().into_boxed_slice(),
            map: info.map.to_vec().into_boxed_slice(),
            flags: FilterFlags::from(info),
            region: info.region,
        }
    }
}
