// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

#![deny(unsafe_code)]
#![deny(missing_docs)]

//! Xash3D protocol between clients, servers and masters.

#![cfg_attr(all(not(feature = "std"), not(test)), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[macro_use]
extern crate log;

mod cursor;

#[cfg(feature = "net")]
pub mod net;

pub mod color;
pub mod filter;
pub mod server_info;
pub mod wrappers;

#[deprecated(since = "0.2.1", note = "use net module instead")]
#[cfg(feature = "net")]
pub use crate::net::{admin, game, master, server};

use core::fmt;

pub use cursor::CursorError;
pub use server_info::ServerInfo;

use crate::filter::Version;

/// Current protocol version.
pub const PROTOCOL_VERSION: u8 = 49;
/// Current client version.
pub const CLIENT_VERSION: Version = Version::new(0, 20);

/// The error type for decoding and encoding packets.
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// Failed to decode a packet.
    InvalidPacket,
    /// Invalid region.
    InvalidRegion,
    /// Invalid client announce IP.
    InvalidClientAnnounceIp,
    /// Invalid last IP.
    InvalidQueryServersLast,
    /// Server protocol version is not supported.
    InvalidProtocolVersion,
    /// Cursor error.
    CursorError(CursorError),
    /// Invalid value for server add packet.
    InvalidServerValue(&'static str, CursorError),
    /// Invalid value for query servers packet.
    InvalidFilterValue(&'static str, CursorError),
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InvalidPacket => "Invalid packet".fmt(fmt),
            Self::InvalidRegion => "Invalid region".fmt(fmt),
            Self::InvalidClientAnnounceIp => "Invalid client announce IP".fmt(fmt),
            Self::InvalidQueryServersLast => "Invalid last server IP".fmt(fmt),
            Self::InvalidProtocolVersion => "Invalid protocol version".fmt(fmt),
            Self::CursorError(source) => source.fmt(fmt),
            Self::InvalidServerValue(key, source) => {
                write!(
                    fmt,
                    "Invalid value for server add key `{}`: {}",
                    key, source
                )
            }
            Self::InvalidFilterValue(key, source) => {
                write!(fmt, "Invalid value for filter key `{}`: {}", key, source)
            }
        }
    }
}

impl core::error::Error for Error {}

impl From<CursorError> for Error {
    fn from(source: CursorError) -> Self {
        Self::CursorError(source)
    }
}
