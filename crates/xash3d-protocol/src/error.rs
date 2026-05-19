use core::fmt;

use crate::{
    cursor::CursorError,
    map::{InvalidKeyError, InvalidMapError},
};

/// The error type for decoding and encoding packets.
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// Failed to decode a packet.
    InvalidPacket,
    /// Invalid map string.
    InvalidMap,
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
            Self::InvalidMap => "Invalid map string".fmt(fmt),
            Self::InvalidRegion => "Invalid region".fmt(fmt),
            Self::InvalidClientAnnounceIp => "Invalid client announce IP".fmt(fmt),
            Self::InvalidQueryServersLast => "Invalid last server IP".fmt(fmt),
            Self::InvalidProtocolVersion => "Invalid protocol version".fmt(fmt),
            Self::CursorError(source) => source.fmt(fmt),
            Self::InvalidServerValue(key, source) => {
                write!(fmt, "Invalid value for server add key `{key}`: {source}")
            }
            Self::InvalidFilterValue(key, source) => {
                write!(fmt, "Invalid value for filter key `{key}`: {source}")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

impl From<CursorError> for Error {
    fn from(source: CursorError) -> Self {
        Self::CursorError(source)
    }
}

impl From<InvalidMapError> for Error {
    fn from(_: InvalidMapError) -> Self {
        Self::InvalidMap
    }
}

impl From<InvalidKeyError> for Error {
    fn from(_: InvalidKeyError) -> Self {
        Self::InvalidMap
    }
}
