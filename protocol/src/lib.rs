// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

#![deny(missing_docs)]

//! Xash3D protocol between clients, servers and masters.

mod cursor;
mod server_info;

pub mod admin;
pub mod color;
pub mod filter;
pub mod game;
pub mod master;
pub mod server;
pub mod types;

pub use server_info::ServerInfo;

use thiserror::Error;

use crate::filter::Version;

/// Current protocol version.
pub const PROTOCOL_VERSION: u8 = 49;
/// Current client version.
pub const CLIENT_VERSION: Version = Version::new(0, 20);

/// The error type for decoding and encoding packets.
#[derive(Error, Debug, PartialEq, Eq)]
pub enum Error {
    /// Failed to decode a packet.
    #[error("Invalid packet")]
    InvalidPacket,
    /// Invalid string in a packet.
    #[error("Invalid UTF-8 string")]
    InvalidString,
    /// Buffer size is no enougth to decode or encode a packet.
    #[error("Unexpected end of buffer")]
    UnexpectedEnd,
    /// Server protocol version is not supported.
    #[error("Invalid protocol version")]
    InvalidProtocolVersion,
}
