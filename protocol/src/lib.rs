// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

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

pub const PROTOCOL_VERSION: u8 = 49;

pub const CLIENT_VERSION: Version = Version::new(0, 20);

#[derive(Error, Debug, PartialEq, Eq)]
pub enum Error {
    #[error("Invalid packet")]
    InvalidPacket,
    #[error("Invalid UTF-8 string")]
    InvalidString,
    #[error("Unexpected end of buffer")]
    UnexpectedEnd,
    #[error("Invalid protocol version")]
    InvalidProtocolVersion,
}
