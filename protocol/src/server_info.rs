// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use super::filter::{FilterFlags, Version};
use super::server::{Region, ServerAdd};
use super::wrappers::Str;

/// Game server information.
#[derive(Clone, Debug)]
pub struct ServerInfo {
    /// Server version.
    pub version: Version,
    /// Server protocol version.
    pub protocol: u8,
    /// Server midification.
    pub gamedir: Box<[u8]>,
    /// Server map.
    pub map: Box<[u8]>,
    /// Server additional filter flags.
    pub flags: FilterFlags,
    /// Server region.
    pub region: Region,
}

impl ServerInfo {
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
