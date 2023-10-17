// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use super::filter::{FilterFlags, Version};
use super::server::{Region, ServerAdd};
use super::types::Str;

#[derive(Clone, Debug)]
pub struct ServerInfo {
    pub version: Version,
    pub gamedir: Box<[u8]>,
    pub map: Box<[u8]>,
    pub flags: FilterFlags,
    pub region: Region,
}

impl ServerInfo {
    pub fn new(info: &ServerAdd<Str<&[u8]>>) -> Self {
        Self {
            version: info.version,
            gamedir: info.gamedir.to_vec().into_boxed_slice(),
            map: info.map.to_vec().into_boxed_slice(),
            flags: FilterFlags::from(info),
            region: info.region,
        }
    }
}
