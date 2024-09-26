// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

#[cfg(feature = "alloc")]
use alloc::boxed::Box;

use super::filter::{FilterFlags, Version};
use super::server::{Region, ServerAdd};
use super::wrappers::Str;

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
