// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use crate::filter::FilterFlags;
use crate::server_info::{Region, ServerInfo};

#[derive(Clone, Debug)]
pub struct Server {
    pub version: Box<str>,
    pub gamedir: Box<str>,
    pub flags: FilterFlags,
    pub region: Region,
}

impl Server {
    pub fn new(info: &ServerInfo<&str>) -> Self {
        Self {
            version: info.version.to_string().into_boxed_str(),
            gamedir: info.gamedir.to_string().into_boxed_str(),
            flags: FilterFlags::from(info),
            region: info.region,
        }
    }
}
