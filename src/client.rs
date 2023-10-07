// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::fmt;
use std::io::{self, Cursor};
use std::ops::Deref;
use std::str;

use byteorder::{ReadBytesExt, LE};
use log::debug;
use thiserror::Error;

use crate::server_info::{Region, ServerInfo};

#[derive(Error, Debug)]
pub enum Error {
    #[error("Invalid packet")]
    InvalidPacket,
    #[error(transparent)]
    IoError(#[from] io::Error),
}

pub struct Filter<'a>(&'a [u8]);

impl fmt::Debug for Filter<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        String::from_utf8_lossy(self.0).fmt(fmt)
    }
}

impl<'a> Deref for Filter<'a> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

#[derive(Debug)]
pub enum Packet<'a> {
    Challenge(Option<u32>),
    ServerAdd(u32, ServerInfo<&'a str>),
    ServerRemove,
    QueryServers(Region, Filter<'a>),
}

impl<'a> Packet<'a> {
    pub fn decode(s: &'a [u8]) -> Result<Self, Error> {
        match s {
            [b'1', region, tail @ ..] => {
                let region = Region::try_from(*region).map_err(|_| Error::InvalidPacket)?;
                let (tail, _last_ip) = decode_cstr(tail)?;
                let (tail, filter) = decode_cstr(tail)?;
                if !tail.is_empty() {
                    return Err(Error::InvalidPacket);
                }

                Ok(Self::QueryServers(region, Filter(filter)))
            }
            [b'q', 0xff, tail @ ..] => {
                let challenge = Cursor::new(tail).read_u32::<LE>()?;
                Ok(Self::Challenge(Some(challenge)))
            }
            [b'0', b'\n', tail @ ..] => {
                let (challenge, info, tail) =
                    ServerInfo::from_bytes(tail).map_err(|_| Error::InvalidPacket)?;
                if tail != b"" && tail != b"\n" {
                    debug!("unexpected end {:?}", tail);
                }
                Ok(Self::ServerAdd(challenge, info))
            }
            [b'b', b'\n'] => Ok(Self::ServerRemove),
            [b'q'] => Ok(Self::Challenge(None)),
            _ => Err(Error::InvalidPacket),
        }
    }
}

fn decode_cstr(data: &[u8]) -> Result<(&[u8], &[u8]), Error> {
    data.iter()
        .position(|&c| c == 0)
        .ok_or(Error::InvalidPacket)
        .map(|offset| (&data[offset + 1..], &data[..offset]))
}

// fn decode_str(data: &[u8]) -> Result<(&[u8], &str), Error> {
//     let (tail, s) = decode_cstr(data)?;
//     let s = str::from_utf8(s).map_err(|_| Error::InvalidPacket)?;
//     Ok((tail, s))
// }
