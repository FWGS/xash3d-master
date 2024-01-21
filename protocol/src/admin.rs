// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

//! Admin packets.

use crate::cursor::{Cursor, CursorMut};
use crate::types::Hide;
use crate::{CursorError, Error};

/// Default hash length.
pub const HASH_LEN: usize = 64;
/// Default hash key.
pub const HASH_KEY: &str = "Half-Life";
/// Default hash personality.
pub const HASH_PERSONAL: &str = "Freeman";

/// Admin challenge request.
#[derive(Clone, Debug, PartialEq)]
pub struct AdminChallenge;

impl AdminChallenge {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"adminchallenge";

    /// Decode packet from `src`.
    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        if src == Self::HEADER {
            Ok(Self)
        } else {
            Err(CursorError::Expect)?
        }
    }

    /// Encode packet to `buf`.
    pub fn encode(&self, buf: &mut [u8]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf).put_bytes(Self::HEADER)?.pos())
    }
}

/// Admin command.
#[derive(Clone, Debug, PartialEq)]
pub struct AdminCommand<'a> {
    /// A number received in admin challenge response.
    pub master_challenge: u32,
    /// A password hash mixed with a challenge number received in admin challenge response.
    pub hash: Hide<&'a [u8]>,
    /// A command to execute on a master server.
    pub command: &'a str,
}

impl<'a> AdminCommand<'a> {
    /// Packet header.
    pub const HEADER: &'static [u8] = b"admin";

    /// Creates a new `AdminCommand`.
    pub fn new(master_challenge: u32, hash: &'a [u8], command: &'a str) -> Self {
        Self {
            master_challenge,
            hash: Hide(hash),
            command,
        }
    }

    /// Decode packet from `src` with specified hash length.
    pub fn decode_with_hash_len(hash_len: usize, src: &'a [u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        let master_challenge = cur.get_u32_le()?;
        let hash = Hide(cur.get_bytes(hash_len)?);
        let command = cur.get_str(cur.remaining())?;
        cur.expect_empty()?;
        Ok(Self {
            master_challenge,
            hash,
            command,
        })
    }

    /// Decode packet from `src`.
    #[inline]
    pub fn decode(src: &'a [u8]) -> Result<Self, Error> {
        Self::decode_with_hash_len(HASH_LEN, src)
    }

    /// Encode packet to `buf`.
    pub fn encode(&self, buf: &mut [u8]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf)
            .put_bytes(Self::HEADER)?
            .put_u32_le(self.master_challenge)?
            .put_bytes(&self.hash)?
            .put_str(self.command)?
            .pos())
    }
}

/// Admin packet.
#[derive(Clone, Debug, PartialEq)]
pub enum Packet<'a> {
    /// Admin challenge request.
    AdminChallenge,
    /// Admin command.
    AdminCommand(AdminCommand<'a>),
}

impl<'a> Packet<'a> {
    /// Decode packet from `src` with specified hash length.
    pub fn decode(hash_len: usize, src: &'a [u8]) -> Result<Option<Self>, Error> {
        if src.starts_with(AdminChallenge::HEADER) {
            AdminChallenge::decode(src).map(|_| Self::AdminChallenge)
        } else if src.starts_with(AdminCommand::HEADER) {
            AdminCommand::decode_with_hash_len(hash_len, src).map(Self::AdminCommand)
        } else {
            return Ok(None);
        }
        .map(Some)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn admin_challenge() {
        let p = AdminChallenge;
        let mut buf = [0; 512];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(
            Packet::decode(HASH_LEN, &buf[..n]),
            Ok(Some(Packet::AdminChallenge))
        );
    }

    #[test]
    fn admin_command() {
        let p = AdminCommand::new(0x12345678, &[1; HASH_LEN], "foo bar baz");
        let mut buf = [0; 512];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(
            Packet::decode(HASH_LEN, &buf[..n]),
            Ok(Some(Packet::AdminCommand(p)))
        );
    }
}
