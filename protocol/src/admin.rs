// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use crate::cursor::{Cursor, CursorMut};
use crate::types::Str;
use crate::Error;

pub const HASH_LEN: usize = 64;

#[derive(Clone, Debug, PartialEq)]
pub struct AdminChallenge;

impl AdminChallenge {
    pub const HEADER: &'static [u8] = b"adminchallenge";

    pub fn decode(src: &[u8]) -> Result<Self, Error> {
        if src == Self::HEADER {
            Ok(Self)
        } else {
            Err(Error::InvalidPacket)
        }
    }

    pub fn encode(&self, buf: &mut [u8]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf).put_bytes(Self::HEADER)?.pos())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct AdminCommand<'a> {
    pub hash: &'a [u8],
    pub command: Str<&'a [u8]>,
}

impl<'a> AdminCommand<'a> {
    pub const HEADER: &'static [u8] = b"admin";

    pub fn new(hash: &'a [u8], command: &'a str) -> Self {
        Self {
            hash,
            command: Str(command.as_bytes()),
        }
    }

    pub fn decode(src: &'a [u8]) -> Result<Self, Error> {
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        let hash = cur.get_bytes(HASH_LEN)?;
        let command = Str(cur.get_bytes(cur.remaining())?);
        cur.expect_empty()?;
        Ok(Self { hash, command })
    }

    pub fn encode(&self, buf: &mut [u8]) -> Result<usize, Error> {
        Ok(CursorMut::new(buf)
            .put_bytes(Self::HEADER)?
            .put_bytes(self.hash)?
            .put_bytes(&self.command)?
            .pos())
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
        assert_eq!(AdminChallenge::decode(&buf[..n]), Ok(p));
    }

    #[test]
    fn admin_command() {
        let p = AdminCommand::new(&[1; HASH_LEN], "foo bar baz");
        let mut buf = [0; 512];
        let n = p.encode(&mut buf).unwrap();
        assert_eq!(AdminCommand::decode(&buf[..n]), Ok(p));
    }
}
