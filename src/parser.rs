// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::num::ParseIntError;
use std::str;

use thiserror::Error;

#[derive(Copy, Clone, Error, Debug, PartialEq, Eq)]
pub enum Error {
    #[error("End of map")]
    End,
    #[error("Invalid map")]
    InvalidMap,
    #[error("Invalid string")]
    InvalidString,
    #[error("Invalid boolean")]
    InvalidBool,
    #[error("Invalid integer")]
    InvalidInteger,
}

impl From<ParseIntError> for Error {
    fn from(_: ParseIntError) -> Self {
        Error::InvalidInteger
    }
}

pub type Result<T, E = Error> = std::result::Result<T, E>;

pub struct Parser<'a> {
    cur: &'a [u8],
}

impl<'a> Parser<'a> {
    pub fn new(cur: &'a [u8]) -> Self {
        Self { cur }
    }

    pub fn parse_bytes(&mut self) -> Result<&'a [u8]> {
        match self.cur.split_first() {
            Some((b'\\', tail)) => {
                let pos = tail
                    .iter()
                    .position(|&c| c == b'\\' || c == b'\n')
                    .unwrap_or(tail.len());
                let (head, tail) = tail.split_at(pos);
                self.cur = tail;
                Ok(head)
            }
            Some((b'\n', _)) | None => Err(Error::End),
            _ => Err(Error::InvalidMap),
        }
    }

    pub fn parse<T: ParseValue<'a>>(&mut self) -> Result<T, T::Err> {
        T::parse(self)
    }

    pub fn end(self) -> &'a [u8] {
        self.cur
    }
}

pub trait ParseValue<'a>: Sized {
    type Err: From<Error>;

    fn parse(p: &mut Parser<'a>) -> Result<Self, Self::Err>;
}

impl<'a> ParseValue<'a> for &'a [u8] {
    type Err = Error;

    fn parse(p: &mut Parser<'a>) -> Result<Self, Self::Err> {
        p.parse_bytes()
    }
}

impl<'a> ParseValue<'a> for &'a str {
    type Err = Error;

    fn parse(p: &mut Parser<'a>) -> Result<Self, Self::Err> {
        p.parse_bytes()
            .and_then(|s| str::from_utf8(s).map_err(|_| Error::InvalidString))
    }
}

impl ParseValue<'_> for String {
    type Err = Error;

    fn parse(p: &mut Parser) -> Result<Self, Self::Err> {
        p.parse::<&str>().map(|s| s.to_string())
    }
}

impl ParseValue<'_> for Box<str> {
    type Err = Error;

    fn parse(p: &mut Parser) -> Result<Self, Self::Err> {
        p.parse::<String>().map(|s| s.into_boxed_str())
    }
}

impl ParseValue<'_> for bool {
    type Err = Error;

    fn parse(p: &mut Parser) -> Result<Self, Self::Err> {
        p.parse_bytes().and_then(|s| match s {
            b"0" => Ok(false),
            b"1" => Ok(true),
            _ => Err(Error::InvalidBool),
        })
    }
}

macro_rules! impl_parse_int {
    ($($t:ty : $f:ty),+ $(,)?) => (
        $(impl ParseValue<'_> for $t {
            type Err = Error;

            fn parse(p: &mut Parser) -> Result<Self, Self::Err> {
                p.parse::<&str>().and_then(|s| {
                    s.parse::<$t>()
                        .or_else(|_| s.parse::<$f>().map(|i| i as $t))
                        .map_err(|_| Error::InvalidInteger)
                })
            }
        })+
    );
}

impl_parse_int! {
    i8 :u8,
    i16:u16,
    i32:u32,
    i64:u64,

    u8 :i8,
    u16:i16,
    u32:i32,
    u64:i64,
}

#[cfg(test)]
pub(crate) fn parse<'a, T: ParseValue<'a>>(s: &'a [u8]) -> Result<T, T::Err> {
    Parser::new(s).parse()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_end() {
        assert_eq!(parse::<&[u8]>(b"\\abc"), Ok(&b"abc"[..]));
        assert_eq!(parse::<&[u8]>(b"\\abc\\"), Ok(&b"abc"[..]));
        assert_eq!(parse::<&[u8]>(b"\\abc\n"), Ok(&b"abc"[..]));
    }

    #[test]
    fn parse_empty() {
        assert_eq!(parse::<&[u8]>(b""), Err(Error::End));
        assert_eq!(parse::<&[u8]>(b"\n"), Err(Error::End));
        assert_eq!(parse::<&[u8]>(b"\\"), Ok(&b""[..]));
        assert_eq!(parse::<&[u8]>(b"\\\\"), Ok(&b""[..]));
        assert_eq!(parse::<&[u8]>(b"\\\n"), Ok(&b""[..]));
    }

    #[test]
    fn parse_str() {
        assert_eq!(parse::<&str>(b"\\abc\n"), Ok("abc"));
        assert_eq!(parse::<&str>(b"\\abc\0\n"), Ok("abc\0"));
        assert_eq!(parse::<&str>(b"\\abc\x80\\n"), Err(Error::InvalidString));
    }

    #[test]
    fn parse_bool() {
        assert_eq!(parse::<bool>(b"\\0\n"), Ok(false));
        assert_eq!(parse::<bool>(b"\\1\n"), Ok(true));
        assert_eq!(parse::<bool>(b"\\2\n"), Err(Error::InvalidBool));
        assert_eq!(parse::<bool>(b"\\00\n"), Err(Error::InvalidBool));
        assert_eq!(parse::<bool>(b"\\true\n"), Err(Error::InvalidBool));
        assert_eq!(parse::<bool>(b"\\false\n"), Err(Error::InvalidBool));
    }

    #[test]
    fn parse_int() {
        assert_eq!(parse::<u8>(b"\\0\n"), Ok(0));
        assert_eq!(parse::<u8>(b"\\255\n"), Ok(255));
        assert_eq!(parse::<u8>(b"\\-1\n"), Ok(255));
        assert_eq!(parse::<u8>(b"\\256\n"), Err(Error::InvalidInteger));
        assert_eq!(parse::<u8>(b"\\0xff\n"), Err(Error::InvalidInteger));

        assert_eq!(parse::<i8>(b"\\-1\n"), Ok(-1));
        assert_eq!(parse::<i8>(b"\\-128\n"), Ok(-128));
        assert_eq!(parse::<i8>(b"\\255\n"), Ok(-1));
        assert_eq!(parse::<i8>(b"\\128\n"), Ok(-128));
        assert_eq!(parse::<i8>(b"\\-129\n"), Err(Error::InvalidInteger));
        assert_eq!(parse::<i8>(b"\\0xff\n"), Err(Error::InvalidInteger));
    }
}
