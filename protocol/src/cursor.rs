// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

mod read;
mod write;

use core::fmt;

pub use read::{Cursor, GetKeyValue};
pub use write::{CursorMut, PutKeyValue};

/// The error type for `Cursor` and `CursorMut`.
#[derive(Debug, PartialEq, Eq)]
pub enum CursorError {
    /// Invalid number.
    InvalidNumber,
    /// Invalid string.
    InvalidString,
    /// Invalid boolean.
    InvalidBool,
    /// Invalid table entry.
    InvalidTableKey,
    /// Invalid table entry.
    InvalidTableValue,
    /// Table end found.
    TableEnd,
    /// Expected data not found.
    Expect,
    /// An unexpected data found.
    ExpectEmpty,
    /// Buffer size is no enougth to decode or encode a packet.
    UnexpectedEnd,
}

impl fmt::Display for CursorError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            Self::InvalidNumber => "Invalid number",
            Self::InvalidString => "Invalid string",
            Self::InvalidBool => "Invalid boolean",
            Self::InvalidTableKey => "Invalid table key",
            Self::InvalidTableValue => "Invalid table entry",
            Self::TableEnd => "Table end",
            Self::Expect => "Expected data not found",
            Self::ExpectEmpty => "Unexpected data",
            Self::UnexpectedEnd => "Unexpected end of buffer",
        };
        s.fmt(fmt)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for CursorError {}

pub type Result<T, E = CursorError> = core::result::Result<T, E>;

#[cfg(test)]
mod tests {
    use super::*;

    use crate::wrappers::Str;

    #[test]
    fn cursor() -> Result<()> {
        let mut buf = [0; 64];
        let n = CursorMut::new(&mut buf)
            .put_bytes(b"12345678")?
            .put_array(b"4321")?
            .put_str("abc")?
            .put_cstr("def")?
            .put_u8(0x7f)?
            .put_i8(-128)?
            .put_u32_le(0x44332211)?
            .pos();
        let s = &buf[..n];

        let mut cur = Cursor::new(s);
        assert_eq!(cur.get_bytes(8), Ok(&b"12345678"[..]));
        assert_eq!(cur.get_array::<4>(), Ok(*b"4321"));
        assert_eq!(cur.get_str(3), Ok("abc"));
        assert_eq!(cur.get_cstr(), Ok(Str(&b"def"[..])));
        assert_eq!(cur.get_u8(), Ok(0x7f));
        assert_eq!(cur.get_i8(), Ok(-128));
        assert_eq!(cur.get_u32_le(), Ok(0x44332211));
        assert_eq!(cur.get_u8(), Err(CursorError::UnexpectedEnd));

        Ok(())
    }

    #[test]
    fn key() -> Result<()> {
        let mut buf = [0; 512];
        let n = CursorMut::new(&mut buf)
            .put_key("p", 49)?
            .put_key("map", "crossfire")?
            .put_key("dm", true)?
            .put_key("team", false)?
            .put_key("coop", false)?
            .put_key("numcl", 4)?
            .put_key("maxcl", 32)?
            .put_key("gamedir", "valve")?
            .put_key("password", false)?
            .put_key("host", "test")?
            .pos();
        let s = &buf[..n];

        let mut cur = Cursor::new(s);
        assert_eq!(cur.get_key(), Ok((&b"p"[..], 49_u8)));
        assert_eq!(cur.get_key(), Ok((&b"map"[..], "crossfire")));
        assert_eq!(cur.get_key(), Ok((&b"dm"[..], true)));
        assert_eq!(cur.get_key(), Ok((&b"team"[..], false)));
        assert_eq!(cur.get_key(), Ok((&b"coop"[..], false)));
        assert_eq!(cur.get_key(), Ok((&b"numcl"[..], 4_u8)));
        assert_eq!(cur.get_key(), Ok((&b"maxcl"[..], 32_u8)));
        assert_eq!(cur.get_key(), Ok((&b"gamedir"[..], "valve")));
        assert_eq!(cur.get_key(), Ok((&b"password"[..], false)));
        assert_eq!(cur.get_key(), Ok((&b"host"[..], "test")));
        assert_eq!(cur.get_key::<&[u8]>(), Err(CursorError::TableEnd));

        Ok(())
    }
}
