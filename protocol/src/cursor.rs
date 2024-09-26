// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use core::{
    fmt::{self, Write},
    mem, str,
};

#[cfg(feature = "alloc")]
use alloc::{borrow::ToOwned, boxed::Box, string::String};

use super::color;
use super::wrappers::Str;

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

impl core::error::Error for CursorError {}

pub type Result<T, E = CursorError> = core::result::Result<T, E>;

pub trait GetKeyValue<'a>: Sized {
    fn get_key_value(cur: &mut Cursor<'a>) -> Result<Self>;
}

impl<'a> GetKeyValue<'a> for &'a [u8] {
    fn get_key_value(cur: &mut Cursor<'a>) -> Result<Self> {
        cur.get_key_value_raw()
    }
}

impl<'a> GetKeyValue<'a> for Str<&'a [u8]> {
    fn get_key_value(cur: &mut Cursor<'a>) -> Result<Self> {
        cur.get_key_value_raw().map(Str)
    }
}

impl<'a> GetKeyValue<'a> for &'a str {
    fn get_key_value(cur: &mut Cursor<'a>) -> Result<Self> {
        let raw = cur.get_key_value_raw()?;
        str::from_utf8(raw).map_err(|_| CursorError::InvalidString)
    }
}

#[cfg(feature = "alloc")]
impl<'a> GetKeyValue<'a> for Box<str> {
    fn get_key_value(cur: &mut Cursor<'a>) -> Result<Self> {
        let raw = cur.get_key_value_raw()?;
        str::from_utf8(raw)
            .map(|s| s.to_owned().into_boxed_str())
            .map_err(|_| CursorError::InvalidString)
    }
}

#[cfg(feature = "alloc")]
impl<'a> GetKeyValue<'a> for String {
    fn get_key_value(cur: &mut Cursor<'a>) -> Result<Self> {
        let raw = cur.get_key_value_raw()?;
        str::from_utf8(raw)
            .map(|s| s.to_owned())
            .map_err(|_| CursorError::InvalidString)
    }
}

impl<'a> GetKeyValue<'a> for bool {
    fn get_key_value(cur: &mut Cursor<'a>) -> Result<Self> {
        match cur.get_key_value_raw()? {
            b"0" => Ok(false),
            b"1" => Ok(true),
            _ => Err(CursorError::InvalidBool),
        }
    }
}

macro_rules! impl_get_value {
    ($($t:ty),+ $(,)?) => {
        $(impl<'a> GetKeyValue<'a> for $t {
            fn get_key_value(cur: &mut Cursor<'a>) -> Result<Self> {
                let s = cur.get_key_value::<&str>()?;
                // HACK: special case for one asshole
                let (_, s) = color::trim_start_color(s);
                s.parse().map_err(|_| CursorError::InvalidNumber)
            }
        })+
    };
}

impl_get_value! {
    u8,
    u16,
    u32,
    u64,

    i8,
    i16,
    i32,
    i64,
}

// TODO: impl GetKeyValue for f32 and f64

#[derive(Copy, Clone)]
pub struct Cursor<'a> {
    buffer: &'a [u8],
}

macro_rules! impl_get {
    ($($n:ident: $t:ty = $f:ident),+ $(,)?) => (
        $(#[inline]
        pub fn $n(&mut self) -> Result<$t> {
            const N: usize = mem::size_of::<$t>();
            self.get_array::<N>().map(<$t>::$f)
        })+
    );
}

impl<'a> Cursor<'a> {
    pub fn new(buffer: &'a [u8]) -> Self {
        Self { buffer }
    }

    pub fn end(self) -> &'a [u8] {
        self.buffer
    }

    pub fn as_slice(&'a self) -> &'a [u8] {
        self.buffer
    }

    #[inline(always)]
    pub fn remaining(&self) -> usize {
        self.buffer.len()
    }

    #[inline(always)]
    pub fn has_remaining(&self) -> bool {
        self.remaining() != 0
    }

    pub fn get_bytes(&mut self, count: usize) -> Result<&'a [u8]> {
        if count <= self.remaining() {
            let (head, tail) = self.buffer.split_at(count);
            self.buffer = tail;
            Ok(head)
        } else {
            Err(CursorError::UnexpectedEnd)
        }
    }

    pub fn advance(&mut self, count: usize) -> Result<()> {
        self.get_bytes(count).map(|_| ())
    }

    pub fn get_array<const N: usize>(&mut self) -> Result<[u8; N]> {
        self.get_bytes(N).map(|s| {
            let mut array = [0; N];
            array.copy_from_slice(s);
            array
        })
    }

    pub fn get_str(&mut self, n: usize) -> Result<&'a str> {
        let mut cur = *self;
        let s = cur
            .get_bytes(n)
            .and_then(|s| str::from_utf8(s).map_err(|_| CursorError::InvalidString))?;
        *self = cur;
        Ok(s)
    }

    pub fn get_cstr(&mut self) -> Result<Str<&'a [u8]>> {
        let pos = self
            .buffer
            .iter()
            .position(|&c| c == b'\0')
            .ok_or(CursorError::UnexpectedEnd)?;
        let (head, tail) = self.buffer.split_at(pos);
        self.buffer = &tail[1..];
        Ok(Str(&head[..pos]))
    }

    pub fn get_cstr_as_str(&mut self) -> Result<&'a str> {
        str::from_utf8(&self.get_cstr()?).map_err(|_| CursorError::InvalidString)
    }

    #[inline(always)]
    pub fn get_u8(&mut self) -> Result<u8> {
        self.get_array::<1>().map(|s| s[0])
    }

    #[inline(always)]
    pub fn get_i8(&mut self) -> Result<i8> {
        self.get_array::<1>().map(|s| s[0] as i8)
    }

    impl_get! {
        get_u16_le: u16 = from_le_bytes,
        get_u32_le: u32 = from_le_bytes,
        get_u64_le: u64 = from_le_bytes,
        get_i16_le: i16 = from_le_bytes,
        get_i32_le: i32 = from_le_bytes,
        get_i64_le: i64 = from_le_bytes,
        get_f32_le: f32 = from_le_bytes,
        get_f64_le: f64 = from_le_bytes,

        get_u16_be: u16 = from_be_bytes,
        get_u32_be: u32 = from_be_bytes,
        get_u64_be: u64 = from_be_bytes,
        get_i16_be: i16 = from_be_bytes,
        get_i32_be: i32 = from_be_bytes,
        get_i64_be: i64 = from_be_bytes,
        get_f32_be: f32 = from_be_bytes,
        get_f64_be: f64 = from_be_bytes,

        get_u16_ne: u16 = from_ne_bytes,
        get_u32_ne: u32 = from_ne_bytes,
        get_u64_ne: u64 = from_ne_bytes,
        get_i16_ne: i16 = from_ne_bytes,
        get_i32_ne: i32 = from_ne_bytes,
        get_i64_ne: i64 = from_ne_bytes,
        get_f32_ne: f32 = from_ne_bytes,
        get_f64_ne: f64 = from_ne_bytes,
    }

    pub fn expect(&mut self, s: &[u8]) -> Result<()> {
        if self.buffer.starts_with(s) {
            self.advance(s.len())?;
            Ok(())
        } else {
            Err(CursorError::Expect)
        }
    }

    pub fn expect_empty(&self) -> Result<()> {
        if self.has_remaining() {
            Err(CursorError::ExpectEmpty)
        } else {
            Ok(())
        }
    }

    pub fn take_while<F>(&mut self, mut cond: F) -> Result<&'a [u8]>
    where
        F: FnMut(u8) -> bool,
    {
        self.buffer
            .iter()
            .position(|&i| !cond(i))
            .ok_or(CursorError::UnexpectedEnd)
            .and_then(|n| self.get_bytes(n))
    }

    pub fn take_while_or_all<F>(&mut self, cond: F) -> &'a [u8]
    where
        F: FnMut(u8) -> bool,
    {
        self.take_while(cond).unwrap_or_else(|_| {
            let (head, tail) = self.buffer.split_at(self.buffer.len());
            self.buffer = tail;
            head
        })
    }

    pub fn get_key_value_raw(&mut self) -> Result<&'a [u8]> {
        let mut cur = *self;
        match cur.get_u8()? {
            b'\\' => {
                let value = cur.take_while_or_all(|c| c != b'\\' && c != b'\n');
                *self = cur;
                Ok(value)
            }
            _ => Err(CursorError::InvalidTableValue),
        }
    }

    pub fn get_key_value<T: GetKeyValue<'a>>(&mut self) -> Result<T> {
        T::get_key_value(self)
    }

    pub fn skip_key_value<T: GetKeyValue<'a>>(&mut self) -> Result<()> {
        T::get_key_value(self).map(|_| ())
    }

    pub fn get_key_raw(&mut self) -> Result<&'a [u8]> {
        let mut cur = *self;
        match cur.get_u8() {
            Ok(b'\\') => {
                let value = cur.take_while(|c| c != b'\\' && c != b'\n')?;
                *self = cur;
                Ok(value)
            }
            Ok(b'\n') | Err(CursorError::UnexpectedEnd) => Err(CursorError::TableEnd),
            _ => Err(CursorError::InvalidTableKey),
        }
    }

    pub fn get_key<T: GetKeyValue<'a>>(&mut self) -> Result<(&'a [u8], T)> {
        Ok((self.get_key_raw()?, self.get_key_value()?))
    }
}

pub trait PutKeyValue {
    fn put_key_value<'a, 'b>(&self, cur: &'b mut CursorMut<'a>) -> Result<&'b mut CursorMut<'a>>;
}

impl<T> PutKeyValue for &T
where
    T: PutKeyValue,
{
    fn put_key_value<'a, 'b>(&self, cur: &'b mut CursorMut<'a>) -> Result<&'b mut CursorMut<'a>> {
        (*self).put_key_value(cur)
    }
}

impl PutKeyValue for &str {
    fn put_key_value<'a, 'b>(&self, cur: &'b mut CursorMut<'a>) -> Result<&'b mut CursorMut<'a>> {
        cur.put_str(self)
    }
}

impl PutKeyValue for bool {
    fn put_key_value<'a, 'b>(&self, cur: &'b mut CursorMut<'a>) -> Result<&'b mut CursorMut<'a>> {
        cur.put_u8(if *self { b'1' } else { b'0' })
    }
}

macro_rules! impl_put_key_value {
    ($($t:ty),+ $(,)?) => {
        $(impl PutKeyValue for $t {
            fn put_key_value<'a, 'b>(&self, cur: &'b mut CursorMut<'a>) -> Result<&'b mut CursorMut<'a>> {
                cur.put_as_str(self)
            }
        })+
    };
}

impl_put_key_value! {
    u8,
    u16,
    u32,
    u64,

    i8,
    i16,
    i32,
    i64,

    f32,
    f64,
}

pub struct CursorMut<'a> {
    buffer: &'a mut [u8],
    pos: usize,
}

macro_rules! impl_put {
    ($($n:ident: $t:ty = $f:ident),+ $(,)?) => (
        $(#[inline]
        pub fn $n(&mut self, n: $t) -> Result<&mut Self> {
            self.put_array(&n.$f())
        })+
    );
}

impl<'a> CursorMut<'a> {
    pub fn new(buffer: &'a mut [u8]) -> Self {
        Self { buffer, pos: 0 }
    }

    pub fn pos(&mut self) -> usize {
        self.pos
    }

    #[inline(always)]
    pub fn available(&self) -> usize {
        self.buffer.len() - self.pos
    }

    pub fn advance<F>(&mut self, count: usize, mut f: F) -> Result<&mut Self>
    where
        F: FnMut(&mut [u8]),
    {
        if count <= self.available() {
            f(&mut self.buffer[self.pos..self.pos + count]);
            self.pos += count;
            Ok(self)
        } else {
            Err(CursorError::UnexpectedEnd)
        }
    }

    pub fn put_bytes(&mut self, s: &[u8]) -> Result<&mut Self> {
        self.advance(s.len(), |i| {
            i.copy_from_slice(s);
        })
    }

    pub fn put_array<const N: usize>(&mut self, s: &[u8; N]) -> Result<&mut Self> {
        self.advance(N, |i| {
            i.copy_from_slice(s);
        })
    }

    pub fn put_str(&mut self, s: &str) -> Result<&mut Self> {
        self.put_bytes(s.as_bytes())
    }

    pub fn put_cstr(&mut self, s: &str) -> Result<&mut Self> {
        self.put_str(s)?.put_u8(0)
    }

    #[inline(always)]
    pub fn put_u8(&mut self, n: u8) -> Result<&mut Self> {
        self.put_array(&[n])
    }

    #[inline(always)]
    pub fn put_i8(&mut self, n: i8) -> Result<&mut Self> {
        self.put_u8(n as u8)
    }

    impl_put! {
        put_u16_le: u16 = to_le_bytes,
        put_u32_le: u32 = to_le_bytes,
        put_u64_le: u64 = to_le_bytes,
        put_i16_le: i16 = to_le_bytes,
        put_i32_le: i32 = to_le_bytes,
        put_i64_le: i64 = to_le_bytes,
        put_f32_le: f32 = to_le_bytes,
        put_f64_le: f64 = to_le_bytes,

        put_u16_be: u16 = to_be_bytes,
        put_u32_be: u32 = to_be_bytes,
        put_u64_be: u64 = to_be_bytes,
        put_i16_be: i16 = to_be_bytes,
        put_i32_be: i32 = to_be_bytes,
        put_i64_be: i64 = to_be_bytes,
        put_f32_be: f32 = to_be_bytes,
        put_f64_be: f64 = to_be_bytes,

        put_u16_ne: u16 = to_ne_bytes,
        put_u32_ne: u32 = to_ne_bytes,
        put_u64_ne: u64 = to_ne_bytes,
        put_i16_ne: i16 = to_ne_bytes,
        put_i32_ne: i32 = to_ne_bytes,
        put_i64_ne: i64 = to_ne_bytes,
        put_f32_ne: f32 = to_ne_bytes,
        put_f64_ne: f64 = to_ne_bytes,
    }

    pub fn put_as_str<T: fmt::Display>(&mut self, value: T) -> Result<&mut Self> {
        write!(self, "{}", value).map_err(|_| CursorError::UnexpectedEnd)?;
        Ok(self)
    }

    pub fn put_key_value<T: PutKeyValue>(&mut self, value: T) -> Result<&mut Self> {
        value.put_key_value(self)
    }

    pub fn put_key_raw(&mut self, key: &str, value: &[u8]) -> Result<&mut Self> {
        self.put_u8(b'\\')?
            .put_str(key)?
            .put_u8(b'\\')?
            .put_bytes(value)
    }

    pub fn put_key<T: PutKeyValue>(&mut self, key: &str, value: T) -> Result<&mut Self> {
        self.put_u8(b'\\')?
            .put_str(key)?
            .put_u8(b'\\')?
            .put_key_value(value)
    }
}

impl fmt::Write for CursorMut<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.put_bytes(s.as_bytes())
            .map(|_| ())
            .map_err(|_| fmt::Error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
