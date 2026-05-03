// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

#![cfg_attr(not(feature = "net"), allow(dead_code))]

use core::{
    fmt::{self, Write},
    str,
};

use super::{CursorError, Result};

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

impl PutKeyValue for crate::server_info::ServerType {
    fn put_key_value<'a, 'b>(
        &self,
        cur: &'b mut CursorMut<'a>,
    ) -> Result<&'b mut CursorMut<'a>, CursorError> {
        match self {
            Self::Dedicated => cur.put_str("d"),
            Self::Local => cur.put_str("l"),
            Self::Proxy => cur.put_str("p"),
            Self::Unknown => cur.put_str("?"),
        }
    }
}

impl PutKeyValue for crate::server_info::Os {
    fn put_key_value<'a, 'b>(
        &self,
        cur: &'b mut CursorMut<'a>,
    ) -> Result<&'b mut CursorMut<'a>, CursorError> {
        match self {
            Self::Linux => cur.put_str("l"),
            Self::Windows => cur.put_str("w"),
            Self::Mac => cur.put_str("m"),
            Self::Unknown => cur.put_str("?"),
        }
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
    offset: usize,
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
        Self {
            buffer,
            pos: 0,
            offset: 0,
        }
    }

    fn with_offset(buffer: &'a mut [u8], offset: usize) -> Self {
        Self {
            buffer,
            pos: 0,
            offset,
        }
    }

    /// Returns the position in the original buffer.
    pub fn pos(&self) -> usize {
        self.offset + self.pos
    }

    /// Returns the position in the current chunk of original buffer.
    pub fn current_pos(&self) -> usize {
        self.pos
    }

    #[inline(always)]
    pub fn available(&self) -> usize {
        self.buffer.len() - self.pos
    }

    pub fn expect_full(&self) -> Result<()> {
        if self.available() == 0 {
            Ok(())
        } else {
            Err(CursorError::ExpectFull)
        }
    }

    /// Splits this cursor into two parts after `len` bytes.
    ///
    /// The first returned cursor have `len` capacity. The second returned cursor have all
    /// remaining capacity in the original buffer.
    pub fn split(mut self, len: usize) -> Result<(Self, Self)> {
        if self.available() < len {
            return Err(CursorError::BufferOverflow);
        }
        let offset = self.pos + len;
        let (head, tail) = self.buffer.split_at_mut(offset);
        let tail = CursorMut::with_offset(tail, self.offset + offset);
        self.buffer = head;
        Ok((self, tail))
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
            Err(CursorError::BufferOverflow)
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

    pub fn put_cstr(&mut self, s: impl AsRef<[u8]>) -> Result<&mut Self> {
        self.put_bytes(s.as_ref())?.put_u8(0)
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
        write!(self, "{value}").map_err(|_| CursorError::BufferOverflow)?;
        Ok(self)
    }

    pub fn put_as_cstr<T: fmt::Display>(&mut self, value: T) -> Result<&mut Self> {
        self.put_as_str(value)?.put_u8(0)
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
    fn split() {
        let mut buf = [0; 8];
        let cur = CursorMut::new(&mut buf);
        assert_eq!(cur.pos(), 0);

        let (mut head, mut tail) = cur.split(4).unwrap();
        assert_eq!(head.pos(), 0);
        assert_eq!(tail.pos(), 4);

        head.put_u8(1).unwrap();
        assert_eq!(head.pos(), 1);

        tail.put_u8(2).unwrap();
        assert_eq!(tail.pos(), 5);

        assert_eq!(buf[0], 1);
        assert_eq!(buf[1], 0);
        assert_eq!(buf[4], 2);
        assert_eq!(buf[5], 0);
    }
}
