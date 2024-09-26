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
