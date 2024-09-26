// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

#![cfg_attr(not(feature = "net"), allow(dead_code))]

use core::{mem, str};

#[cfg(feature = "alloc")]
use alloc::{borrow::ToOwned, boxed::Box, string::String};

use crate::{color, wrappers::Str};

use super::{CursorError, Result};

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

impl GetKeyValue<'_> for crate::server_info::Region {
    fn get_key_value(cur: &mut Cursor) -> Result<Self, CursorError> {
        cur.get_key_value::<u8>()?.try_into()
    }
}

impl GetKeyValue<'_> for crate::server_info::ServerType {
    fn get_key_value(cur: &mut Cursor) -> Result<Self, CursorError> {
        cur.get_key_value_raw()?.try_into()
    }
}

impl GetKeyValue<'_> for crate::server_info::Os {
    fn get_key_value(cur: &mut Cursor) -> Result<Self, CursorError> {
        cur.get_key_value_raw()?.try_into()
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
