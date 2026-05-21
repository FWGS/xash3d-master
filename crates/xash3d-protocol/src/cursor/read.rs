#![cfg_attr(not(feature = "net"), allow(dead_code))]

use core::{ffi::CStr, mem, str};

use memchr::{memchr, memchr2};

use crate::wrappers::{Str, StrSlice};

use super::{CursorError, Result};

#[derive(Copy, Clone)]
pub struct Cursor<'a> {
    buffer: &'a [u8],
    pos: usize,
}

macro_rules! impl_get {
    ($($n:ident: $t:ty = $f:ident),+ $(,)?) => (
        $(#[inline(always)]
        pub fn $n(&mut self) -> Result<$t> {
            const N: usize = mem::size_of::<$t>();
            self.get_array::<N>().map(<$t>::$f)
        })+
    );
}

impl<'a> Cursor<'a> {
    pub fn new(buffer: &'a [u8]) -> Self {
        Self { buffer, pos: 0 }
    }

    #[inline(always)]
    pub fn end(self) -> &'a [u8] {
        &self.buffer[self.pos..]
    }

    #[inline(always)]
    pub fn pos(&self) -> usize {
        self.pos
    }

    #[inline(always)]
    pub fn as_slice(&'a self) -> &'a [u8] {
        &self.buffer[self.pos..]
    }

    #[inline(always)]
    pub fn remaining(&self) -> usize {
        self.buffer.len() - self.pos
    }

    #[inline(always)]
    pub fn has_remaining(&self) -> bool {
        self.pos < self.buffer.len()
    }

    pub fn get_tail(&mut self) -> &'a [u8] {
        if self.pos < self.buffer.len() {
            let tail = &self.buffer[self.pos..];
            self.pos = self.buffer.len();
            tail
        } else {
            b""
        }
    }

    #[inline(always)]
    pub fn get_bytes(&mut self, count: usize) -> Result<&'a [u8]> {
        let end = self.pos + count;
        if end <= self.buffer.len() {
            let bytes = &self.buffer[self.pos..end];
            self.pos = end;
            Ok(bytes)
        } else {
            Err(CursorError::NeedMoreBytes(end - self.buffer.len()))
        }
    }

    pub fn advance(&mut self, count: usize) -> Result<()> {
        self.get_bytes(count).map(|_| ())
    }

    #[inline(always)]
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

    pub fn find(&mut self, c: u8) -> Result<usize> {
        memchr(c, &self.buffer[self.pos..]).ok_or(CursorError::NeedMoreBytes(1))
    }

    pub fn find2(&mut self, c0: u8, c1: u8) -> Result<usize> {
        memchr2(c0, c1, &self.buffer[self.pos..]).ok_or(CursorError::NeedMoreBytes(1))
    }

    pub fn take_until(&mut self, c: u8) -> Result<&'a [u8]> {
        let e = self.pos + self.find(c)?;
        let s = &self.buffer[self.pos..e];
        self.pos = e;
        Ok(s)
    }

    pub fn take_until2(&mut self, c0: u8, c1: u8) -> Result<&'a [u8]> {
        let e = self.pos + self.find2(c0, c1)?;
        let s = &self.buffer[self.pos..e];
        self.pos = e;
        Ok(s)
    }

    pub fn get_cstr_ffi(&mut self) -> Result<&'a CStr> {
        let e = self.pos + self.find(b'\0')? + 1;
        let s = &self.buffer[self.pos..e];
        self.pos = e;
        // SAFETY: The slice contains exactly one nul-byte at the end.
        Ok(unsafe { CStr::from_bytes_with_nul_unchecked(s) })
    }

    pub fn get_cstr(&mut self) -> Result<StrSlice<'a>> {
        Ok(Str(self.get_cstr_ffi()?.to_bytes()))
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
        if self.remaining() < s.len() {
            Err(CursorError::NeedMoreBytes(s.len() - self.remaining()))
        } else if self.as_slice().starts_with(s) {
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
        self.as_slice()
            .iter()
            .position(|&i| !cond(i))
            .ok_or(CursorError::NeedMoreBytes(1))
            .and_then(|n| self.get_bytes(n))
    }
}
