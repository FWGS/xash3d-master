// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

//! Wrappers for byte slices with pretty-printers.

use std::fmt;
use std::ops::Deref;

use crate::cursor::{CursorMut, PutKeyValue};
use crate::CursorError;

/// Wrapper for slice of bytes with printing the bytes as a string.
///
/// # Examples
///
/// ```rust
/// # use xash3d_protocol::types::Str;
/// let s = format!("{}", Str(b"\xff\talex\n"));
/// assert_eq!(s, "\\xff\\talex\\n");
/// ```
#[derive(Copy, Clone, PartialEq, Eq, Default)]
pub struct Str<T>(pub T);

impl<T> From<T> for Str<T> {
    fn from(value: T) -> Self {
        Self(value)
    }
}

impl PutKeyValue for Str<&[u8]> {
    fn put_key_value<'a, 'b>(
        &self,
        cur: &'b mut CursorMut<'a>,
    ) -> Result<&'b mut CursorMut<'a>, CursorError> {
        cur.put_bytes(self.0)
    }
}

impl<T> fmt::Debug for Str<T>
where
    T: AsRef<[u8]>,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "\"{}\"", self)
    }
}

impl<T> fmt::Display for Str<T>
where
    T: AsRef<[u8]>,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        for &c in self.0.as_ref() {
            match c {
                b'\n' => write!(fmt, "\\n")?,
                b'\t' => write!(fmt, "\\t")?,
                b'\\' => write!(fmt, "\\\\")?,
                _ if c.is_ascii_graphic() || c == b' ' => {
                    write!(fmt, "{}", c as char)?;
                }
                _ => write!(fmt, "\\x{:02x}", c)?,
            }
        }
        Ok(())
    }
}

impl<T> Deref for Str<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Wrapper for slice of bytes without printing.
///
/// # Examples
///
/// ```rust
/// # use xash3d_protocol::types::Hide;
/// let s = format!("{}", Hide([1, 2, 3, 4]));
/// assert_eq!(s, "<hidden>");
/// ```
#[derive(Copy, Clone, PartialEq, Eq, Default)]
pub struct Hide<T>(pub T);

impl<T> fmt::Debug for Hide<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "<hidden>")
    }
}

impl<T> fmt::Display for Hide<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "<hidden>")
    }
}

impl<T> Deref for Hide<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
