// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::fmt;
use std::ops::Deref;

/// Wrapper for slice of bytes with printing the bytes as a string
#[derive(Copy, Clone, PartialEq, Eq, Default)]
pub struct Str<T>(pub T);

impl<T> From<T> for Str<T> {
    fn from(value: T) -> Self {
        Self(value)
    }
}

impl<T> fmt::Debug for Str<T>
where
    T: AsRef<[u8]>,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        for &c in self.0.as_ref() {
            match c {
                b'\n' => write!(fmt, "\\n")?,
                b'\t' => write!(fmt, "\\t")?,
                _ if c.is_ascii_graphic() || c == b' ' => {
                    write!(fmt, "{}", c as char)?;
                }
                _ => write!(fmt, "\\x{:02x}", c)?,
            }
        }
        Ok(())
    }
}

impl<T> fmt::Display for Str<T>
where
    T: AsRef<[u8]>,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        <Self as fmt::Debug>::fmt(self, fmt)
    }
}

impl<T> Deref for Str<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
