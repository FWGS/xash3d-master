//! Wrappers for byte slices with pretty-printers.

use core::{
    fmt::{self, Write},
    ops::Deref,
    str,
};

use crate::cursor::{CursorError, CursorMut, PutKeyValue};

/// A non-utf8 string slice.
pub type StrSlice<'a> = Str<&'a [u8]>;

/// Wrapper for slice of bytes with printing the bytes as a string.
///
/// # Examples
///
/// ```rust
/// # use xash3d_protocol::wrappers::Str;
/// let s = format!("{}", Str(b"\xff\talex\n"));
/// assert_eq!(s, "\\xff\\talex\\n");
/// ```
#[derive(Copy, Clone, PartialEq, Eq, Default)]
pub struct Str<T>(pub T);

impl<'a> Str<&'a [u8]> {
    /// Returns a byte slice of this string's content.
    pub fn as_bytes(&self) -> &'a [u8] {
        self.0
    }
}

impl<T> From<T> for Str<T> {
    fn from(value: T) -> Self {
        Self(value)
    }
}

impl<'a> From<&'a str> for Str<&'a [u8]> {
    fn from(value: &'a str) -> Self {
        Self(value.as_bytes())
    }
}

impl<T: AsRef<[u8]>> AsRef<[u8]> for Str<T> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
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
        write!(fmt, "\"{self}\"")
    }
}

fn str_format_bytes(s: &[u8], fmt: &mut fmt::Formatter) -> fmt::Result {
    const HEX: [u8; 16] = *b"0123456789abcdef";

    #[inline(always)]
    fn is_printable(c: u8) -> bool {
        c != b'\\' && (c.is_ascii_graphic() || c == b' ')
    }

    let mut it = s.iter().enumerate();
    while let Some((i, mut c)) = it.next() {
        if is_printable(*c) {
            let n = it.find(|(_, c)| !is_printable(**c));
            let e = n.map_or(s.len(), |(e, _)| e);
            // SAFETY: The slice contains only ASCII graphic and space characters.
            let valid = unsafe { str::from_utf8_unchecked(&s[i..e]) };
            fmt.write_str(valid)?;
            match n {
                Some((_, n)) => c = n,
                None => break,
            }
        }

        match c {
            b'\\' => fmt.write_str("\\\\")?,
            b'\n' => fmt.write_str("\\n")?,
            b'\t' => fmt.write_str("\\t")?,
            _ => {
                fmt.write_str("\\x")?;
                fmt.write_char(HEX[(c >> 4) as usize] as char)?;
                fmt.write_char(HEX[(c & 15) as usize] as char)?;
            }
        }
    }

    Ok(())
}

impl<T> fmt::Display for Str<T>
where
    T: AsRef<[u8]>,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        str_format_bytes(self.0.as_ref(), fmt)
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
/// # use xash3d_protocol::wrappers::Hide;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn str_wrapper_format() {
        assert_eq!(
            Str(b"123\\foobar\n\x00 \tbaz%\n\\\xff").to_string(),
            r#"123\\foobar\n\x00 \tbaz%\n\\\xff"#
        );
        assert_eq!(
            Str(b"\xff123\\foobar\n\x00 \tbaz%\n\\").to_string(),
            r#"\xff123\\foobar\n\x00 \tbaz%\n\\"#
        );
    }
}
