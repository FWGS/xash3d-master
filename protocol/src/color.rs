// SPDX-License-Identifier: LGPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

//! Color codes for strings.

#[cfg(feature = "alloc")]
use alloc::{borrow::Cow, string::String};

/// Color codes `^digit`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Color {
    /// Black is coded as `^0`.
    Black,
    /// Red is coded as `^1`.
    Red,
    /// Green is coded as `^2`.
    Green,
    /// Yellow is coded as `^3`.
    Yellow,
    /// Blue is coded as `^4`.
    Blue,
    /// Cyan is coded as `^5`.
    Cyan,
    /// Magenta is coded as `^6`.
    Magenta,
    /// White is coded as `^7`.
    White,
}

impl TryFrom<&str> for Color {
    type Error = ();

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Ok(match value {
            "^0" => Self::Black,
            "^1" => Self::Red,
            "^2" => Self::Green,
            "^3" => Self::Yellow,
            "^4" => Self::Blue,
            "^5" => Self::Cyan,
            "^6" => Self::Magenta,
            "^7" => Self::White,
            _ => return Err(()),
        })
    }
}

/// Test if string starts with color code.
///
/// # Examples
/// ```rust
/// # use xash3d_protocol::color::is_color_code;
/// assert_eq!(is_color_code("hello"), false);
/// assert_eq!(is_color_code("^4blue ocean"), true);
/// ```
#[inline]
pub fn is_color_code(s: &str) -> bool {
    matches!(s.as_bytes(), [b'^', c, ..] if c.is_ascii_digit())
}

/// Trim color codes from a start of string.
///
/// # Examples
///
/// ```rust
/// # use xash3d_protocol::color::trim_start_color;
/// assert_eq!(trim_start_color("hello"), ("", "hello"));
/// assert_eq!(trim_start_color("^1red apple"), ("^1", "red apple"));
/// assert_eq!(trim_start_color("^1^2^3yellow roof"), ("^3", "yellow roof"));
/// ```
#[inline]
pub fn trim_start_color(s: &str) -> (&str, &str) {
    let mut n = 0;
    while is_color_code(&s[n..]) {
        n += 2;
    }
    if n > 0 {
        (&s[n - 2..n], &s[n..])
    } else {
        s.split_at(0)
    }
}

/// Iterator for colored parts of a string.
///
/// # Examples
///
/// ```rust
/// # use xash3d_protocol::color::ColorIter;
/// let colored = "^1red flower^7 and ^2green grass";
/// let mut iter = ColorIter::new(colored);
/// assert_eq!(iter.next(), Some(("^1", "red flower")));
/// assert_eq!(iter.next(), Some(("^7", " and ")));
/// assert_eq!(iter.next(), Some(("^2", "green grass")));
/// assert_eq!(iter.next(), None);
/// ```
pub struct ColorIter<'a> {
    inner: &'a str,
}

impl<'a> ColorIter<'a> {
    /// Creates a new `ColorIter`.
    pub fn new(inner: &'a str) -> Self {
        Self { inner }
    }
}

impl<'a> Iterator for ColorIter<'a> {
    type Item = (&'a str, &'a str);

    fn next(&mut self) -> Option<Self::Item> {
        if self.inner.is_empty() {
            return None;
        }
        let (color, tail) = trim_start_color(self.inner);
        let offset = tail
            .char_indices()
            .map(|(i, _)| i)
            .find(|&i| is_color_code(&tail[i..]))
            .unwrap_or(tail.len());
        let (head, tail) = tail.split_at(offset);
        self.inner = tail;
        Some((color, head))
    }
}

/// Trim color codes from a string.
///
/// # Examples
///
/// ```rust
/// # use xash3d_protocol::color::trim_color;
/// assert_eq!(trim_color("^1no^7 ^2colors^7"), "no colors");
/// ```
#[cfg(feature = "alloc")]
pub fn trim_color(s: &str) -> Cow<'_, str> {
    let (_, s) = trim_start_color(s);
    if !s.chars().any(|c| c == '^') {
        return Cow::Borrowed(s);
    }

    let mut out = String::with_capacity(s.len());
    for (_, s) in ColorIter::new(s) {
        out.push_str(s);
    }

    Cow::Owned(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trim_start_colors() {
        assert_eq!(trim_start_color("foo^2bar"), ("", "foo^2bar"));
        assert_eq!(trim_start_color("^foo^2bar"), ("", "^foo^2bar"));
        assert_eq!(trim_start_color("^1foo^2bar"), ("^1", "foo^2bar"));
        assert_eq!(trim_start_color("^1^2^3foo^2bar"), ("^3", "foo^2bar"));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn trim_colors() {
        assert_eq!(trim_color("foo^2bar"), "foobar");
        assert_eq!(trim_color("^1foo^2bar^3"), "foobar");
        assert_eq!(trim_color("^1foo^2bar^3"), "foobar");
        assert_eq!(trim_color("^1foo^bar^3"), "foo^bar");
        assert_eq!(trim_color("^1foo^2bar^"), "foobar^");
        assert_eq!(trim_color("^foo^bar^"), "^foo^bar^");
        assert_eq!(trim_color("\u{fe0f}^1foo^bar^"), "\u{fe0f}foo^bar^");
        assert_eq!(
            trim_color("^1^2^3foo\u{fe0f}^2^\u{fe0f}^bar^"),
            "foo\u{fe0f}^\u{fe0f}^bar^"
        );
    }
}
