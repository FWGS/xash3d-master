// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::borrow::Cow;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Color {
    Black,
    Red,
    Green,
    Yellow,
    Blue,
    Cyan,
    Magenta,
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

#[inline]
pub fn is_color_code(s: &str) -> bool {
    matches!(s.as_bytes(), [b'^', c, ..] if c.is_ascii_digit())
}

#[inline]
pub fn trim_start_color(s: &str) -> (&str, &str) {
    let n = if is_color_code(s) { 2 } else { 0 };
    s.split_at(n)
}

pub struct ColorIter<'a> {
    inner: &'a str,
}

impl<'a> ColorIter<'a> {
    pub fn new(inner: &'a str) -> Self {
        Self { inner }
    }
}

impl<'a> Iterator for ColorIter<'a> {
    type Item = (&'a str, &'a str);

    fn next(&mut self) -> Option<Self::Item> {
        if !self.inner.is_empty() {
            let i = self.inner[1..].find('^').map(|i| i + 1).unwrap_or(self.inner.len());
            let (head, tail) = self.inner.split_at(i);
            let (color, text) = trim_start_color(head);
            self.inner = tail;
            Some((color, text))
        } else {
            None
        }
    }
}

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
    }

    #[test]
    fn trim_colors() {
        assert_eq!(trim_color("foo^2bar"), "foobar");
        assert_eq!(trim_color("^1foo^2bar^3"), "foobar");
        assert_eq!(trim_color("^1foo^2bar^3"), "foobar");
        assert_eq!(trim_color("^1foo^bar^3"), "foo^bar");
        assert_eq!(trim_color("^1foo^2bar^"), "foobar^");
        assert_eq!(trim_color("^foo^bar^"), "^foo^bar^");
    }
}
