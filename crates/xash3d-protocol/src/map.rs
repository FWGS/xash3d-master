use core::{
    ffi::CStr,
    fmt::{self, Write},
    mem,
    ops::Deref,
    str::{self, FromStr, Utf8Error},
};

use memchr::{memchr, memchr2, memchr_iter};

use crate::cursor::CursorError;

/// The error type which can occur when attempting to interpret a sequence of [u8] as a [MapStr].
#[derive(Debug, PartialEq, Eq)]
pub struct MapStrError(());

impl fmt::Display for MapStrError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("failed to create a map string")
    }
}

/// The error type which can be returned when attempting to parse a [MapStr] into another type.
#[derive(Debug, PartialEq, Eq)]
pub enum MapStrParseError<E> {
    /// A map string is not a valid UTF-8 string.
    Utf8Error(Utf8Error),
    /// A map string can not be parsed into another type.
    ParseError(E),
}

impl<E: fmt::Display> fmt::Display for MapStrParseError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Utf8Error(err) => err.fmt(f),
            Self::ParseError(err) => err.fmt(f),
        }
    }
}

impl<E> From<Utf8Error> for MapStrParseError<E> {
    fn from(value: Utf8Error) -> Self {
        Self::Utf8Error(value)
    }
}

/// A type representing a map string.
///
/// The string must not contain `\` and `\0` characters. The character encoding is undefined.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct MapStr {
    bytes: [u8],
}

impl MapStr {
    /// Creates a new map string from a C string.
    ///
    /// # Examples
    ///
    /// ```
    /// use xash3d_protocol::map::MapStr;
    ///
    /// let gamedir = MapStr::from_cstr(c"valve").unwrap();
    /// assert_eq!(gamedir, "valve");
    ///
    /// // A string must not contain `\` characters.
    /// assert!(MapStr::from_cstr(c"\\gamedir\\valve").is_err());
    /// ```
    pub fn from_cstr(s: &CStr) -> Result<&Self, MapStrError> {
        let bytes = s.to_bytes();
        if memchr(b'\\', bytes).is_none() {
            // SAFETY: The slice does not contain `\` and `\0` characters.
            Ok(unsafe { Self::new_unchecked(bytes) })
        } else {
            Err(MapStrError(()))
        }
    }

    /// Creates a new map string from a slice of bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use xash3d_protocol::map::MapStr;
    ///
    /// let gamedir = MapStr::from_slice(b"valve").unwrap();
    /// assert_eq!(gamedir, "valve");
    ///
    /// // A string must not contain `\` characters.
    /// assert!(MapStr::from_slice(b"\\gamedir\\valve").is_err());
    /// ```
    pub fn from_slice(bytes: &[u8]) -> Result<&Self, MapStrError> {
        if memchr2(b'\\', b'\0', bytes).is_none() {
            // SAFETY: The slice does not contain `\` and `\0` characters.
            Ok(unsafe { Self::new_unchecked(bytes) })
        } else {
            Err(MapStrError(()))
        }
    }

    /// Creates a map string without checking whether a byte slice contains invalid characters.
    ///
    /// # Safety
    ///
    /// The given byte slice must not contain `\` and `\0` characters.
    pub unsafe fn new_unchecked(bytes: &[u8]) -> &Self {
        // SAFETY: MapStr is a repr(transparent) struct with a [u8] field.
        unsafe { mem::transmute(bytes) }
    }

    /// Returns a byte slice of this MapStr’s contents.
    #[inline(always)]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Converts a map string to a string slice.
    pub fn to_str(&self) -> Result<&str, Utf8Error> {
        str::from_utf8(self.as_bytes())
    }

    /// Parses this map string into another type.
    pub fn parse<F>(&self) -> Result<F, MapStrParseError<<F as FromStr>::Err>>
    where
        F: FromStr,
    {
        self.to_str()?.parse().map_err(MapStrParseError::ParseError)
    }

    pub fn parse_bool(&self) -> Result<bool, CursorError> {
        match self.as_bytes() {
            b"0" => Ok(false),
            b"1" => Ok(true),
            _ => Err(CursorError::InvalidBool),
        }
    }
}

impl<'a> TryFrom<&'a [u8]> for &'a MapStr {
    type Error = MapStrError;

    fn try_from(bytes: &'a [u8]) -> Result<Self, Self::Error> {
        MapStr::from_slice(bytes)
    }
}

impl<'a> TryFrom<&'a str> for &'a MapStr {
    type Error = MapStrError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        MapStr::from_slice(s.as_bytes())
    }
}

impl Deref for MapStr {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_bytes()
    }
}

impl PartialEq<&[u8]> for &MapStr {
    fn eq(&self, other: &&[u8]) -> bool {
        self.as_bytes().eq(*other)
    }
}

impl PartialEq<&str> for &MapStr {
    fn eq(&self, other: &&str) -> bool {
        self.as_bytes().eq(other.as_bytes())
    }
}

impl fmt::Debug for MapStr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('"')?;
        fmt::Display::fmt(self, f)?;
        f.write_char('"')
    }
}

impl fmt::Display for MapStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut bytes = self.as_bytes();
        loop {
            match str::from_utf8(bytes) {
                Ok(s) => return f.write_str(s),
                Err(err) => {
                    let (valid, tail) = bytes.split_at(err.valid_up_to());

                    // SAFETY: from_utf8 verifies that it is a valid UTF-8 string.
                    unsafe {
                        f.write_str(str::from_utf8_unchecked(valid))?;
                    }

                    f.write_char('\u{FFFD}')?;

                    if let Some(invalid_len) = err.error_len() {
                        bytes = &tail[invalid_len..]
                    } else {
                        break;
                    }
                }
            }
        }
        Ok(())
    }
}

/// The error type which can occur when attempting to create a [MapIter].
#[derive(Debug, PartialEq, Eq)]
pub struct InvalidMapError(());

impl fmt::Display for InvalidMapError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("map contains invalid characters")
    }
}

/// The error type which can occur when iterating a [MapIter].
#[derive(Debug, PartialEq, Eq)]
pub struct InvalidKeyError(());

impl fmt::Display for InvalidKeyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("failed to extract map key")
    }
}

/// An iterator over `\key\value` pairs.
///
/// # Examples
///
/// ```
/// use xash3d_protocol::map::MapIter;
///
/// let src = c"\\gamedir\\valve\\map\\crossfire\\players\\3";
/// for i in MapIter::from_cstr(src).unwrap() {
///     let (key, value) = i.unwrap();
///     match key.as_bytes() {
///         b"gamedir" => assert_eq!(value, "valve"),
///         b"map" => assert_eq!(value, "crossfire"),
///         b"players" => assert_eq!(value, "3"),
///         _ => unreachable!(),
///     }
/// }
/// ```
pub struct MapIter<'a> {
    bytes: &'a [u8],
}

impl<'a> MapIter<'a> {
    /// Creates a new `MapIter` from a C string.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the string is non-empty and does not start with a `\` character.
    pub fn from_cstr(s: &'a CStr) -> Result<Self, InvalidMapError> {
        let bytes = s.to_bytes();
        let bytes = match bytes.first() {
            Some(b'\\') => &bytes[1..],
            Some(_) => return Err(InvalidMapError(())),
            None => bytes,
        };

        // SAFETY: The slice does not contain `\0` characters and does not start with
        // a `\` character.
        Ok(unsafe { Self::new_unchecked(bytes) })
    }

    /// Creates a new `MapIter` from a byte slice.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the following conditions are not met:
    ///
    /// * The slice contains `\0` characters.
    /// * The slice is non-empty and it does not start with a `\` character.
    pub fn from_slice(bytes: &'a [u8]) -> Result<Self, InvalidMapError> {
        let bytes = match bytes.first() {
            Some(b'\\') => {
                let bytes = &bytes[1..];
                if memchr(b'\0', bytes).is_some() {
                    return Err(InvalidMapError(()));
                }
                bytes
            }
            Some(_) => return Err(InvalidMapError(())),
            None => bytes,
        };

        // SAFETY: The slice does not contain `\0` characters and does not start with
        // a `\` character.
        Ok(unsafe { Self::new_unchecked(bytes) })
    }

    /// Creates a map iter without checking whether a byte slice contains invalid characters.
    ///
    /// # Safety
    ///
    /// Callers of this function are responsible that these preconditions are satisfied:
    ///
    ///   * The byte slice must not contain `\0` characters.
    ///   * The byte slice must start with a `\` character if length is not zero.
    pub unsafe fn new_unchecked(bytes: &'a [u8]) -> Self {
        Self { bytes }
    }
}

impl<'a> Iterator for MapIter<'a> {
    type Item = Result<(&'a MapStr, &'a MapStr), InvalidKeyError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.bytes.is_empty() {
            return None;
        }

        let mut iter = memchr_iter(b'\\', self.bytes);
        let Some(p) = iter.next() else {
            return Some(Err(InvalidKeyError(())));
        };
        let (e, tail) = match iter.next() {
            Some(e) => (e, e + 1),
            None => (self.bytes.len(), self.bytes.len()),
        };

        // SAFETY: The byte slice does not contain `\0` characters which is checked in
        // the constructor.
        let ret = unsafe {
            let k = self.bytes.get_unchecked(..p);
            let v = self.bytes.get_unchecked(p + 1..e);
            self.bytes = self.bytes.get_unchecked(tail..);
            (MapStr::new_unchecked(k), MapStr::new_unchecked(v))
        };

        Some(Ok(ret))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn map_str() {
        assert!(MapStr::from_slice(b"123abc").is_ok());
        assert!(MapStr::from_slice(b"123\\abc").is_err());
    }

    #[test]
    fn map_str_format() {
        assert_eq!(MapStr::from_slice(b"abc123").unwrap().to_string(), "abc123");
        assert_eq!(
            MapStr::from_slice(b"a\xff1").unwrap().to_string(),
            "a\u{FFFD}1"
        );
    }

    #[test]
    fn map_iter() {
        let mut it = MapIter::from_slice(b"").unwrap();
        assert!(it.next().is_none());

        let mut it = MapIter::from_slice(b"\\key0\\value0\\key1\\\\key2\\value2").unwrap();
        let mut next = || it.next().unwrap().unwrap();
        let (k, v) = next();
        assert_eq!(k, "key0");
        assert_eq!(v, "value0");
        let (k, v) = next();
        assert_eq!(k, "key1");
        assert_eq!(v, "");
        let (k, v) = next();
        assert_eq!(k, "key2");
        assert_eq!(v, "value2");
        assert!(it.next().is_none());

        let mut it = MapIter::from_slice(b"\\key0").unwrap();
        assert!(it.next().unwrap().is_err());

        assert!(MapIter::from_slice(b"abc\\123").is_err());
        assert!(MapIter::from_slice(b"\\abc\\123\0").is_err());
        assert!(MapIter::from_slice(b"\\abc\0\\123").is_err());

        let s = CStr::from_bytes_with_nul(b"\0").unwrap();
        let mut it = MapIter::from_cstr(s).unwrap();
        assert!(it.next().is_none());

        let s = CStr::from_bytes_with_nul(b"\\key0\\value0\0").unwrap();
        let mut it = MapIter::from_cstr(s).unwrap();
        let (k, v) = it.next().unwrap().unwrap();
        assert_eq!(k, "key0");
        assert_eq!(v, "value0");
        assert!(it.next().is_none());

        let s = CStr::from_bytes_with_nul(b"abc\\123\0").unwrap();
        assert!(MapIter::from_cstr(s).is_err());
    }
}
