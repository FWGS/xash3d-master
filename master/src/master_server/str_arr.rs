use std::str;

pub struct StrArr<const N: usize> {
    len: u8,
    arr: [u8; N],
}

impl<const N: usize> StrArr<N> {
    pub const MAX_SIZE: usize = N;

    pub fn new(s: &[u8]) -> Option<Self> {
        if N > 255 {
            panic!("MAX_SIZE must be less than 255");
        }
        let s = str::from_utf8(s).ok()?;
        let mut buf = [0; N];
        if s.len() <= Self::MAX_SIZE {
            buf[..s.len()].copy_from_slice(s.as_bytes());
            Some(Self {
                len: s.len() as u8,
                arr: buf,
            })
        } else {
            None
        }
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.arr[..self.len as usize]
    }

    pub fn as_str(&self) -> &str {
        // SAFETY: checked in constructor
        unsafe {
            str::from_utf8_unchecked(self.as_bytes())
        }
    }
}
