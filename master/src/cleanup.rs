use std::ops::{Deref, DerefMut};

pub struct Cleanup<T> {
    max: u16,
    cur: u16,
    data: T,
}

impl<T> Cleanup<T> {
    fn with_max(data: T, max: u16) -> Self {
        Self { max, cur: 0, data }
    }

    pub fn new(data: T) -> Self {
        Self::with_max(data, 100)
    }

    fn next(&mut self) -> bool {
        self.cur += 1;
        if self.cur < self.max {
            false
        } else {
            self.cur = 0;
            true
        }
    }

    pub fn maybe_clean<R, F: FnMut(&mut T) -> R>(&mut self, mut f: F) -> Option<R> {
        if self.next() {
            Some(f(&mut self.data))
        } else {
            None
        }
    }
}

impl<T: Default> Default for Cleanup<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T> Deref for Cleanup<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<T> DerefMut for Cleanup<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test1() {
        let mut x = Cleanup::with_max(0, 3);
        x.maybe_clean(|x| *x += 1);
        x.maybe_clean(|x| *x += 1);
        x.maybe_clean(|x| *x += 1);
        assert_eq!(*x, 1);
    }

    #[test]
    fn test2() {
        let mut x = Cleanup::with_max(0, 0);
        for _ in 0..100 {
            x.maybe_clean(|x| *x += 1);
        }
        assert_eq!(*x, 100);
    }

    #[test]
    fn test3() {
        let mut x = Cleanup::with_max(0, 1);
        for _ in 0..100 {
            x.maybe_clean(|x| *x += 1);
        }
        assert_eq!(*x, 100);
    }

    #[test]
    fn test4() {
        let mut x = Cleanup::with_max(0, 2);
        for _ in 0..100 {
            x.maybe_clean(|x| *x += 1);
        }
        assert_eq!(*x, 50);
    }

    #[test]
    fn test5() {
        let mut x = Cleanup::with_max(0, 10);
        for _ in 0..100 {
            x.maybe_clean(|x| *x += 1);
        }
        assert_eq!(*x, 10);
    }
}
