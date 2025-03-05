use std::ops::{Deref, DerefMut};

/// Helper wrapper to periodically execute an action.
pub struct Periodic<T> {
    limit: u16,
    cur: u16,
    data: T,
}

impl<T> Periodic<T> {
    /// Default limit.
    pub const DEFAULT_LIMIT: u16 = 100;

    /// Wraps `data` with a default limit.
    pub fn new(data: T) -> Self {
        Self::with_limit(data, Self::DEFAULT_LIMIT)
    }

    /// Wraps `data`.
    pub fn with_limit(data: T, limit: u16) -> Self {
        Self {
            limit,
            cur: 0,
            data,
        }
    }

    /// Increase the counter.
    ///
    /// Returns true if the counter has reached the limit.
    fn next(&mut self) -> bool {
        self.cur += 1;
        if self.cur < self.limit {
            false
        } else {
            self.cur = 0;
            true
        }
    }

    /// Increase a counter and execute a function if it has reached the limit.
    ///
    /// Resets the counter if the function was executed.
    pub fn maybe_run<R, F: FnMut(&mut T) -> R>(&mut self, mut f: F) -> Option<R> {
        if self.next() {
            Some(f(&mut self.data))
        } else {
            None
        }
    }
}

impl<T: Default> Default for Periodic<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T> Deref for Periodic<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<T> DerefMut for Periodic<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test1() {
        let mut x = Periodic::with_limit(0, 3);
        x.maybe_run(|x| *x += 1);
        x.maybe_run(|x| *x += 1);
        x.maybe_run(|x| *x += 1);
        assert_eq!(*x, 1);
    }

    #[test]
    fn test2() {
        let mut x = Periodic::with_limit(0, 0);
        for _ in 0..100 {
            x.maybe_run(|x| *x += 1);
        }
        assert_eq!(*x, 100);
    }

    #[test]
    fn test3() {
        let mut x = Periodic::with_limit(0, 1);
        for _ in 0..100 {
            x.maybe_run(|x| *x += 1);
        }
        assert_eq!(*x, 100);
    }

    #[test]
    fn test4() {
        let mut x = Periodic::with_limit(0, 2);
        for _ in 0..100 {
            x.maybe_run(|x| *x += 1);
        }
        assert_eq!(*x, 50);
    }

    #[test]
    fn test5() {
        let mut x = Periodic::with_limit(0, 10);
        for _ in 0..100 {
            x.maybe_run(|x| *x += 1);
        }
        assert_eq!(*x, 10);
    }
}
