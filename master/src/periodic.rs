/// Helper wrapper to periodically execute an action.
pub struct Periodic {
    limit: u16,
    cur: u16,
}

impl Periodic {
    /// Default limit.
    pub const DEFAULT_LIMIT: u16 = 100;

    pub fn new() -> Self {
        Self::with_limit(Periodic::DEFAULT_LIMIT)
    }

    pub fn with_limit(limit: u16) -> Self {
        Self { limit, cur: 0 }
    }

    /// Increase the counter.
    ///
    /// Returns true if the counter has reached the limit.
    pub fn next(&mut self) -> bool {
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
    pub fn maybe_run<R, F: FnMut() -> R>(&mut self, mut f: F) -> Option<R> {
        if self.next() {
            Some(f())
        } else {
            None
        }
    }
}

impl Default for Periodic {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test1() {
        let mut p = Periodic::with_limit(3);
        let mut x = 0;
        p.maybe_run(|| x += 1);
        p.maybe_run(|| x += 1);
        p.maybe_run(|| x += 1);
        assert_eq!(x, 1);
    }

    #[test]
    fn test2() {
        let mut p = Periodic::with_limit(0);
        let mut x = 0;
        for _ in 0..100 {
            p.maybe_run(|| x += 1);
        }
        assert_eq!(x, 100);
    }

    #[test]
    fn test3() {
        let mut p = Periodic::with_limit(1);
        let mut x = 0;
        for _ in 0..100 {
            p.maybe_run(|| x += 1);
        }
        assert_eq!(x, 100);
    }

    #[test]
    fn test4() {
        let mut p = Periodic::with_limit(2);
        let mut x = 0;
        for _ in 0..100 {
            p.maybe_run(|| x += 1);
        }
        assert_eq!(x, 50);
    }

    #[test]
    fn test5() {
        let mut p = Periodic::with_limit(10);
        let mut x = 0;
        for _ in 0..100 {
            p.maybe_run(|| x += 1);
        }
        assert_eq!(x, 10);
    }
}
