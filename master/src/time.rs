use std::{
    sync::OnceLock,
    time::{Duration, Instant},
};

/// A time relative to the startup of the program.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct RelativeTime(u32);

impl RelativeTime {
    /// Returns current relative time.
    pub fn now() -> Self {
        static TIMER: OnceLock<Instant> = OnceLock::new();
        Self(TIMER.get_or_init(Instant::now).elapsed().as_secs() as u32)
    }

    /// Returns the amount of time elapsed from another time to this one.
    ///
    /// Returns zero if `earlier` is later than this time.
    pub fn duration_since(&self, earlier: Self) -> Duration {
        Duration::from_secs(self.0.saturating_sub(earlier.0) as u64)
    }
}
