use std::{
    sync::OnceLock,
    time::{Duration, Instant},
};

/// A time relative to the startup of the program.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct RelativeTime(u32);

impl RelativeTime {
    // 125ms units provide ~17 years of uptime without overflow
    const MILLIS_PER_UNIT: u64 = 125;
    const UNITS_PER_SEC: u64 = 1000 / Self::MILLIS_PER_UNIT; // 8

    fn from_millis(ms: u64) -> Self {
        Self((ms / Self::UNITS_PER_SEC) as u32)
    }

    fn as_millis(&self) -> u64 {
        (self.0 as u64) * Self::UNITS_PER_SEC
    }

    /// Returns current relative time.
    pub fn now() -> Self {
        static TIMER: OnceLock<Instant> = OnceLock::new();
        Self::from_millis(TIMER.get_or_init(Instant::now).elapsed().as_millis() as u64)
    }

    /// Returns the amount of time elapsed from another time to this one.
    ///
    /// Returns zero if `earlier` is later than this time.
    pub fn duration_since(&self, earlier: Self) -> Duration {
        Duration::from_millis(self.as_millis().saturating_sub(earlier.as_millis()))
    }
}
