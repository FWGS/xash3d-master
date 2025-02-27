use std::time::Instant;

pub struct RelativeTimer {
    start: Instant,
}

impl RelativeTimer {
    pub fn new() -> Self {
        RelativeTimer {
            start: Instant::now(),
        }
    }

    pub fn now(&self) -> u32 {
        self.start.elapsed().as_secs() as u32
    }
}

impl Default for RelativeTimer {
    fn default() -> Self {
        Self::new()
    }
}
