use std::{
    ffi::c_int,
    io,
    marker::PhantomData,
    sync::atomic::{AtomicBool, AtomicU32, Ordering},
    thread,
    time::{Duration, Instant},
};

use bitflags::bitflags;
use signal_hook::{consts::signal::*, SigId};

bitflags! {
    #[derive(Copy, Clone)]
    struct Flags: u32 {
        const EXIT = 1 << 0;
        const RELOAD_CONFIG = 1 << 1;
    }
}

static INITIALIZED: AtomicBool = AtomicBool::new(false);
static SIGNAL_FLAGS: AtomicU32 = AtomicU32::new(0);
static STOP: AtomicBool = AtomicBool::new(false);

#[derive(Copy, Clone)]
pub struct SignalFlags(());

impl SignalFlags {
    pub const fn get() -> Self {
        Self(())
    }

    fn load(&self) -> Flags {
        let bits = SIGNAL_FLAGS.load(Ordering::Acquire);
        Flags::from_bits_retain(bits)
    }

    fn remove(&self, flags: Flags) -> Flags {
        let bits = SIGNAL_FLAGS.fetch_and(!flags.bits(), Ordering::SeqCst);
        Flags::from_bits_retain(bits)
    }

    pub fn is_exit(&self) -> bool {
        self.load().intersects(Flags::EXIT)
    }

    pub fn remove_reload(&self) -> bool {
        self.remove(Flags::RELOAD_CONFIG)
            .intersects(Flags::RELOAD_CONFIG)
    }

    pub fn is_empty(&self) -> bool {
        self.load().is_empty()
    }
}

pub struct Signals {
    // prevent auto-impl Send and Sync markers
    phantom: PhantomData<*mut ()>,
}

impl Signals {
    fn register_flag(&self, signal: c_int, flags: Flags) -> io::Result<SigId> {
        let flags = flags.bits();
        let thread = thread::current();
        #[allow(unsafe_code)]
        // SAFETY: Used atomic operations and thread unpack which is implemented via futexes.
        let signal_id = unsafe {
            signal_hook::low_level::register(signal, move || {
                SIGNAL_FLAGS.fetch_or(flags, Ordering::SeqCst);
                if !STOP.swap(true, Ordering::SeqCst) {
                    thread.unpark();
                }
            })?
        };
        Ok(signal_id)
    }

    fn register(&self) -> io::Result<()> {
        #[cfg(not(windows))]
        {
            self.register_flag(SIGINT, Flags::EXIT)?;
            self.register_flag(SIGTERM, Flags::EXIT)?;
            self.register_flag(SIGUSR1, Flags::RELOAD_CONFIG)?;
        }

        #[cfg(windows)]
        {
            self.register_flag(SIGINT, Flags::EXIT)?;
            self.register_flag(SIGTERM, Flags::EXIT)?;
            self.register_flag(SIGBREAK, Flags::RELOAD_CONFIG)?;
        }

        Ok(())
    }

    /// Initialize signal handlers.
    pub fn init() -> io::Result<Self> {
        assert!(!INITIALIZED.swap(false, Ordering::SeqCst));

        let ret = Self {
            phantom: PhantomData,
        };
        ret.register()?;
        Ok(ret)
    }

    pub fn wait(&self) {
        while !STOP.load(Ordering::SeqCst) {
            thread::park();
        }
        STOP.store(false, Ordering::SeqCst);
    }

    pub fn wait_timeout(&self, dur: Duration) -> bool {
        let start = Instant::now();
        let mut remaining = dur;
        while !STOP.load(Ordering::SeqCst) {
            thread::park_timeout(remaining);
            if let Some(r) = dur.checked_sub(start.elapsed()) {
                remaining = r;
            } else {
                break;
            }
        }
        !STOP.swap(false, Ordering::SeqCst)
    }
}
