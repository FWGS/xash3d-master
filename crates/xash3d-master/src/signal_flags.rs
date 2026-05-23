use std::{
    ffi::c_int,
    sync::{
        atomic::{AtomicU32, Ordering},
        OnceLock,
    },
};

use bitflags::bitflags;
use signal_hook::{consts::signal::*, SigId};

use crate::master_server::Error;

bitflags! {
    #[derive(Copy, Clone)]
    struct Flags: u32 {
        const EXIT = 1 << 0;
        const RELOAD_CONFIG = 1 << 1;
    }
}

static SIGNAL_FLAGS: AtomicU32 = AtomicU32::new(0);
static SIGNAL_FLAGS_INIT: OnceLock<()> = OnceLock::new();

#[derive(Copy, Clone)]
pub struct SignalFlags(());

impl SignalFlags {
    pub const fn get() -> Self {
        Self(())
    }

    fn register_flag(&self, signal: c_int, flags: Flags) -> Result<SigId, Error> {
        let flags = flags.bits();
        #[allow(unsafe_code)]
        // SAFETY: Only a single atomic operation is used.
        let signal_id = unsafe {
            signal_hook::low_level::register(signal, move || {
                SIGNAL_FLAGS.fetch_or(flags, Ordering::SeqCst);
            })?
        };
        Ok(signal_id)
    }

    fn register(&self) -> Result<(), Error> {
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

    pub fn init() -> Result<Self, Error> {
        let mut result = None;
        SIGNAL_FLAGS_INIT.get_or_init(|| {
            result = Some(Self::get().register());
        });
        result.unwrap_or(Ok(())).map(|_| Self::get())
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
