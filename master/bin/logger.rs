// SPDX-License-Identifier: GPL-3.0-only

use std::sync::atomic::{AtomicBool, Ordering};

use log::{Metadata, Record};
use xash3d_master::config::LogConfig;

pub struct Logger {
    print_time: AtomicBool,
}

impl Logger {
    const fn new() -> Logger {
        Self {
            print_time: AtomicBool::new(true),
        }
    }

    pub fn update_config(&self, cfg: &LogConfig) {
        log::set_max_level(cfg.level);
        self.print_time.store(cfg.time, Ordering::Relaxed);
    }
}

impl log::Log for Logger {
    fn enabled(&self, _metadata: &Metadata) -> bool {
        true
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            #[cfg(feature = "logtime")]
            if self.print_time.load(Ordering::Relaxed) {
                let dt = chrono::Local::now().format("%Y-%m-%d %H:%M:%S");
                println!("[{}] {} - {}", dt, record.level(), record.args());
                return;
            }

            println!("{} - {}", record.level(), record.args());
        }
    }

    fn flush(&self) {}
}

static LOGGER: Logger = Logger::new();

pub fn init() -> &'static Logger {
    if let Err(e) = log::set_logger(&LOGGER) {
        eprintln!("Failed to initialize logger: {}", e);
    }
    &LOGGER
}
