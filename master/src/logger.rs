// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

use log::{Metadata, Record};

use crate::config::LogConfig;

#[derive(Default)]
pub struct LoggerOptions {
    print_time: AtomicBool,
}

impl LoggerOptions {
    pub fn update_config(&self, cfg: &LogConfig) {
        log::set_max_level(cfg.level);
        self.print_time.store(cfg.time, Ordering::Relaxed);
    }
}

#[derive(Default)]
struct Logger {
    opts: Arc<LoggerOptions>,
}

impl log::Log for Logger {
    fn enabled(&self, _metadata: &Metadata) -> bool {
        true
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            #[cfg(feature = "logtime")]
            if self.opts.print_time.load(Ordering::Relaxed) {
                let dt = chrono::Local::now().format("%Y-%m-%d %H:%M:%S");
                println!("[{}] {} - {}", dt, record.level(), record.args());
                return;
            }

            println!("{} - {}", record.level(), record.args());
        }
    }

    fn flush(&self) {}
}

pub fn init() -> Arc<LoggerOptions> {
    let logger = Box::new(Logger::default());
    let opts = logger.opts.clone();
    if let Err(e) = log::set_boxed_logger(logger) {
        eprintln!("Failed to initialize logger: {}", e);
    }
    opts
}
