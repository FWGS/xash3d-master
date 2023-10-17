// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use log::{LevelFilter, Metadata, Record};

struct Logger;

impl Logger {}

impl log::Log for Logger {
    fn enabled(&self, _metadata: &Metadata) -> bool {
        true
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            #[cfg(not(feature = "logtime"))]
            println!("{} - {}", record.level(), record.args());

            #[cfg(feature = "logtime")]
            {
                let dt = chrono::Local::now().format("%Y-%m-%d %H:%M:%S");
                println!("[{}] {} - {}", dt, record.level(), record.args());
            }
        }
    }

    fn flush(&self) {}
}

static LOGGER: Logger = Logger;

pub fn init(level_filter: LevelFilter) {
    if let Err(e) = log::set_logger(&LOGGER) {
        eprintln!("Failed to initialize logger: {}", e);
    }
    log::set_max_level(level_filter);
}
