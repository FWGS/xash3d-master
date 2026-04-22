use log::{LevelFilter, Log, Metadata, Record};

use crate::cli::Cli;

struct Logger;

impl Log for Logger {
    fn enabled(&self, _metadata: &Metadata) -> bool {
        true
    }

    fn log(&self, record: &Record) {
        if !self.enabled(record.metadata()) {
            return;
        }

        eprintln!(
            "[{}] {}: {}",
            record.level(),
            record.target(),
            record.args()
        );
    }

    fn flush(&self) {}
}

pub fn init(cli: &Cli) {
    static LOGGER: Logger = Logger;

    if cli.log == LevelFilter::Off {
        return;
    }

    log::set_max_level(cli.log);

    if let Err(err) = log::set_logger(&LOGGER) {
        eprintln!("failed to initialize logger: {err}");
    }
}
