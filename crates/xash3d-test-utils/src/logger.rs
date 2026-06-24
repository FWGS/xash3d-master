pub fn init_logger() {
    struct Logger;

    impl log::Log for Logger {
        fn enabled(&self, _metadata: &log::Metadata) -> bool {
            true
        }

        fn log(&self, record: &log::Record) {
            println!("{} - {}", record.level(), record.args());
        }

        fn flush(&self) {}
    }

    static LOGGER: Logger = Logger;

    log::set_logger(&LOGGER).ok();
    log::set_max_level(log::LevelFilter::Trace);
}
