use std::{
    fmt::{self, Write},
    sync::{
        atomic::{AtomicBool, AtomicU32, AtomicUsize, Ordering, Ordering::Relaxed},
        mpsc, Arc,
    },
    thread,
    time::{Duration, Instant},
};

use crate::config::StatConfig;

enum Metric {
    Count(usize),
    PerSecond(u32),
    PerInterval(u32),
}

#[derive(Default)]
struct Counters {
    servers: AtomicUsize,
    server_challenge: AtomicU32,
    server_add: AtomicU32,
    server_del: AtomicU32,
    query_servers: AtomicU32,
    query_info: AtomicU32,
    errors: AtomicU32,
}

impl Counters {
    fn get_metric(&self, c: char) -> Option<Metric> {
        Some(match c {
            's' => Metric::Count(self.servers.load(Ordering::Relaxed)),
            'c' => Metric::PerSecond(self.server_challenge.load(Ordering::Relaxed)),
            'a' => Metric::PerSecond(self.server_add.load(Ordering::Relaxed)),
            'd' => Metric::PerSecond(self.server_del.load(Ordering::Relaxed)),
            'q' => Metric::PerSecond(self.query_servers.load(Ordering::Relaxed)),
            'i' => Metric::PerSecond(self.query_info.load(Ordering::Relaxed)),
            'e' => Metric::PerSecond(self.errors.load(Ordering::Relaxed)),
            'C' => Metric::PerInterval(self.server_challenge.load(Ordering::Relaxed)),
            'A' => Metric::PerInterval(self.server_add.load(Ordering::Relaxed)),
            'D' => Metric::PerInterval(self.server_del.load(Ordering::Relaxed)),
            'Q' => Metric::PerInterval(self.query_servers.load(Ordering::Relaxed)),
            'I' => Metric::PerInterval(self.query_info.load(Ordering::Relaxed)),
            'E' => Metric::PerInterval(self.errors.load(Ordering::Relaxed)),
            _ => return None,
        })
    }

    fn print(&self, mut format: &str, buf: &mut String, time: Duration) -> fmt::Result {
        let time = time.as_secs_f64();

        loop {
            // TODO: precompile format string
            match format.find('%').map(|i| format.split_at(i)) {
                Some((head, tail)) => {
                    format = &tail[1..];
                    write!(buf, "{head}")?;
                    let mut chars = format.char_indices();
                    match chars.next().map(|(_, c)| c) {
                        Some('s') => {
                            write!(buf, "{}", self.servers.load(Ordering::Relaxed))?;
                        }
                        Some(c) => match self.get_metric(c) {
                            Some(Metric::Count(value)) => {
                                write!(buf, "{value}")?;
                            }
                            Some(Metric::PerSecond(value)) => {
                                write!(buf, "{:.1}", value as f64 / time)?;
                            }
                            Some(Metric::PerInterval(value)) => {
                                write!(buf, "{value}")?;
                            }
                            None => {
                                write!(buf, "%{c}")?;
                            }
                        },
                        None => write!(buf, "%")?,
                    }
                    match chars.next() {
                        Some((i, _)) => format = &format[i..],
                        None => break,
                    }
                }
                None => {
                    write!(buf, "{format}")?;
                    break;
                }
            }
        }

        // reset counters
        let Self {
            servers: _,
            server_challenge,
            server_add,
            server_del,
            query_servers,
            query_info,
            errors,
        } = self;

        server_challenge.store(0, Relaxed);
        server_add.store(0, Relaxed);
        server_del.store(0, Relaxed);
        query_servers.store(0, Relaxed);
        query_info.store(0, Relaxed);
        errors.store(0, Relaxed);

        Ok(())
    }

    fn clear(&self) {
        let Self {
            servers,
            server_challenge,
            server_add,
            server_del,
            query_servers,
            query_info,
            errors,
        } = self;

        servers.store(0, Relaxed);
        server_challenge.store(0, Relaxed);
        server_add.store(0, Relaxed);
        server_del.store(0, Relaxed);
        query_servers.store(0, Relaxed);
        query_info.store(0, Relaxed);
        errors.store(0, Relaxed);
    }
}

pub struct Stats {
    enabled: AtomicBool,
    tx: mpsc::Sender<StatConfig>,
    counters: Arc<Counters>,
}

macro_rules! impl_counter_inc {
    ($vis:vis fn $meth:ident = $field:ident) => {
        $vis fn $meth(&self) {
            if self.enabled() {
                self.counters.$field.fetch_add(1, Relaxed);
            }
        }
    }
}

impl Stats {
    pub fn new(mut config: StatConfig) -> Self {
        let counters_ = Arc::new(Counters::default());
        let (tx, rx) = mpsc::channel();

        let enabled = AtomicBool::new(config.interval != 0);
        let counters = counters_.clone();
        thread::spawn(move || -> fmt::Result {
            let buf = &mut String::new();

            loop {
                if config.interval == 0 {
                    config = rx.recv().unwrap();
                    counters.clear();
                    continue;
                }

                let duration = Duration::from_secs(config.interval as u64);
                let start = Instant::now();
                if let Ok(new_config) = rx.recv_timeout(duration) {
                    config = new_config;
                    continue;
                }

                buf.clear();
                counters.print(&config.format, buf, start.elapsed())?;
                info!("{}", buf);
            }
        });

        Self {
            enabled,
            tx,
            counters: counters_,
        }
    }

    pub fn update_config(&self, config: StatConfig) {
        self.enabled.store(config.interval != 0, Ordering::Release);
        self.tx.send(config).unwrap();
    }

    pub fn clear(&self) {
        self.counters.clear();
    }

    #[inline(always)]
    fn enabled(&self) -> bool {
        self.enabled.load(Ordering::Acquire)
    }

    pub fn servers_count(&self, n: usize) {
        if self.enabled() {
            self.counters.servers.store(n, Relaxed);
        }
    }

    impl_counter_inc!(pub fn on_server_challenge = server_challenge);
    impl_counter_inc!(pub fn on_server_add = server_add);
    impl_counter_inc!(pub fn on_server_del = server_del);
    impl_counter_inc!(pub fn on_query_servers = query_servers);
    impl_counter_inc!(pub fn on_query_info = query_info);
    impl_counter_inc!(pub fn on_error = errors);
}
