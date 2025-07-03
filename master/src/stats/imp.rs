use std::fmt::{self, Write};
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering::Relaxed};
use std::sync::mpsc;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use log::info;

use crate::config::StatConfig;

#[derive(Default)]
struct Counters {
    servers: AtomicUsize,
    server_add: AtomicU32,
    server_del: AtomicU32,
    query_servers: AtomicU32,
    errors: AtomicU32,
}

impl Counters {
    fn print(&self, mut format: &str, buf: &mut String, time: Duration) -> fmt::Result {
        let time = time.as_secs_f64();
        let servers = self.servers.load(Relaxed);
        let server_add = self.server_add.swap(0, Relaxed);
        let server_del = self.server_del.swap(0, Relaxed);
        let query_servers = self.query_servers.swap(0, Relaxed);
        let errors = self.errors.swap(0, Relaxed);

        loop {
            // TODO: precompile format string
            match format.find('%').map(|i| format.split_at(i)) {
                Some((head, tail)) => {
                    format = &tail[1..];
                    write!(buf, "{head}")?;
                    let mut chars = format.char_indices();
                    match chars.next().map(|(_, c)| c) {
                        Some('s') => write!(buf, "{servers}")?,
                        Some('A') => write!(buf, "{server_add}")?,
                        Some('D') => write!(buf, "{server_del}")?,
                        Some('Q') => write!(buf, "{query_servers}")?,
                        Some('E') => write!(buf, "{errors}")?,
                        Some('a') => write!(buf, "{:.1}", server_add as f64 / time)?,
                        Some('d') => write!(buf, "{:.1}", server_del as f64 / time)?,
                        Some('q') => write!(buf, "{:.1}", query_servers as f64 / time)?,
                        Some('e') => write!(buf, "{:.1}", errors as f64 / time)?,
                        Some(c) => write!(buf, "%{c}")?,
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

        Ok(())
    }

    fn clear(&self) {
        self.servers.store(0, Relaxed);
        self.server_add.store(0, Relaxed);
        self.server_del.store(0, Relaxed);
        self.query_servers.store(0, Relaxed);
        self.errors.store(0, Relaxed);
    }
}

pub struct Stats {
    enabled: bool,
    tx: mpsc::Sender<StatConfig>,
    counters: Arc<Counters>,
}

impl Stats {
    pub fn new(mut config: StatConfig) -> Self {
        let counters_ = Arc::new(Counters::default());
        let (tx, rx) = mpsc::channel();

        let enabled = config.interval != 0;
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

    pub fn update_config(&mut self, config: StatConfig) {
        self.enabled = config.interval != 0;
        self.tx.send(config).unwrap();
    }

    pub fn clear(&self) {
        self.counters.clear();
    }

    pub fn servers_count(&self, n: usize) {
        if self.enabled {
            self.counters.servers.store(n, Relaxed);
        }
    }

    pub fn on_server_add(&self) {
        if self.enabled {
            self.counters.server_add.fetch_add(1, Relaxed);
        }
    }

    pub fn on_server_del(&self) {
        if self.enabled {
            self.counters.server_del.fetch_add(1, Relaxed);
        }
    }

    pub fn on_query_servers(&self) {
        if self.enabled {
            self.counters.query_servers.fetch_add(1, Relaxed);
        }
    }

    pub fn on_error(&self) {
        if self.enabled {
            self.counters.errors.fetch_add(1, Relaxed);
        }
    }
}
