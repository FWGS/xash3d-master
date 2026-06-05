use std::{
    fmt::{self, Write},
    time::Duration,
};

enum Metric {
    Count(u64),
    PerSecond(u64),
    PerInterval(u64),
}

#[derive(Default, Debug)]
pub struct Counters {
    pub servers: u64,
    pub server_challenge: u64,
    pub server_add: u64,
    pub server_del: u64,
    pub query_servers: u64,
    pub query_info: u64,
    pub errors: u64,
}

pub struct Stats<'a> {
    format: &'a str,
    interval: f64,
    prev: Counters,
}

impl<'a> Stats<'a> {
    pub fn new(format: &'a str, interval: Duration, counters: Counters) -> Self {
        Self {
            format,
            interval: interval.as_secs_f64(),
            prev: counters,
        }
    }

    fn get_metric(&self, counters: &Counters, c: char) -> Option<Metric> {
        macro_rules! delta {
            ($counter:ident) => {
                counters.$counter.saturating_sub(self.prev.$counter)
            };
        }

        Some(match c {
            's' => Metric::Count(counters.servers),
            'c' => Metric::PerSecond(delta!(server_challenge)),
            'a' => Metric::PerSecond(delta!(server_add)),
            'd' => Metric::PerSecond(delta!(server_del)),
            'q' => Metric::PerSecond(delta!(query_servers)),
            'i' => Metric::PerSecond(delta!(query_info)),
            'e' => Metric::PerSecond(delta!(errors)),
            'C' => Metric::PerInterval(delta!(server_challenge)),
            'A' => Metric::PerInterval(delta!(server_add)),
            'D' => Metric::PerInterval(delta!(server_del)),
            'Q' => Metric::PerInterval(delta!(query_servers)),
            'I' => Metric::PerInterval(delta!(query_info)),
            'E' => Metric::PerInterval(delta!(errors)),
            _ => return None,
        })
    }

    fn print(&self, counters: &Counters) -> fmt::Result {
        let mut buf = String::with_capacity(256);
        let mut format = self.format;
        loop {
            // TODO: precompile format string
            match format.find('%').map(|i| format.split_at(i)) {
                Some((head, tail)) => {
                    format = &tail[1..];
                    write!(buf, "{head}")?;
                    let mut chars = format.char_indices();
                    match chars.next().map(|(_, c)| c) {
                        Some(c) => match self.get_metric(counters, c) {
                            Some(Metric::Count(value)) => {
                                write!(buf, "{value}")?;
                            }
                            Some(Metric::PerSecond(value)) => {
                                write!(buf, "{:.1}", value as f64 / self.interval)?;
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

        info!("{buf}");

        Ok(())
    }

    pub fn update(&mut self, counters: Counters) {
        if self.print(&counters).is_err() {
            error!("failed to print stats");
        }
        self.prev = counters;
    }
}
