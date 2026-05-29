use std::{process, thread};

use crate::{
    cli::{self, Cli},
    config::{self, Config},
    logger::{self, Logger},
    signals::{SignalFlags, Signals},
    udp_server::{UdpServer, UdpServerError},
    worker::Worker,
};

struct App {
    cli: Cli,
    logger: &'static Logger,
    signals: Signals,
    workers: Vec<Worker>,
}

impl App {
    fn new() -> Result<Self, UdpServerError> {
        let cli = cli::parse().unwrap_or_else(|e| {
            eprintln!("{e}");
            std::process::exit(1);
        });
        let logger = logger::init();
        let signals = Signals::init()?;
        Ok(Self {
            cli,
            logger,
            signals,
            workers: Vec::new(),
        })
    }

    fn load_config(&self) -> Result<Config, config::Error> {
        let mut cfg = match self.cli.config_path {
            Some(ref p) => config::load(p.as_ref())?,
            None => Config::default(),
        };

        if let Some(level) = self.cli.log_level {
            cfg.log.level = level;
        }
        if let Some(ip) = self.cli.listen_ip {
            cfg.master.server.ip = ip;
        }
        if let Some(port) = self.cli.listen_port {
            cfg.master.server.port = port;
        }
        if let Some(format) = &self.cli.stats_format {
            cfg.stat.format = format.clone();
        }
        if let Some(interval) = self.cli.stats_interval {
            cfg.stat.interval = interval;
        }

        self.logger.update_config(&cfg.log);

        Ok(cfg)
    }

    fn udp_server_update_config(&mut self, cfg: &Config) -> Result<(), UdpServerError> {
        let old_addr = self.workers[0].udp_server().local_addr()?;
        let new_addr = cfg.master.server.addr();
        if old_addr.is_ipv4() != new_addr.is_ipv4() {
            info!("UDP server IP version changed, full restart");
            for i in 0..self.workers.len() {
                let udp_server = if i == 0 {
                    UdpServer::new(cfg)?
                } else {
                    self.workers[0].udp_server().try_clone()?
                };
                self.workers[i].udp_server_replace(udp_server)?;
            }
        } else {
            for worker in self.workers.iter_mut() {
                worker.udp_server_update_config(cfg)?;
            }
        }
        Ok(())
    }

    fn run(&mut self) -> Result<(), UdpServerError> {
        let cfg = self.load_config().unwrap_or_else(|e| {
            match self.cli.config_path.as_deref() {
                Some(p) => eprintln!("Failed to load config \"{p}\": {e}"),
                None => eprintln!("{e}"),
            }
            process::exit(1);
        });

        for i in 0..self.cli.threads {
            let worker = if i == 0 {
                Worker::builder()?
                    .udp_server(UdpServer::new(&cfg)?)?
                    .build()
            } else {
                self.workers[0].try_clone()?
            };
            self.workers.push(worker);
        }

        let signal_flags = SignalFlags::get();
        while !signal_flags.is_exit() {
            info!("Starting {} workers", self.workers.len());

            thread::scope(|s| {
                let mut threads = Vec::with_capacity(self.workers.len());
                for worker in self.workers.iter_mut() {
                    let waker = worker.waker();
                    let th = s.spawn(move || worker.run());
                    threads.push((waker, th));
                }

                debug!("main: wait signals");
                self.signals.wait();

                debug!("main: stop workers");
                for (waker, _) in threads.iter() {
                    waker.wake()?;
                }

                debug!("main: wait workers to stop");
                for (_, th) in threads.drain(..) {
                    th.join().unwrap()?;
                }

                Ok::<_, UdpServerError>(())
            })?;

            if signal_flags.remove_reload() {
                if let Some(config_path) = self.cli.config_path.as_deref() {
                    info!("Reloading config from {}", config_path);

                    match self.load_config() {
                        Ok(cfg) => {
                            self.udp_server_update_config(&cfg)?;
                        }
                        Err(e) => error!("failed to load config: {}", e),
                    }
                }
            }
        }

        info!("Server stopped");
        Ok(())
    }
}

pub fn run() -> Result<(), UdpServerError> {
    App::new()?.run()
}
