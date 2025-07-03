// SPDX-License-Identifier: GPL-3.0-only

#![deny(unsafe_code)]

mod cli;
mod logger;

use std::{
    process,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
};

use log::{error, info};
#[cfg(not(windows))]
use signal_hook::{consts::signal::*, flag as signal_flag};
use xash3d_master::{
    config::{self, Config},
    Error, Master,
};

use crate::{cli::Cli, logger::Logger};

fn load_config(cli: &Cli, logger: &Logger) -> Result<Config, config::Error> {
    let mut cfg = match cli.config_path {
        Some(ref p) => config::load(p.as_ref())?,
        None => Config::default(),
    };

    if let Some(level) = cli.log_level {
        cfg.log.level = level;
    }
    if let Some(ip) = cli.listen_ip {
        cfg.master.server.ip = ip;
    }
    if let Some(port) = cli.listen_port {
        cfg.master.server.port = port;
    }
    if let Some(format) = &cli.stats_format {
        cfg.stat.format = format.clone();
    }
    if let Some(interval) = cli.stats_interval {
        cfg.stat.interval = interval;
    }

    logger.update_config(&cfg.log);

    Ok(cfg)
}

fn run() -> Result<(), Error> {
    let cli = cli::parse().unwrap_or_else(|e| {
        eprintln!("{e}");
        std::process::exit(1);
    });

    let logger = logger::init();

    let cfg = load_config(&cli, logger).unwrap_or_else(|e| {
        match cli.config_path.as_deref() {
            Some(p) => eprintln!("Failed to load config \"{p}\": {e}"),
            None => eprintln!("{e}"),
        }
        process::exit(1);
    });

    let mut master = Master::new(cfg)?;
    let sig_flag = Arc::new(AtomicBool::new(false));
    // XXX: Windows does not support SIGUSR1.
    #[cfg(not(windows))]
    signal_flag::register(SIGUSR1, sig_flag.clone())?;

    loop {
        master.run(&sig_flag)?;

        if sig_flag.swap(false, Ordering::Relaxed) {
            if let Some(config_path) = cli.config_path.as_deref() {
                info!("Reloading config from {}", config_path);

                match load_config(&cli, logger) {
                    Ok(cfg) => {
                        if let Err(e) = master.update_config(cfg) {
                            error!("{}", e);
                        }
                    }
                    Err(e) => error!("failed to load config: {}", e),
                }
            }
        }
    }
}

fn main() {
    if let Err(e) = run() {
        error!("{}", e);
        process::exit(1);
    }
}
