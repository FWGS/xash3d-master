// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

#![deny(unsafe_code)]

mod cli;
mod config;
mod logger;
mod master_server;
mod stats;

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

use crate::cli::Cli;
use crate::config::Config;
use crate::master_server::{Error, Master};

fn load_config(cli: &Cli) -> Result<Config, config::Error> {
    let mut cfg = match cli.config_path {
        Some(ref p) => config::load(p.as_ref())?,
        None => Config::default(),
    };

    if let Some(level) = cli.log_level {
        cfg.log.level = level;
    }
    if let Some(ip) = cli.listen_ip {
        cfg.server.ip = ip;
    }
    if let Some(port) = cli.listen_port {
        cfg.server.port = port;
    }
    if let Some(format) = &cli.stats_format {
        cfg.stat.format = format.clone();
    }
    if let Some(interval) = cli.stats_interval {
        cfg.stat.interval = interval;
    }

    log::set_max_level(cfg.log.level);

    Ok(cfg)
}

fn run() -> Result<(), Error> {
    let cli = cli::parse().unwrap_or_else(|e| {
        eprintln!("{}", e);
        std::process::exit(1);
    });

    logger::init();

    let cfg = load_config(&cli).unwrap_or_else(|e| {
        match cli.config_path.as_deref() {
            Some(p) => eprintln!("Failed to load config \"{}\": {}", p, e),
            None => eprintln!("{}", e),
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

                match load_config(&cli) {
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
