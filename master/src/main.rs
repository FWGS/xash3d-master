// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

mod cli;
mod config;
mod logger;
mod master_server;

use std::process;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use log::{error, info};
use signal_hook::consts::signal::*;
use signal_hook::flag as signal_flag;

use crate::cli::Cli;
use crate::config::Config;
use crate::master_server::{Error, MasterServer};

fn load_config(cli: &Cli) -> Result<Config, config::Error> {
    let mut cfg = config::load(cli.config_path.as_ref())?;

    if let Some(level) = cli.log_level {
        cfg.log.level = level;
    }
    if let Some(ip) = cli.listen_ip {
        cfg.server.ip = ip;
    }
    if let Some(port) = cli.listen_port {
        cfg.server.port = port;
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
        eprintln!("Failed to load config \"{}\": {}", cli.config_path, e);
        process::exit(1);
    });

    let mut master = MasterServer::new(cfg)?;
    let sig_flag = Arc::new(AtomicBool::new(false));
    signal_flag::register(SIGUSR1, sig_flag.clone())?;

    loop {
        master.run(&sig_flag)?;

        if sig_flag.swap(false, Ordering::Relaxed) {
            info!("Reloading config from {}", cli.config_path);

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

fn main() {
    if let Err(e) = run() {
        error!("{}", e);
        process::exit(1);
    }
}
