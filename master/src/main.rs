// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

mod cli;
mod config;
mod logger;
mod master_server;

use log::error;

fn main() {
    let cli = cli::parse().unwrap_or_else(|e| {
        eprintln!("{}", e);
        std::process::exit(1);
    });

    let mut cfg = config::load(cli.config_path.as_ref()).unwrap_or_else(|e| {
        eprintln!("Failed to load config \"{}\": {}", cli.config_path, e);
        std::process::exit(1);
    });

    if let Some(level) = cli.log_level {
        cfg.log.level = level;
    }

    if let Some(ip) = cli.listen_ip {
        cfg.server.ip = ip;
    }

    if let Some(port) = cli.listen_port {
        cfg.server.port = port;
    }

    logger::init(cfg.log.level);

    if let Err(e) = master_server::run(cfg) {
        error!("{}", e);
        std::process::exit(1);
    }
}
