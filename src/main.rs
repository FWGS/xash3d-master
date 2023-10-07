// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

mod cli;
mod client;
mod filter;
mod logger;
mod master_server;
mod parser;
mod server;
mod server_info;

use log::error;

fn main() {
    let cli = cli::parse().unwrap_or_else(|e| {
        eprintln!("{}", e);
        std::process::exit(1);
    });

    logger::init(cli.log_level);

    if let Err(e) = master_server::run(cli.listen) {
        error!("{}", e);
        std::process::exit(1);
    }
}
