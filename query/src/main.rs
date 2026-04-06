// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

mod cli;
mod color;
mod server_info;
mod server_result;

// commands
mod list_servers;
mod monitor_servers;
mod query_servers_info;

use std::{io, process};

use thiserror::Error;
use xash3d_observer::{Handler, Observer, ObserverBuilder};
use xash3d_protocol::Error as ProtocolError;

use crate::cli::Cli;

#[derive(Error, Debug)]
enum QueryError {
    #[error("Undefined command")]
    UndefinedCommand,
    #[error(transparent)]
    Protocol(#[from] ProtocolError),
    #[error(transparent)]
    Io(#[from] io::Error),
}

fn create_observer<T: Handler>(cli: &Cli, handler: T) -> io::Result<Observer<T>> {
    ObserverBuilder::new()
        .filter(&cli.filter)
        .build(handler, cli.masters.as_slice())
}

fn execute(cli: Cli) -> Result<(), QueryError> {
    match cli.args.first().map(|s| s.as_str()).unwrap_or_default() {
        "all" | "" => query_servers_info::run(&cli, &[])?,
        "info" => {
            if cli.args.len() > 1 {
                query_servers_info::run(&cli, &cli.args[1..])?;
            }
        }
        "list" => list_servers::run(&cli)?,
        "monitor" => monitor_servers::run(&cli)?,
        _ => return Err(QueryError::UndefinedCommand),
    }
    Ok(())
}

fn main() {
    let cli = cli::parse();

    #[cfg(not(windows))]
    unsafe {
        // suppress broken pipe error
        libc::signal(libc::SIGPIPE, libc::SIG_DFL);
    }

    if let Err(e) = execute(cli) {
        eprintln!("error: {e}");
        process::exit(1);
    }
}
