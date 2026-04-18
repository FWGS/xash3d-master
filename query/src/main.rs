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

use std::{io::{self, Write}, net::SocketAddr, process};

use serde::Serialize;
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

fn observer_builder<'a>(cli: &'a Cli) -> ObserverBuilder<'a> {
    ObserverBuilder::new().filter(&cli.filter)
}

fn create_observer<T: Handler>(cli: &Cli, handler: T) -> io::Result<Observer<T>> {
    observer_builder(cli).build(handler, cli.masters.as_slice())
}

/// Same as [create_observer] but without master servers.
fn create_observer_no_masters<T: Handler>(cli: &Cli, handler: T) -> io::Result<Observer<T>> {
    observer_builder(cli).build(handler, &[] as &[&str])
}

fn parse_server_addresses(servers: &[String]) -> Vec<SocketAddr> {
    let mut list = Vec::with_capacity(servers.len());
    for i in servers {
        match i.parse() {
            Ok(addr) => list.push(addr),
            Err(_) => eprintln!("invalid address {i}"),
        }
    }
    if servers.len() != list.len() {
        process::exit(1);
    }
    list.sort_unstable();
    list.dedup();
    list
}

fn print_json<T: Serialize>(cli: &Cli, value: &T) {
    let print = if !cli.compact {
        serde_json::to_writer_pretty
    } else {
        serde_json::to_writer
    };
    let mut stdout = io::stdout().lock();
    print(&mut stdout, value).unwrap();
    stdout.write_all(b"\n").unwrap();
    stdout.flush().unwrap();
}

fn execute(cli: Cli) -> Result<(), QueryError> {
    match cli.args.first().map(|s| s.as_str()).unwrap_or_default() {
        "all" | "" => query_servers_info::run_all(&cli)?,
        "info" => {
            let list = parse_server_addresses(&cli.args[1..]);
            query_servers_info::run_custom_servers(&cli, list)?;
        }
        "list" => list_servers::run(&cli)?,
        "monitor" => {
            let list = parse_server_addresses(&cli.args[1..]);
            monitor_servers::run(&cli, list)?;
        }
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
