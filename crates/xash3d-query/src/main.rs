mod cli;
mod color;
mod logger;
mod server_info;
mod server_result;
mod utils;

// commands
mod list_servers;
mod monitor_servers;
mod query_servers_info;

use std::{io, process};

use thiserror::Error;

use crate::{cli::Cli, utils::parse_server_addresses};

#[derive(Error, Debug)]
enum QueryError {
    #[error("Undefined command")]
    UndefinedCommand,
    #[error(transparent)]
    Io(#[from] io::Error),
}

fn execute(cli: Cli) -> Result<(), QueryError> {
    match cli.args.first().map(|s| s.as_str()).unwrap_or_default() {
        "all" | "" => {
            // Query info for all servers received from master servers.
            query_servers_info::run(&cli)?;
        }
        "info" => {
            // Query info for user specified servers.
            let list = parse_server_addresses(&cli.args[1..], cli.ip_version);
            query_servers_info::run_custom_servers(&cli, list)?;
        }
        "list" => {
            // List servers received from master servers.
            list_servers::run(&cli)?;
        }
        "monitor" => {
            // Monitor servers in real time.
            let list = parse_server_addresses(&cli.args[1..], cli.ip_version);
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

    logger::init(&cli);

    if let Err(e) = execute(cli) {
        eprintln!("error: {e}");
        process::exit(1);
    }
}
