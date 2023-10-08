// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::net::IpAddr;
use std::process;

use getopts::Options;
use log::LevelFilter;
use thiserror::Error;

use crate::config;

const BIN_NAME: &str = env!("CARGO_BIN_NAME");
const PKG_NAME: &str = env!("CARGO_PKG_NAME");
const PKG_VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Error, Debug)]
pub enum Error {
    #[error("Invalid ip address \"{0}\"")]
    InvalidIp(String),
    #[error("Invalid port number \"{0}\"")]
    InvalidPort(String),
    #[error(transparent)]
    Options(#[from] getopts::Fail),
}

#[derive(Debug, Default)]
pub struct Cli {
    pub log_level: Option<LevelFilter>,
    pub listen_ip: Option<IpAddr>,
    pub listen_port: Option<u16>,
    pub config_path: Box<str>,
}

fn print_usage(opts: Options) {
    let brief = format!("Usage: {} [options]", BIN_NAME);
    print!("{}", opts.usage(&brief));
}

fn print_version() {
    println!("{} v{}", PKG_NAME, PKG_VERSION);
}

pub fn parse() -> Result<Cli, Error> {
    let mut cli = Cli {
        config_path: config::DEFAULT_CONFIG_PATH.to_string().into_boxed_str(),
        ..Cli::default()
    };

    let args: Vec<_> = std::env::args().collect();
    let mut opts = Options::new();
    opts.optflag("h", "help", "print usage help");
    opts.optflag("v", "version", "print program version");
    let log_help =
        "logging level [default: warn(2)]\nLEVEL: 0-5, off, error, warn, info, debug, trace";
    opts.optopt("l", "log", log_help, "LEVEL");
    let ip_help = format!("listen ip [default: {}]", config::DEFAULT_MASTER_SERVER_IP);
    opts.optopt("i", "ip", &ip_help, "IP");
    let port_help = format!(
        "listen port [default: {}]",
        config::DEFAULT_MASTER_SERVER_PORT
    );
    opts.optopt("p", "port", &port_help, "PORT");
    let config_help = format!("config path [default: {}]", cli.config_path);
    opts.optopt("c", "config", &config_help, "PATH");

    let matches = opts.parse(&args[1..])?;

    if matches.opt_present("help") {
        print_usage(opts);
        process::exit(0);
    }

    if matches.opt_present("version") {
        print_version();
        process::exit(0);
    }

    if let Some(value) = matches.opt_str("log") {
        match config::parse_log_level(value.as_ref()) {
            Some(level) => cli.log_level = Some(level),
            None => {
                eprintln!("Invalid value for log option: \"{}\"", value);
                process::exit(1);
            }
        }
    }

    if let Some(s) = matches.opt_str("ip") {
        cli.listen_ip = Some(s.parse().map_err(|_| Error::InvalidIp(s))?);
    }

    if let Some(s) = matches.opt_str("port") {
        cli.listen_port = Some(s.parse().map_err(|_| Error::InvalidPort(s))?);
    }

    if let Some(s) = matches.opt_str("config") {
        cli.config_path = s.into_boxed_str();
    }

    Ok(cli)
}
