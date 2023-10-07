// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::process;

use getopts::Options;
use log::LevelFilter;
use thiserror::Error;

const BIN_NAME: &str = env!("CARGO_BIN_NAME");
const PKG_NAME: &str = env!("CARGO_PKG_NAME");
const PKG_VERSION: &str = env!("CARGO_PKG_VERSION");

const DEFAULT_MASTER_SERVER_PORT: u16 = 27010;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Invalid ip address \"{0}\"")]
    InvalidIp(String),
    #[error("Invalid port number \"{0}\"")]
    InvalidPort(String),
    #[error(transparent)]
    Options(#[from] getopts::Fail),
}

#[derive(Debug)]
pub struct Cli {
    pub log_level: LevelFilter,
    pub listen: SocketAddr,
}

impl Default for Cli {
    fn default() -> Self {
        Self {
            log_level: LevelFilter::Warn,
            listen: SocketAddr::new(
                IpAddr::from(Ipv4Addr::new(0, 0, 0, 0)),
                DEFAULT_MASTER_SERVER_PORT,
            ),
        }
    }
}

fn print_usage(opts: Options) {
    let brief = format!("Usage: {} [options]", BIN_NAME);
    print!("{}", opts.usage(&brief));
}

fn print_version() {
    println!("{} v{}", PKG_NAME, PKG_VERSION);
}

pub fn parse() -> Result<Cli, Error> {
    let mut cli = Cli::default();

    let args: Vec<_> = std::env::args().collect();
    let mut opts = Options::new();
    opts.optflag("h", "help", "print usage help");
    opts.optflag("v", "version", "print program version");
    let log_help =
        "logging level [default: warn(2)]\nLEVEL: 0-5, off, error, warn, info, debug, trace";
    opts.optopt("l", "log", log_help, "LEVEL");
    let ip_help = format!("listen ip [default: {}]", cli.listen.ip());
    opts.optopt("i", "ip", &ip_help, "IP");
    let port_help = format!("listen port [default: {}]", cli.listen.port());
    opts.optopt("p", "port", &port_help, "PORT");

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
        use LevelFilter as E;

        cli.log_level = match value.as_str() {
            _ if "off".starts_with(&value) => E::Off,
            _ if "error".starts_with(&value) => E::Error,
            _ if "warn".starts_with(&value) => E::Warn,
            _ if "info".starts_with(&value) => E::Info,
            _ if "debug".starts_with(&value) => E::Debug,
            _ if "trace".starts_with(&value) => E::Trace,
            _ => match value.parse::<u8>() {
                Ok(0) => E::Off,
                Ok(1) => E::Error,
                Ok(2) => E::Warn,
                Ok(3) => E::Info,
                Ok(4) => E::Debug,
                Ok(5) => E::Trace,
                _ => {
                    eprintln!("Invalid value for log option: \"{}\"", value);
                    process::exit(1);
                }
            },
        };
    }

    if let Some(s) = matches.opt_str("ip") {
        cli.listen
            .set_ip(s.parse().map_err(|_| Error::InvalidIp(s))?);
    }

    if let Some(s) = matches.opt_str("port") {
        cli.listen
            .set_port(s.parse().map_err(|_| Error::InvalidPort(s))?);
    }

    Ok(cli)
}
