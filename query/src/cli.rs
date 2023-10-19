// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::process;

use getopts::Options;

const BIN_NAME: &str = env!("CARGO_BIN_NAME");
const PKG_NAME: &str = env!("CARGO_PKG_NAME");
const PKG_VERSION: &str = env!("CARGO_PKG_VERSION");

const DEFAULT_HOST: &str = "mentality.rip";
const DEFAULT_PORT: u16 = 27010;

#[derive(Debug)]
pub struct Cli {
    pub masters: Vec<Box<str>>,
    pub args: Vec<String>,
    pub master_timeout: u32,
    pub server_timeout: u32,
    pub protocol: Vec<u8>,
    pub json: bool,
    pub debug: bool,
}

impl Default for Cli {
    fn default() -> Cli {
        Cli {
            masters: vec![
                format!("{}:{}", DEFAULT_HOST, DEFAULT_PORT).into_boxed_str(),
                //format!("{}:{}", DEFAULT_HOST, DEFAULT_PORT + 1).into_boxed_str(),
            ],
            args: Default::default(),
            master_timeout: 2,
            server_timeout: 2,
            protocol: vec![xash3d_protocol::VERSION, xash3d_protocol::VERSION - 1],
            json: false,
            debug: false,
        }
    }
}

fn print_usage(opts: Options) {
    let brief = format!(
        "\
Usage: {} [options] <COMMAND> [ARGS]

COMMANDS:
    all                 fetch servers from all masters and fetch info for each server
    info hosts...       fetch info for each server
    list                fetch servers from all masters and print server addresses\
        ",
        BIN_NAME
    );
    print!("{}", opts.usage(&brief));
}

fn print_version() {
    println!("{} v{}", PKG_NAME, PKG_VERSION);
}

pub fn parse() -> Cli {
    let mut cli = Cli::default();

    let args: Vec<_> = std::env::args().collect();
    let mut opts = Options::new();
    opts.optflag("h", "help", "print usage help");
    opts.optflag("v", "version", "print program version");
    let help = format!(
        "master address to connect [default: {}]",
        cli.masters.join(",")
    );
    opts.optopt("m", "master", &help, "LIST");
    let help = format!(
        "time to wait results from masters [default: {}]",
        cli.master_timeout
    );
    opts.optopt("T", "master-timeout", &help, "SECONDS");
    let help = format!(
        "time to wait results from servers [default: {}]",
        cli.server_timeout
    );
    opts.optopt("t", "server-timeout", &help, "SECONDS");
    let protocols = cli
        .protocol
        .iter()
        .map(|&i| format!("{}", i))
        .collect::<Vec<_>>()
        .join(",");
    let help = format!("protocol version [default: {}]", protocols);
    opts.optopt("p", "protocol", &help, "VERSION");
    opts.optflag("j", "json", "output JSON");
    opts.optflag("d", "debug", "output debug");

    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("{}", e);
            process::exit(1);
        }
    };

    if matches.opt_present("help") {
        print_usage(opts);
        process::exit(0);
    }

    if matches.opt_present("version") {
        print_version();
        process::exit(0);
    }

    if let Some(s) = matches.opt_str("master") {
        cli.masters.clear();

        for mut i in s.split(',').map(String::from) {
            if !i.contains(':') {
                i.push_str(":27010");
            }
            cli.masters.push(i.into_boxed_str());
        }
    }

    match matches.opt_get("master") {
        Ok(Some(t)) => cli.master_timeout = t,
        Ok(None) => {}
        Err(_) => {
            eprintln!("Invalid master-timeout");
            process::exit(1);
        }
    }

    match matches.opt_get("server-timeout") {
        Ok(Some(t)) => cli.server_timeout = t,
        Ok(None) => {}
        Err(_) => {
            eprintln!("Invalid server-timeout");
            process::exit(1);
        }
    }

    if let Some(s) = matches.opt_str("protocol") {
        cli.protocol.clear();

        let mut error = false;
        for i in s.split(',') {
            match i.parse() {
                Ok(i) => cli.protocol.push(i),
                Err(_) => {
                    eprintln!("Invalid protocol version: {}", i);
                    error = true;
                }
            }
        }

        if error {
            process::exit(1);
        }
    }

    cli.json = matches.opt_present("json");
    cli.debug = matches.opt_present("debug");
    cli.args = matches.free;

    cli
}
