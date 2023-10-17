// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::process;

use getopts::Options;
use xash3d_protocol::admin;

const BIN_NAME: &str = env!("CARGO_BIN_NAME");
const PKG_NAME: &str = env!("CARGO_PKG_NAME");
const PKG_VERSION: &str = env!("CARGO_PKG_VERSION");

const DEFAULT_HOST: &str = "mentality.rip";
const DEFAULT_PORT: u16 = 27010;

#[derive(Debug)]
pub struct Cli {
    pub address: String,
    pub command: String,
    pub hash_len: usize,
    pub hash_key: String,
    pub hash_personal: String,
}

impl Default for Cli {
    fn default() -> Cli {
        Cli {
            address: format!("{}:{}", DEFAULT_HOST, DEFAULT_PORT),
            command: String::new(),
            hash_len: admin::HASH_LEN,
            hash_key: admin::HASH_KEY.to_owned(),
            hash_personal: admin::HASH_PERSONAL.to_owned(),
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

pub fn parse() -> Cli {
    let mut cli = Cli::default();

    let args: Vec<_> = std::env::args().collect();
    let mut opts = Options::new();
    opts.optflag("h", "help", "print usage help");
    opts.optflag("v", "version", "print program version");
    let help = format!("address to connect [default: {}]", cli.address);
    opts.optopt("h", "host", &help, "ADDR");
    let help = format!("hash length [default: {}]", cli.hash_len);
    opts.optopt("l", "hash-length", &help, "N");
    let help = format!("hash key [default: {}]", cli.hash_key);
    opts.optopt("k", "hash-key", &help, "KEY");
    let help = format!("hash personalization [default: {}]", cli.hash_personal);
    opts.optopt("p", "hash-personal", &help, "PERSONAL");

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

    if let Some(mut s) = matches.opt_str("host") {
        if !s.contains(':') {
            s.push_str(":27010");
        }
        cli.address = s;
    }

    match matches.opt_get("hash-length") {
        Ok(Some(n)) => cli.hash_len = n,
        Ok(None) => {}
        Err(_) => {
            eprintln!("Invalid key length");
            process::exit(1);
        }
    }

    if let Some(s) = matches.opt_str("hash-key") {
        cli.hash_key = s;
    }

    if let Some(s) = matches.opt_str("hash-personal") {
        cli.hash_personal = s;
    }

    cli.command = matches.free.join(" ");
    cli
}
