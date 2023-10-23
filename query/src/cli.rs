// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::process;

use getopts::Options;

use xash3d_protocol as proto;

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
    pub force_color: bool,
    pub filter: String,
    pub key: Option<u32>,
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
            protocol: vec![proto::PROTOCOL_VERSION, proto::PROTOCOL_VERSION - 1],
            json: false,
            debug: false,
            force_color: false,
            // if changed do not forget to update cli parsing
            filter: format!("\\gamedir\\valve\\clver\\{}", proto::CLIENT_VERSION),
            key: None,
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
    opts.optflag("F", "force-color", "force colored output");
    opts.optflag("k", "key", "send challenge key to master");
    opts.optflag("n", "nat", "query servers behind NAT");
    let help = format!("query filter [default: {:?}]", cli.filter);
    opts.optopt("f", "filter", &help, "FILTER");

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

    match matches.opt_get("master-timeout") {
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

    if let Some(s) = matches.opt_str("filter") {
        let mut filter = String::with_capacity(cli.filter.len() + s.len());
        if !s.contains("\\gamedir\\") {
            filter.push_str("\\gamedir\\valve");
        }
        if !s.contains("\\clver\\") {
            filter.push_str("\\clver\\0.20");
        }
        filter.push_str(&s);
        cli.filter = filter;
    }

    if !cli.filter.contains("\\nat\\") {
        let s = if matches.opt_present("nat") { "1" } else { "0" };
        cli.filter.push_str(&format!("\\nat\\{}", s));
    }

    if matches.opt_present("key") {
        let key = fastrand::u32(..);
        cli.key = Some(key);
        cli.filter.push_str(&format!("\\key\\{:x}", key));
    }

    cli.json = matches.opt_present("json");
    cli.debug = matches.opt_present("debug");
    cli.force_color = matches.opt_present("force-color");
    cli.args = matches.free;

    cli
}
