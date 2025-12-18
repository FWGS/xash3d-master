// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::{
    fmt::{self, Write},
    process,
    str::FromStr,
};

use getopts::Options;

use xash3d_protocol::{self as proto, filter::Version};

const BIN_NAME: &str = env!("CARGO_BIN_NAME");
const PKG_NAME: &str = env!("CARGO_PKG_NAME");
const PKG_VERSION: &str = env!("CARGO_PKG_VERSION");

#[rustfmt::skip]
const DEFAULT_MASTERS: &[&str] = &[
    "mentality.rip:27010",
    "ms2.mentality.rip:27010",
    "ms3.mentality.rip:27010",
    "mentality.rip:27011",
];

const DEFAULT_CLIENT_BUILDNUM: u32 = 4000;

struct Filter {
    clver: Option<Version>,
    buildnum: Option<u32>,
    protocol: Option<u8>,
    gamedir: Option<String>,
    map: Option<String>,
}

fn filter_opt<T: FromStr, F: Fn(&T) -> bool>(
    matches: &getopts::Matches,
    name: &str,
    dst: &mut Option<T>,
    f: F,
) {
    if let Some(s) = matches.opt_str(name) {
        if s == "none" {
            *dst = None;
            return;
        }
        match s.parse() {
            Ok(v) => {
                if f(&v) {
                    *dst = Some(v);
                }
            }
            Err(_) => {
                eprintln!("Invalid value for --{name}: {s}");
                process::exit(1);
            }
        }
    }
}

impl Filter {
    fn opt_get(&mut self, matches: &getopts::Matches) -> String {
        let mut out = String::new();

        if let Some(s) = matches.opt_str("filter") {
            if s.contains("\\clver\\") {
                self.clver = None;
            }
            if s.contains("\\buildnum\\") {
                self.buildnum = None;
            }
            out = s;
        }

        filter_opt(matches, "filter-clver", &mut self.clver, |_| true);
        filter_opt(matches, "filter-buildnum", &mut self.buildnum, |_| true);
        filter_opt(matches, "filter-gamedir", &mut self.gamedir, |s| s != "all");
        filter_opt(matches, "filter-map", &mut self.map, |s| s != "map");

        write!(&mut out, "{self}").unwrap();
        out
    }
}

impl fmt::Display for Filter {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        if let Some(clver) = self.clver {
            write!(fmt, "\\clver\\{clver}")?;
        }
        if let Some(buildnum) = self.buildnum {
            write!(fmt, "\\buildnum\\{buildnum}")?;
        }
        if let Some(protocol) = self.protocol {
            write!(fmt, "\\protocol\\{protocol}")?;
        }
        if let Some(gamedir) = &self.gamedir {
            write!(fmt, "\\gamedir\\{gamedir}")?;
        }
        if let Some(map) = &self.map {
            write!(fmt, "\\map\\{map}")?;
        }
        Ok(())
    }
}

impl Default for Filter {
    fn default() -> Self {
        Self {
            clver: Some(proto::CLIENT_VERSION),
            buildnum: Some(DEFAULT_CLIENT_BUILDNUM),
            protocol: None,
            gamedir: None,
            map: None,
        }
    }
}

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
            masters: DEFAULT_MASTERS
                .iter()
                .map(|i| i.to_string().into_boxed_str())
                .collect(),
            args: Default::default(),
            master_timeout: 2,
            server_timeout: 2,
            protocol: vec![proto::PROTOCOL_VERSION, proto::PROTOCOL_VERSION - 1],
            json: false,
            debug: false,
            force_color: false,
            filter: String::new(),
            key: None,
        }
    }
}

fn print_usage(opts: Options) {
    let brief = format!(
        "\
Usage: {BIN_NAME} [options] <COMMAND> [ARGS]

COMMANDS:
    all                 fetch servers from all masters and fetch info for each server
    info hosts...       fetch info for each server
    list                fetch servers from all masters and print server addresses
    monitor             live monitoring for server updates\
        "
    );
    print!("{}", opts.usage(&brief));
}

fn print_version() {
    println!("{PKG_NAME} v{PKG_VERSION}");
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
    opts.optopt("M", "master", &help, "LIST");
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
        .map(|&i| format!("{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let help = format!("protocol version [default: {protocols}]");
    opts.optopt("p", "protocol", &help, "VERSION");
    opts.optflag("j", "json", "output JSON");
    opts.optflag("d", "debug", "output debug");
    opts.optflag("F", "force-color", "force colored output");
    opts.optflag("k", "key", "send challenge key to master");

    // Filter options
    let mut filter = Filter::default();
    let help = format!("query filter [default: {filter}]");
    opts.optopt("f", "filter", &help, "FILTER");
    let default = filter.clver.unwrap();
    let help = format!("set query filter clver [default: {default}]");
    opts.optopt("V", "filter-clver", &help, "VERSION");
    let default = filter.buildnum.unwrap();
    let help = format!("set query filter buildnum [default: {default}]");
    opts.optopt("b", "filter-buildnum", &help, "BUILDNUM");
    let help = "set query filter gamedir [default: all]";
    opts.optopt("g", "filter-gamedir", help, "GAMEDIR");
    let help = "set query filter map [default: all]";
    opts.optopt("m", "filter-map", help, "MAP");

    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("{e}");
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
                    eprintln!("Invalid protocol version: {i}");
                    error = true;
                }
            }
        }

        if error {
            process::exit(1);
        }
    }

    cli.filter = filter.opt_get(&matches);

    if matches.opt_present("key") {
        let key = fastrand::u32(..);
        cli.key = Some(key);
        cli.filter.push_str(&format!("\\key\\{key:x}"));
    }

    cli.json = matches.opt_present("json");
    cli.debug = matches.opt_present("debug");
    cli.force_color = matches.opt_present("force-color");
    cli.args = matches.free;

    cli
}
