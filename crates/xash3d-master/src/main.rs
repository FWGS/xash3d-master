#![deny(unsafe_code)]

#[macro_use]
extern crate log;

mod app;
mod cli;
mod config;
mod hash_map;
mod logger;
mod master_server;
mod periodic;
mod signal_flags;
mod stats;
mod str_arr;
mod time;

fn main() {
    if let Err(e) = app::run() {
        error!("{}", e);
        std::process::exit(1);
    }
}
