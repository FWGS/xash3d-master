#[macro_use]
extern crate log;

mod app;
mod cli;
mod config;
mod hash_map;
mod logger;
mod periodic;
mod signals;
mod stats;
mod str_arr;
mod time;
mod udp_server;
mod worker;

fn main() {
    if let Err(e) = app::run() {
        error!("{}", e);
        std::process::exit(1);
    }
}
