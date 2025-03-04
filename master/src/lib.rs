#![deny(unsafe_code)]

mod cleanup;
mod master_server;
mod stats;
mod str_arr;
mod time;

pub mod config;

pub use config::Config;
pub use master_server::{AddrExt, Error, Master, MasterServer};
