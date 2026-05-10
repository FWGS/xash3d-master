#![deny(unsafe_code)]

#[macro_use]
extern crate log;

mod hash_map;
mod master_server;
mod periodic;
mod stats;
mod str_arr;
mod time;

pub mod config;

use crate::{stats::Stats, str_arr::StrArr};

pub use crate::{
    config::Config,
    master_server::{AddrExt, Error, Master, MasterServer},
};
