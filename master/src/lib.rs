#![deny(unsafe_code)]

mod master_server;
mod periodic;
mod stats;
mod str_arr;
mod time;

pub mod config;

use crate::{periodic::Periodic, stats::Stats, str_arr::StrArr, time::RelativeTimer};

pub use crate::{
    config::Config,
    master_server::{AddrExt, Error, Master, MasterServer},
};
