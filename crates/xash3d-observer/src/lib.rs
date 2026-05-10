#[macro_use]
extern crate log;

mod connection;
mod net;
mod observer_new;
mod observer_old;

pub mod event;
pub mod filter;

use std::time::Duration;

use xash3d_protocol::{self as proto};

#[deprecated]
pub type ProtocolError = proto::Error;

pub use crate::observer_new::*;
pub use crate::observer_old::*;

#[deprecated]
pub const MASTER_INTERVAL: Duration = Duration::from_secs(8);
#[deprecated]
pub const SERVER_INTERVAL: Duration = Duration::from_secs(2);
#[deprecated]
pub const SERVER_TIMEOUT: Duration = Duration::from_secs(16);
#[deprecated]
pub const SERVER_CLEAN_INTERVAL: Duration = Duration::from_secs(16);
