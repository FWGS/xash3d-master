//! Xash3D protocol between clients, servers and masters.

#![cfg_attr(all(not(feature = "std"), not(test)), no_std)]
#![cfg_attr(all(doc, docsrs), feature(doc_auto_cfg))]

#[cfg(feature = "alloc")]
extern crate alloc;

#[macro_use]
extern crate log;

mod cursor;
mod error;

#[cfg(feature = "net")]
pub mod net;

pub mod color;
pub mod filter;
pub mod server_info;
pub mod wrappers;

#[deprecated(since = "0.2.1", note = "use net module instead")]
#[cfg(feature = "net")]
pub use crate::net::{admin, game, master, server};

pub use crate::cursor::CursorError;
pub use crate::error::Error;
pub use crate::server_info::ServerInfo;

/// Current protocol version.
pub const PROTOCOL_VERSION: u8 = 49;
/// Current client version.
pub const CLIENT_VERSION: crate::filter::Version = crate::filter::Version::new(0, 21);
