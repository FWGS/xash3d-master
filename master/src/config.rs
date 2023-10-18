// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::fs;
use std::io;
use std::net::{IpAddr, Ipv4Addr, SocketAddrV4};
use std::path::Path;

use log::LevelFilter;
use serde::{de::Error as _, Deserialize, Deserializer};
use thiserror::Error;
use xash3d_protocol::admin;
use xash3d_protocol::filter::Version;

pub const DEFAULT_CONFIG_PATH: &str = "config/main.toml";

pub const DEFAULT_MASTER_SERVER_IP: IpAddr = IpAddr::V4(Ipv4Addr::new(0, 0, 0, 0));
pub const DEFAULT_MASTER_SERVER_PORT: u16 = 27010;
pub const DEFAULT_TIMEOUT: u32 = 300;
pub const DEFAULT_ADMIN_TIMEOUT: u32 = 10;

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    Toml(#[from] toml::de::Error),
    #[error(transparent)]
    Io(#[from] io::Error),
}

#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct Config {
    #[serde(default)]
    pub log: LogConfig,
    #[serde(default)]
    pub server: ServerConfig,
    #[serde(default)]
    pub client: ClientConfig,
    #[serde(default)]
    pub hash: HashConfig,
    #[serde(rename = "admin")]
    #[serde(default)]
    pub admin_list: Box<[AdminConfig]>,
}

#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct LogConfig {
    #[serde(default = "default_log_level")]
    #[serde(deserialize_with = "deserialize_log_level")]
    pub level: LevelFilter,
}

impl Default for LogConfig {
    fn default() -> Self {
        Self {
            level: default_log_level(),
        }
    }
}

#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct ServerConfig {
    #[serde(default = "default_server_ip")]
    pub ip: IpAddr,
    #[serde(default = "default_server_port")]
    pub port: u16,
    #[serde(default)]
    pub timeout: TimeoutConfig,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            ip: default_server_ip(),
            port: default_server_port(),
            timeout: Default::default(),
        }
    }
}

#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct TimeoutConfig {
    #[serde(default = "default_timeout")]
    pub challenge: u32,
    #[serde(default = "default_timeout")]
    pub server: u32,
    #[serde(default = "default_admin_timeout")]
    pub admin: u32,
}

impl Default for TimeoutConfig {
    fn default() -> Self {
        Self {
            challenge: default_timeout(),
            server: default_timeout(),
            admin: default_admin_timeout(),
        }
    }
}

#[derive(Deserialize, Default, Debug)]
#[serde(deny_unknown_fields)]
pub struct ClientConfig {
    #[serde(default)]
    #[serde(deserialize_with = "deserialize_version")]
    pub version: Version,
    #[serde(default)]
    pub update_map: Box<str>,
    #[serde(default)]
    pub update_title: Box<str>,
    #[serde(default)]
    pub update_addr: Option<SocketAddrV4>,
}

#[derive(Deserialize, Default, Debug)]
#[serde(deny_unknown_fields)]
pub struct HashConfig {
    #[serde(default = "default_hash_len")]
    pub len: usize,
    #[serde(default = "default_hash_key")]
    pub key: Box<str>,
    #[serde(default = "default_hash_personal")]
    pub personal: Box<str>,
}

#[derive(Deserialize, Default, Debug)]
#[serde(deny_unknown_fields)]
pub struct AdminConfig {
    pub name: Box<str>,
    pub password: Box<str>,
}

fn default_log_level() -> LevelFilter {
    LevelFilter::Warn
}

fn default_server_ip() -> IpAddr {
    DEFAULT_MASTER_SERVER_IP
}

fn default_server_port() -> u16 {
    DEFAULT_MASTER_SERVER_PORT
}

fn default_timeout() -> u32 {
    DEFAULT_TIMEOUT
}

fn default_admin_timeout() -> u32 {
    DEFAULT_ADMIN_TIMEOUT
}

fn default_hash_len() -> usize {
    admin::HASH_LEN
}

fn default_hash_key() -> Box<str> {
    Box::from(admin::HASH_KEY)
}

fn default_hash_personal() -> Box<str> {
    Box::from(admin::HASH_PERSONAL)
}

fn deserialize_log_level<'de, D>(de: D) -> Result<LevelFilter, D::Error>
where
    D: Deserializer<'de>,
{
    let s = <&str>::deserialize(de)?;
    parse_log_level(s).ok_or_else(|| D::Error::custom(format!("Invalid log level: \"{}\"", s)))
}

pub fn parse_log_level(s: &str) -> Option<LevelFilter> {
    use LevelFilter as E;

    let level_filter = match s {
        _ if "off".starts_with(s) => E::Off,
        _ if "error".starts_with(s) => E::Error,
        _ if "warn".starts_with(s) => E::Warn,
        _ if "info".starts_with(s) => E::Info,
        _ if "debug".starts_with(s) => E::Debug,
        _ if "trace".starts_with(s) => E::Trace,
        _ => match s.parse::<u8>() {
            Ok(0) => E::Off,
            Ok(1) => E::Error,
            Ok(2) => E::Warn,
            Ok(3) => E::Info,
            Ok(4) => E::Debug,
            Ok(5) => E::Trace,
            _ => return None,
        },
    };
    Some(level_filter)
}

fn deserialize_version<'de, D>(de: D) -> Result<Version, D::Error>
where
    D: Deserializer<'de>,
{
    let s = <&str>::deserialize(de)?;
    s.parse()
        .map_err(|_| D::Error::custom(format!("Invalid version: \"{}\"", s)))
}

pub fn load<P: AsRef<Path>>(path: P) -> Result<Config, Error> {
    let data = fs::read(path)?;
    Ok(toml::de::from_slice(&data)?)
}
