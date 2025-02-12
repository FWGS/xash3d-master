// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

use std::{
    fs, io,
    net::{IpAddr, Ipv4Addr},
    path::Path,
};

use log::LevelFilter;
use serde::{de::Error as _, Deserialize, Deserializer};
use thiserror::Error;
use xash3d_protocol::{admin, filter::Version};

pub const DEFAULT_MASTER_SERVER_IP: IpAddr = IpAddr::V4(Ipv4Addr::UNSPECIFIED);

pub const DEFAULT_MASTER_SERVER_PORT: u16 = 27010;
pub const DEFAULT_CHALLENGE_TIMEOUT: u32 = 10;
pub const DEFAULT_SERVER_TIMEOUT: u32 = 300;
pub const DEFAULT_ADMIN_TIMEOUT: u32 = 10;

pub const DEFAULT_MAX_SERVERS_PER_IP: u16 = 14;

pub const DEFAULT_HASH_LEN: usize = admin::HASH_LEN;

macro_rules! impl_helpers {
    ($($f:ident: $t:ty),+$(,)?) => (
        $(const fn $f<const N: $t>() -> $t { N })+
    );
}

impl_helpers! {
    default_u16: u16,
    default_u32: u32,
    default_usize: usize,
}

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    Toml(#[from] toml::de::Error),
    #[error(transparent)]
    Io(#[from] io::Error),
}

#[derive(Default, Deserialize, Debug)]
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
    #[serde(default)]
    pub stat: StatConfig,
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
#[serde(rename_all = "kebab-case")]
pub struct ServerConfig {
    #[serde(default = "default_server_ip")]
    pub ip: IpAddr,
    #[serde(default = "default_u16::<DEFAULT_MASTER_SERVER_PORT>")]
    pub port: u16,
    #[serde(default = "default_u16::<DEFAULT_MAX_SERVERS_PER_IP>")]
    pub max_servers_per_ip: u16,
    #[serde(default = "default_server_version")]
    #[serde(deserialize_with = "deserialize_version")]
    pub min_version: Version,
    #[serde(default)]
    pub timeout: TimeoutConfig,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            ip: default_server_ip(),
            port: DEFAULT_MASTER_SERVER_PORT,
            max_servers_per_ip: DEFAULT_MAX_SERVERS_PER_IP,
            min_version: default_server_version(),
            timeout: Default::default(),
        }
    }
}

#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct TimeoutConfig {
    #[serde(default = "default_u32::<DEFAULT_CHALLENGE_TIMEOUT>")]
    pub challenge: u32,
    #[serde(default = "default_u32::<DEFAULT_SERVER_TIMEOUT>")]
    pub server: u32,
    #[serde(default = "default_u32::<DEFAULT_ADMIN_TIMEOUT>")]
    pub admin: u32,
}

impl Default for TimeoutConfig {
    fn default() -> Self {
        Self {
            challenge: DEFAULT_CHALLENGE_TIMEOUT,
            server: DEFAULT_SERVER_TIMEOUT,
            admin: DEFAULT_ADMIN_TIMEOUT,
        }
    }
}

#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct ClientConfig {
    #[serde(default = "default_client_version")]
    #[serde(deserialize_with = "deserialize_version")]
    pub version: Version,
    #[serde(default = "default_client_update_map")]
    pub update_map: Box<str>,
    #[serde(default = "default_client_update_title")]
    pub update_title: Box<str>,
    #[serde(default)]
    pub update_addr: Option<Box<str>>,
}

impl Default for ClientConfig {
    fn default() -> Self {
        Self {
            version: default_client_version(),
            update_map: default_client_update_map(),
            update_title: default_client_update_title(),
            update_addr: None,
        }
    }
}

#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct HashConfig {
    #[serde(default = "default_usize::<DEFAULT_HASH_LEN>")]
    pub len: usize,
    #[serde(default = "default_hash_key")]
    pub key: Box<str>,
    #[serde(default = "default_hash_personal")]
    pub personal: Box<str>,
}

impl Default for HashConfig {
    fn default() -> Self {
        Self {
            len: DEFAULT_HASH_LEN,
            key: default_hash_key(),
            personal: default_hash_personal(),
        }
    }
}

#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct AdminConfig {
    pub name: Box<str>,
    pub password: Box<str>,
}

#[derive(Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
pub struct StatConfig {
    pub interval: u32,
    #[serde(default = "default_stats_format")]
    pub format: Box<str>,
}

impl Default for StatConfig {
    fn default() -> Self {
        Self {
            interval: 0,
            format: default_stats_format(),
        }
    }
}

fn default_log_level() -> LevelFilter {
    LevelFilter::Info
}

fn default_server_ip() -> IpAddr {
    DEFAULT_MASTER_SERVER_IP
}

fn default_client_version() -> Version {
    Version::new(0, 19)
}

fn default_server_version() -> Version {
    Version::with_patch(0, 19, 2)
}

fn default_client_update_map() -> Box<str> {
    Box::from("Update please")
}

fn default_client_update_title() -> Box<str> {
    Box::from("https://github.com/FWGS/xash3d-fwgs")
}

fn default_hash_key() -> Box<str> {
    Box::from(admin::HASH_KEY)
}

fn default_hash_personal() -> Box<str> {
    Box::from(admin::HASH_PERSONAL)
}

fn default_stats_format() -> Box<str> {
    Box::from("stats: %s servers, %a add/s, %d del/s, %q query/s, %e error/s")
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
