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

pub const DEFAULT_SERVER_MIN_VERSION: Version = Version::with_patch(0, 19, 2);
pub const DEFAULT_CLIENT_MIN_VERSION: Version = Version::new(0, 19);

// Disabled if zero.
pub const DEFAULT_MIN_ENGINE_BUILDNUM: u32 = 0;

// it was added in 0.19.4 on 26 Feb 2025:
// https://github.com/tyabus/xash3d/commit/839504e464ccdfeb15bce060be0603e2ee580d00
// give it 100 more days in the past, just in case
//
// Disabled if zero.
pub const DEFAULT_MIN_OLD_ENGINE_BUILDNUM: u32 = 3500;

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    Toml(#[from] toml::de::Error),
    #[error(transparent)]
    Io(#[from] io::Error),
}

#[derive(Clone, Default, Deserialize, Debug)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "kebab-case")]
#[serde(default)]
pub struct Config {
    pub log: LogConfig,
    #[serde(flatten)]
    pub master: MasterConfig,
    pub stat: StatConfig,
}

#[derive(Clone, Default, Deserialize, Debug)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "kebab-case")]
#[serde(default)]
pub struct MasterConfig {
    pub server: ServerConfig,
    pub client: ClientConfig,
    pub hash: HashConfig,
    #[serde(rename = "admin")]
    pub admin_list: Box<[AdminConfig]>,
}

#[derive(Clone, Deserialize, Debug)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "kebab-case")]
#[serde(default)]
pub struct LogConfig {
    #[serde(deserialize_with = "deserialize_log_level")]
    pub level: LevelFilter,
    pub time: bool,
}

impl Default for LogConfig {
    fn default() -> Self {
        Self {
            level: LevelFilter::Info,
            time: true,
        }
    }
}

#[derive(Clone, Deserialize, Debug)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "kebab-case")]
#[serde(default)]
pub struct ServerConfig {
    pub ip: IpAddr,
    pub port: u16,
    pub max_servers_per_ip: u16,
    #[serde(deserialize_with = "deserialize_version")]
    pub min_version: Version,
    pub timeout: TimeoutConfig,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            ip: DEFAULT_MASTER_SERVER_IP,
            port: DEFAULT_MASTER_SERVER_PORT,
            max_servers_per_ip: DEFAULT_MAX_SERVERS_PER_IP,
            min_version: DEFAULT_SERVER_MIN_VERSION,
            timeout: Default::default(),
        }
    }
}

#[derive(Clone, Deserialize, Debug)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "kebab-case")]
#[serde(default)]
pub struct TimeoutConfig {
    pub challenge: u32,
    pub server: u32,
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

#[derive(Clone, Deserialize, Debug)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "kebab-case")]
#[serde(default)]
pub struct ClientConfig {
    #[serde(deserialize_with = "deserialize_version")]
    pub min_version: Version,
    pub min_engine_buildnum: u32,
    pub min_old_engine_buildnum: u32,
    pub update_map: Box<str>,
    pub update_title: Box<str>,
    pub update_addr: Option<Box<str>>,
}

impl Default for ClientConfig {
    fn default() -> Self {
        Self {
            min_version: DEFAULT_CLIENT_MIN_VERSION,
            min_engine_buildnum: DEFAULT_MIN_ENGINE_BUILDNUM,
            min_old_engine_buildnum: DEFAULT_MIN_OLD_ENGINE_BUILDNUM,
            update_map: Box::from("Update please"),
            update_title: Box::from("https://github.com/FWGS/xash3d-fwgs"),
            update_addr: None,
        }
    }
}

#[derive(Clone, Deserialize, Debug)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "kebab-case")]
#[serde(default)]
pub struct HashConfig {
    pub len: usize,
    pub key: Box<str>,
    pub personal: Box<str>,
}

impl Default for HashConfig {
    fn default() -> Self {
        Self {
            len: DEFAULT_HASH_LEN,
            key: Box::from(admin::HASH_KEY),
            personal: Box::from(admin::HASH_PERSONAL),
        }
    }
}

#[derive(Clone, Deserialize, Debug)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "kebab-case")]
pub struct AdminConfig {
    pub name: Box<str>,
    pub password: Box<str>,
}

#[derive(Clone, Deserialize, Debug)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "kebab-case")]
#[serde(default)]
pub struct StatConfig {
    pub interval: u32,
    pub format: Box<str>,
}

impl Default for StatConfig {
    fn default() -> Self {
        Self {
            interval: 0,
            format: Box::from("stats: %s servers, %a add/s, %d del/s, %q query/s, %e error/s"),
        }
    }
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
