use std::{
    net::SocketAddr,
    time::{Duration, SystemTime},
};

use serde::{Serialize, Serializer};
use xash3d_protocol::wrappers::Str;

use crate::server_info::ServerInfo;

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "status")]
#[serde(rename_all = "lowercase")]
pub enum ServerResultKind {
    Ok {
        #[serde(flatten)]
        info: ServerInfo,
    },
    Ping,
    InvalidPacket {
        // TODO: remove me
        message: String,
        response: String,
    },
    Timeout,
    InvalidProtocol,
    Remove,
}

impl ServerResultKind {
    pub fn is_timeout(&self) -> bool {
        matches!(self, ServerResultKind::Timeout)
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct ServerResult {
    #[serde(serialize_with = "serialize_unix_time")]
    pub time: SystemTime,
    pub address: SocketAddr,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ping: Option<f32>,
    #[serde(flatten)]
    pub kind: ServerResultKind,
}

impl ServerResult {
    pub fn new(address: SocketAddr, ping: Option<Duration>, kind: ServerResultKind) -> Self {
        let ping = ping.map(|ping| ping.as_micros() as f32 / 1000.0);
        Self {
            time: SystemTime::now(),
            address,
            ping,
            kind,
        }
    }

    pub fn ok(address: SocketAddr, ping: Duration, info: ServerInfo) -> Self {
        Self::new(address, Some(ping), ServerResultKind::Ok { info })
    }

    pub fn ping(address: SocketAddr, ping: Duration) -> Self {
        Self::new(address, Some(ping), ServerResultKind::Ping)
    }

    pub fn timeout(address: SocketAddr) -> Self {
        Self::new(address, None, ServerResultKind::Timeout)
    }

    pub fn invalid_protocol(address: SocketAddr) -> Self {
        Self::new(address, None, ServerResultKind::InvalidProtocol)
    }

    pub fn invalid_packet(address: SocketAddr, response: &[u8]) -> Self {
        Self::new(
            address,
            None,
            ServerResultKind::InvalidPacket {
                message: String::new(),
                response: Str(response).to_string(),
            },
        )
    }
}

fn unix_time(time: &SystemTime) -> u64 {
    time.duration_since(SystemTime::UNIX_EPOCH)
        .map(|i| i.as_secs())
        .unwrap_or(0)
}

fn serialize_unix_time<S: Serializer>(time: &SystemTime, ser: S) -> Result<S::Ok, S::Error> {
    ser.serialize_u64(unix_time(time))
}
