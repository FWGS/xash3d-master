use std::{
    mem,
    net::SocketAddr,
    time::{Duration, SystemTime},
};

use serde::{ser::SerializeStruct, Serialize, Serializer};

use crate::server_info::{Players, ServerInfo};

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "status")]
#[serde(rename_all = "lowercase")]
pub enum ServerResultKind {
    Ok {
        #[serde(flatten)]
        info: ServerInfo,
    },
    /// An internal enum variant.
    #[serde(rename = "ok")]
    OkWithPlayers {
        #[serde(flatten)]
        info: ServerInfo,
        #[serde(flatten)]
        players: Players,
    },
    Ping,
    InvalidPacket {
        data: Vec<u8>,
    },
    Timeout,
    InvalidProtocol,
    Remove,
}

impl ServerResultKind {
    fn new_ok_with_players(mut info: ServerInfo, players: Players) -> Self {
        info.bots = players.bots_count();
        Self::OkWithPlayers { info, players }
    }

    pub fn is_timeout(&self) -> bool {
        matches!(self, ServerResultKind::Timeout)
    }
}

fn make_millis_f32(ping: Duration) -> f32 {
    ping.as_micros() as f32 / 1000.0
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ServerAddress {
    pub domain: Option<String>,
    pub resolved: SocketAddr,
}

impl Serialize for ServerAddress {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if let Some(domain) = &self.domain {
            let mut s = serializer.serialize_struct("ServerAddress", 2)?;
            s.serialize_field("address", &domain)?;
            s.serialize_field("resolved", &self.resolved)?;
            s.end()
        } else {
            let mut s = serializer.serialize_struct("ServerAddress", 1)?;
            s.serialize_field("address", &self.resolved)?;
            s.end()
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct ServerResult {
    #[serde(serialize_with = "serialize_unix_time")]
    pub time: SystemTime,
    #[serde(flatten)]
    pub address: ServerAddress,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(serialize_with = "serialize_ping")]
    pub ping: Option<Duration>,
    #[serde(flatten)]
    pub kind: ServerResultKind,
    /// Tempopary storage for server players.
    #[serde(skip)]
    players: Option<Players>,
}

impl ServerResult {
    pub fn new(resolved: SocketAddr, ping: Option<Duration>, kind: ServerResultKind) -> Self {
        Self {
            time: SystemTime::now(),
            address: ServerAddress {
                domain: None,
                resolved,
            },
            ping,
            kind,
            players: None,
        }
    }

    pub fn new_ping(address: SocketAddr, ping: Duration) -> Self {
        Self::new(address, Some(ping), ServerResultKind::Ping)
    }

    pub fn new_timeout(address: SocketAddr) -> Self {
        Self::new(address, None, ServerResultKind::Timeout)
    }

    pub fn ping_millis_f32(&self) -> Option<f32> {
        self.ping.map(make_millis_f32)
    }

    pub fn set_players(&mut self, players: Players) {
        let mut kind = mem::replace(&mut self.kind, ServerResultKind::Timeout);
        if let ServerResultKind::Ok { info } = kind {
            kind = ServerResultKind::new_ok_with_players(info, players);
        } else {
            self.players = Some(players);
        }
        self.kind = kind;
    }

    pub fn is_ok(&self) -> bool {
        matches!(self.kind, ServerResultKind::Ok { .. })
    }

    pub fn has_players(&self) -> bool {
        self.players.is_some()
    }

    pub fn set_ok(&mut self, ping: Duration, info: ServerInfo) {
        let mut kind = mem::replace(&mut self.kind, ServerResultKind::Timeout);
        if let ServerResultKind::OkWithPlayers { players, .. } = kind {
            kind = ServerResultKind::new_ok_with_players(info, players);
        } else if let Some(players) = self.players.take() {
            kind = ServerResultKind::new_ok_with_players(info, players);
        } else {
            kind = ServerResultKind::Ok { info };
        }
        self.ping = Some(ping);
        self.kind = kind;
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

fn serialize_ping<S: Serializer>(ping: &Option<Duration>, ser: S) -> Result<S::Ok, S::Error> {
    ping.map(make_millis_f32).serialize(ser)
}
