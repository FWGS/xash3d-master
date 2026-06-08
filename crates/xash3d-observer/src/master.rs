use std::{fmt, net::SocketAddr, time::Duration};

use xash3d_protocol::{
    game::QueryServers, master::QueryServersResponse, server::GetServerInfoResponse,
};

use crate::event::{Event, ServerInfo, ServerList};

pub struct Master {
    addr: SocketAddr,
    key: u32,
}

impl Master {
    pub fn new(addr: SocketAddr) -> Self {
        Self { addr, key: 0 }
    }

    #[inline(always)]
    pub fn address(&self) -> &SocketAddr {
        &self.addr
    }

    pub(crate) fn encode_query_servers_packet<'a>(
        &mut self,
        filter: &str,
        buf: &'a mut [u8],
    ) -> &'a [u8] {
        struct FilterKey<'b> {
            filter: &'b str,
            key: u32,
        }

        impl fmt::Display for FilterKey<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}", self.filter)?;
                write!(f, "\\key\\{:x}", self.key)?;
                Ok(())
            }
        }

        // generate a fresh key for each request
        self.key = fastrand::u32(..);

        let packet = QueryServers::new(FilterKey {
            filter,
            key: self.key,
        });

        // TODO: handle error, filter may not fit
        packet.encode(buf).unwrap()
    }

    pub(crate) fn handle_packet<'a>(
        &mut self,
        from: &SocketAddr,
        data: &'a [u8],
    ) -> Option<Event<'a>> {
        match QueryServersResponse::decode(data) {
            Ok(response) => {
                if response.key != Some(self.key) {
                    // ignore if invalid or missing challenge key in the response
                    return None;
                }

                Some(Event::ServerList(ServerList::new(*from, response)))
            }
            Err(_) => {
                // The master server can respond with a fake server at same address. It's used
                // for update messages.
                if let Ok(response) = GetServerInfoResponse::decode(data) {
                    let info = ServerInfo {
                        server: *from,
                        ping: Duration::default(),
                        changed: true,
                        response,
                    };
                    Some(Event::ServerInfo(info))
                } else {
                    Some(Event::MasterInvalidPacket(*from, data))
                }
            }
        }
    }
}
