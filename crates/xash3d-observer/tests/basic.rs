use std::{
    collections::{HashMap, HashSet},
    io,
    net::{SocketAddr, UdpSocket},
    thread,
    time::{Duration, Instant},
};

use xash3d_observer::{event::Event, Buffer, Observer, Server};
use xash3d_protocol::{game, server, wrappers::Str};

fn init_logger() {
    struct Logger;

    impl log::Log for Logger {
        fn enabled(&self, _metadata: &log::Metadata) -> bool {
            true
        }

        fn log(&self, record: &log::Record) {
            println!("{} - {}", record.level(), record.args());
        }

        fn flush(&self) {}
    }

    static LOGGER: Logger = Logger;

    log::set_logger(&LOGGER).ok();
    log::set_max_level(log::LevelFilter::Trace);
}

struct FakeServer {
    sock: UdpSocket,
    protocol: u8,
    /// GoldSrc server.
    gs: bool,
    /// Enable additional response to `GetServerInfo2` request with `GetServerInfo2ResponseOld`.
    dproto: bool,
    /// Enable response to `GetServerInfo` request.
    info: bool,
}

impl FakeServer {
    fn new(protocol: u8) -> Self {
        let addr = SocketAddr::from(([127, 0, 0, 1], 0));
        let sock = UdpSocket::bind(addr).unwrap();
        Self {
            sock,
            protocol,
            gs: false,
            dproto: false,
            info: true,
        }
    }

    fn new_gs(dproto: bool, info: bool) -> Self {
        Self {
            gs: true,
            dproto,
            info,
            ..Self::new(48)
        }
    }

    fn name(&self) -> String {
        let mut ret;
        if self.gs {
            ret = format!("GoldSrc {}", self.protocol);
        } else {
            ret = format!("Xash3D {}", self.protocol);
        }
        if self.dproto {
            ret.push_str(" (dproto)");
        }
        if self.gs && self.info {
            ret.push_str(" (info)");
        }
        ret
    }

    fn handle_get_server_info(
        &self,
        req: &game::GetServerInfo,
        from: &SocketAddr,
    ) -> io::Result<()> {
        let protocol = self.protocol;
        let host = self.name();
        if req.protocol == protocol {
            let resp = server::GetServerInfoResponse {
                gamedir: Str(b"valve"),
                map: Str(b"crossfire"),
                host: Str(host.as_bytes()),
                protocol,
                maxcl: 32,
                ..server::GetServerInfoResponse::default()
            };
            let mut buf = [0; 512];
            let buf = resp.encode(&mut buf).unwrap();
            self.sock.send_to(buf, from)?;
        } else {
            let mut buf = [0; 512];
            let buf =
                server::GetServerInfoResponse::encode_wrong_version(host.as_bytes(), &mut buf)
                    .unwrap();
            self.sock.send_to(buf, from)?;
        }
        Ok(())
    }

    fn handle_get_server_info2(
        &self,
        _req: &game::GetServerInfo2,
        from: &SocketAddr,
    ) -> io::Result<()> {
        let protocol = self.protocol;
        let host = self.name();
        let resp = server::GetServerInfo2Response {
            protocol,
            host: Str(host.as_bytes()),
            map: Str(b"crossfire"),
            gamedir: Str(b"valve"),
            game: Str(b"Half-Life"),
            max_players: 32,
            version: Str(b"1.2.3.4"),
            ..server::GetServerInfo2Response::default()
        };
        let mut buf = [0; 512];
        let buf = resp.encode(&mut buf).unwrap();
        self.sock.send_to(buf, from)?;

        if !self.dproto {
            return Ok(());
        }

        let addr = format!("{}", self.sock.local_addr()?);
        let resp = server::GetServerInfo2ResponseOld {
            address: Str(addr.as_bytes()),
            host: Str(host.as_bytes()),
            map: Str(b"crossfire"),
            gamedir: Str(b"valve"),
            game: Str(b"Half-Life"),
            max_players: 32,
            protocol: protocol - 1,
            ..server::GetServerInfo2ResponseOld::default()
        };
        let mut buf = [0; 512];
        let buf = resp.encode(&mut buf).unwrap();
        self.sock.send_to(buf, from)?;

        Ok(())
    }

    fn handle(&self, buf: &[u8], from: &SocketAddr) -> io::Result<()> {
        // TODO: GoldSrc engine has correct parser for `GetServerInfo` request.
        if self.gs && !self.info && buf.starts_with(game::Ping::HEADER) {
            let mut buf = [0; 128];
            let buf = server::PingResponse::encode(&mut buf).unwrap();
            self.sock.send_to(buf, from)?;
            return Ok(());
        }

        let Ok(Some(packet)) = game::Packet::decode(buf) else {
            panic!("failed to decode a packet");
        };

        match packet {
            game::Packet::GetServerInfo(ref req) if self.info => {
                self.handle_get_server_info(req, from)?;
            }
            game::Packet::GetServerInfo2(ref req) => {
                self.handle_get_server_info2(req, from)?;
            }
            _ => {}
        }

        Ok(())
    }

    fn run(self) -> SocketAddr {
        let addr = self.sock.local_addr().unwrap();
        thread::Builder::new()
            .name(format!("server {addr} {}", self.name()))
            .spawn(move || {
                let mut buf = [0; 1024];
                loop {
                    match self.sock.recv_from(&mut buf) {
                        Ok((n, ref from)) => {
                            if let Err(e) = self.handle(&buf[..n], from) {
                                panic!("error: {e}");
                            }
                        }
                        Err(e) => panic!("error: {e}"),
                    }
                }
            })
            .unwrap();
        addr
    }
}

#[derive(Debug, PartialEq, Eq)]
enum ServerState {
    Unknown,
    Info,
    Timeout,
    Removed,
    InvalidProtocol,
    InvalidPacket,
}

struct ServerResult {
    name: String,
    state: ServerState,
}

impl ServerResult {
    fn new(name: String) -> Self {
        Self {
            name,
            state: ServerState::Unknown,
        }
    }
}

#[test]
fn query_info() -> io::Result<()> {
    init_logger();

    let servers = [
        FakeServer::new(48),
        FakeServer::new(49),
        FakeServer::new_gs(false, false),
        FakeServer::new_gs(true, false),
        FakeServer::new_gs(false, true),
        FakeServer::new_gs(true, true),
    ];

    let mut observer = Observer::new()?;
    let mut results = HashMap::new();
    let mut waiting = HashSet::new();
    for server in servers {
        let name = server.name();
        let addr = server.run();
        println!("FAKE SERVER: {addr} {name}");
        results.insert(addr, ServerResult::new(name));
        waiting.insert(addr);
        observer.insert_server(Server::new(addr));
    }

    let start = Instant::now();
    let timeout = Duration::from_secs(1);
    let mut remaining = Some(timeout);
    let mut buffer = Buffer::new();
    while remaining.is_some() {
        // if waiting.is_empty() {
        //     break;
        // }

        match observer.wait_event(&mut buffer, remaining)? {
            Event::Timeout => {}
            Event::ServerInfo(info) => {
                let addr = info.address();
                results.get_mut(addr).unwrap().state = ServerState::Info;
                waiting.remove(addr);
            }
            Event::ServerInfoTimeout(ref addr) => {
                results.get_mut(addr).unwrap().state = ServerState::Timeout;
            }
            Event::ServerRemove(ref addr) => {
                results.get_mut(addr).unwrap().state = ServerState::Removed;
            }
            Event::ServerInvalidProtocol(ref addr) => {
                results.get_mut(addr).unwrap().state = ServerState::InvalidProtocol;
            }
            Event::ServerInvalidPacket(ref addr, ..) => {
                results.get_mut(addr).unwrap().state = ServerState::InvalidPacket;
            }
            _ => {}
        }

        remaining = timeout.checked_sub(start.elapsed());
    }

    let mut failed = false;
    for (addr, result) in results.iter() {
        let s = if result.state != ServerState::Info {
            failed = true;
            "FAIL"
        } else {
            "OK"
        };
        println!("{s:>4}: {addr} {} {:?}", result.name, result.state);
    }
    assert!(!failed);

    Ok(())
}
