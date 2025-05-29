use std::{
    io,
    net::{Ipv4Addr, SocketAddr, SocketAddrV4, UdpSocket},
    sync::atomic::AtomicBool,
    thread,
    time::Duration,
};

use log::info;
use xash3d_master::{Config, MasterServer};
use xash3d_protocol::{filter::Filter, game, master, server, wrappers::Str};

const UNSPECIFIED: SocketAddrV4 = SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0);

struct Logger;
static LOGGER: Logger = Logger;

impl log::Log for Logger {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        println!("{} - {}", record.level(), record.args());
    }

    fn flush(&self) {}
}

struct Test {
    master_addr: SocketAddr,
    server_addr: SocketAddr,
}

impl Test {
    fn new(cfg: &Config) -> Test {
        let mut test = Test {
            master_addr: UNSPECIFIED.into(),
            server_addr: UNSPECIFIED.into(),
        };
        test.create_master(cfg);
        test.add_server(cfg);
        test
    }

    fn create_master(&mut self, cfg: &Config) {
        let mut master = MasterServer::new(cfg.clone(), UNSPECIFIED).unwrap();
        self.master_addr = master.local_addr().unwrap();
        let sig_flag = AtomicBool::new(false);
        thread::spawn(move || master.run(&sig_flag).unwrap());
    }

    fn add_server(&mut self, cfg: &Config) {
        let sock = UdpSocket::bind(UNSPECIFIED).unwrap();
        self.server_addr = sock.local_addr().unwrap();
        let challenge = Some(0xdeadbeef);
        let p = server::Challenge::new(challenge);
        let mut buf = [0; 512];
        let p = p.encode(&mut buf).unwrap();
        sock.send_to(p, self.master_addr).unwrap();

        let (l, _) = sock.recv_from(&mut buf).unwrap();
        let r = master::ChallengeResponse::decode(&buf[..l]).unwrap();
        assert_eq!(r.server_challenge, challenge);

        let p = server::ServerAdd {
            gamedir: "valve",
            map: "crossfire",
            version: cfg.master.server.min_version,
            challenge: r.master_challenge,
            server_type: server::ServerType::Dedicated,
            os: server::Os::Linux,
            region: server::Region::RestOfTheWorld,
            protocol: xash3d_protocol::PROTOCOL_VERSION,
            players: 8,
            max: 32,
            flags: server::ServerFlags::empty(),
        };
        let p = p.encode(&mut buf).unwrap();
        sock.send_to(p, self.master_addr).unwrap();
    }
}

#[test]
fn server_add() {
    log::set_logger(&LOGGER).ok();
    log::set_max_level(log::LevelFilter::Trace);

    let cfg = Config::default();
    let test = Test::new(&cfg);
    let mut buf = [0; 1024];
    let sock = UdpSocket::bind(UNSPECIFIED).unwrap();
    let game_key = Some(0xbeefdead);
    let p = game::QueryServers {
        region: server::Region::RestOfTheWorld,
        last: UNSPECIFIED.into(),
        filter: Filter {
            gamedir: Some(Str(b"valve")),
            clver: Some(xash3d_protocol::CLIENT_VERSION),
            client_os: Some(Str(b"linux")),
            client_arch: Some(Str(b"amd64")),
            client_buildnum: Some(cfg.master.client.min_engine_buildnum),
            key: game_key,
            ..Filter::default()
        },
    };
    let p = p.encode(&mut buf).unwrap();
    sock.send_to(p, test.master_addr).unwrap();

    let (l, _) = sock.recv_from(&mut buf).unwrap();
    let r = master::QueryServersResponse::decode(&buf[..l]).unwrap();
    assert_eq!(r.key, game_key);
    let servers = r.iter::<SocketAddrV4>().collect::<Vec<_>>();
    assert_eq!(servers.len(), 1);
    assert_eq!(servers[0].port(), test.server_addr.port());
}

#[test]
fn client_rate_limit() {
    log::set_logger(&LOGGER).ok();
    log::set_max_level(log::LevelFilter::Trace);

    let mut cfg = Config::default();
    cfg.master.server.client_rate_limit = 10;
    info!("client rate limit {}", cfg.master.server.client_rate_limit);

    let test = Test::new(&cfg);
    let sock = UdpSocket::bind(UNSPECIFIED).unwrap();
    sock.set_read_timeout(Some(Duration::from_millis(100)))
        .unwrap();
    let queries = cfg.master.server.client_rate_limit + 20;
    for i in 0..3 {
        if i > 0 {
            info!("client sleep for 1s");
            thread::sleep(Duration::from_secs(1));
        }
        info!("send {queries} client queries");
        let game_key = Some(0xbeefdead);
        let p = game::QueryServers {
            region: server::Region::RestOfTheWorld,
            last: UNSPECIFIED.into(),
            filter: Filter {
                gamedir: Some(Str(b"valve")),
                clver: Some(xash3d_protocol::CLIENT_VERSION),
                client_os: Some(Str(b"linux")),
                client_arch: Some(Str(b"amd64")),
                client_buildnum: Some(cfg.master.client.min_engine_buildnum),
                key: game_key,
                ..Filter::default()
            },
        };
        let mut buf = [0; 512];
        let p = p.encode(&mut buf).unwrap();
        for _ in 0..queries {
            sock.send_to(p, test.master_addr).unwrap();
        }
        let mut n = 0;
        while n < queries {
            match sock.recv_from(&mut buf) {
                Ok((l, _)) => {
                    n += 1;
                    info!("client query {n} ok");
                    let r = master::QueryServersResponse::decode(&buf[..l]).unwrap();
                    assert_eq!(r.key, game_key);
                    let servers = r.iter::<SocketAddrV4>().collect::<Vec<_>>();
                    assert_eq!(servers.len(), 1);
                    assert_eq!(servers[0].port(), test.server_addr.port());
                }
                Err(err) => match err.kind() {
                    io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut => {
                        info!("client query {} read timeout", n + 1);
                        break;
                    }
                    _ => panic!("{err}"),
                },
            }
        }
        assert_eq!(n, cfg.master.server.client_rate_limit);
    }
}
