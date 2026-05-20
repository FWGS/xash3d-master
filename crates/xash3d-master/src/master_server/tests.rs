use std::{
    io,
    net::{Ipv4Addr, SocketAddr, SocketAddrV4, UdpSocket},
    thread,
    time::Duration,
};

use xash3d_protocol::{
    filter::{Filter, Version},
    game::{self, QueryServers},
    master,
    server::{self, Region},
    wrappers::Str,
};

use crate::{
    master_server::{MasterServer, ServerInfo},
    Config,
};

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
    fn new() -> Test {
        Test {
            master_addr: UNSPECIFIED.into(),
            server_addr: UNSPECIFIED.into(),
        }
    }

    fn with_master(cfg: &Config) -> Test {
        let mut test = Self::new();
        test.create_master(cfg);
        test
    }

    fn with_master_and_server(cfg: &Config) -> Test {
        let mut test = Self::with_master(cfg);
        test.add_server(cfg);
        test
    }

    fn create_master(&mut self, cfg: &Config) {
        let mut master = MasterServer::new(cfg.clone(), UNSPECIFIED).unwrap();
        self.master_addr = master.local_addr().unwrap();
        thread::spawn(move || master.run().unwrap());
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
            gamedir: Str(b"valve"),
            map: Str(b"crossfire"),
            version: cfg.master.server.min_version,
            challenge: r.master_challenge,
            server_type: server::ServerType::Dedicated,
            os: server::Os::Linux,
            region: server::Region::RestOfTheWorld,
            protocol: xash3d_protocol::PROTOCOL_VERSION,
            players: 8,
            max: 32,
            bots: 0,
            flags: server::ServerFlags::empty(),
        };
        let p = p.encode(&mut buf).unwrap();
        sock.send_to(p, self.master_addr).unwrap();
    }
}

#[test]
fn check_remove_server_by_ip() {
    use server::{Os, ServerAdd, ServerFlags, ServerType};

    let cfg = Config::default();
    let mut master = MasterServer::new(cfg, UNSPECIFIED).unwrap();

    let server_add = ServerAdd {
        gamedir: Str(b"valve"),
        map: Str(b"crossfire"),
        version: Version::new(0, 20),
        challenge: 0x12345678,
        server_type: ServerType::Dedicated,
        os: Os::Linux,
        region: Region::RestOfTheWorld,
        protocol: 49,
        players: 4,
        max: 32,
        bots: 8,
        flags: ServerFlags::all(),
    };
    let info = ServerInfo::new(&server_add);

    for i in 1..=4 {
        let ip = Ipv4Addr::new(1, 1, 1, i);
        for j in 0..4 {
            let addr = SocketAddrV4::new(ip, 27015 + j);
            master.add_server(addr, info.clone());
        }
    }

    assert_eq!(master.count_all_servers(), 16);

    master.admin_command("ban 2.2.2.2");
    assert_eq!(master.count_all_servers(), 16);

    master.admin_command("ban 1.1.1.1");
    assert_eq!(master.count_all_servers(), 12);

    master.admin_command("ban 1.1.1.2");
    assert_eq!(master.count_all_servers(), 8);

    master.admin_command("ban 1.1.1.3");
    assert_eq!(master.count_all_servers(), 4);

    master.admin_command("ban 1.1.1.4");
    assert_eq!(master.count_all_servers(), 0);
}

#[test]
fn check_query_servers() {
    const BUILDNUM_NEW: u32 = 3500;
    const BUILDNUM_OLD: u32 = 3000;

    let mut cfg = Config::default();
    cfg.master.client.min_version = Version::new(0, 19);
    cfg.master.client.min_engine_buildnum = BUILDNUM_NEW;
    cfg.master.client.min_old_engine_buildnum = BUILDNUM_OLD;

    let addr = SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0);
    let master = MasterServer::new(cfg, addr).unwrap();

    let mut query = QueryServers::default();

    // check missing fields
    assert!(!master.is_query_servers_valid(&addr, &query));

    query.filter.clver = Some(Version::new(0, 21));
    query.filter.client_buildnum = None;
    assert!(!master.is_query_servers_valid(&addr, &query));

    query.filter.clver = None;
    query.filter.client_buildnum = Some(BUILDNUM_NEW);
    assert!(!master.is_query_servers_valid(&addr, &query));

    // check engine buildnum
    query.filter.clver = Some(Version::new(0, 21));
    query.filter.client_buildnum = Some(BUILDNUM_NEW);
    assert!(master.is_query_servers_valid(&addr, &query));
    query.filter.client_buildnum = Some(BUILDNUM_NEW - 1);
    assert!(!master.is_query_servers_valid(&addr, &query));

    // check engine buildnum
    query.filter.clver = Some(Version::new(0, 19));
    query.filter.client_buildnum = Some(BUILDNUM_OLD);
    assert!(master.is_query_servers_valid(&addr, &query));
    query.filter.client_buildnum = Some(BUILDNUM_OLD - 1);
    assert!(!master.is_query_servers_valid(&addr, &query));
}

#[test]
fn server_add() {
    log::set_logger(&LOGGER).ok();
    log::set_max_level(log::LevelFilter::Trace);

    let cfg = Config::default();
    let test = Test::with_master_and_server(&cfg);
    let mut buf = [0; 1024];
    let sock = UdpSocket::bind(UNSPECIFIED).unwrap();
    let game_key = Some(0xbeefdead);
    let p = game::QueryServers::new(Filter {
        gamedir: Some(Str(b"valve")),
        clver: Some(xash3d_protocol::CLIENT_VERSION),
        client_os: Some(Str(b"linux")),
        client_arch: Some(Str(b"amd64")),
        client_buildnum: Some(cfg.master.client.min_engine_buildnum),
        key: game_key,
        ..Filter::default()
    });
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
fn server_reuse_challenge() {
    log::set_logger(&LOGGER).ok();
    log::set_max_level(log::LevelFilter::Trace);

    let test = Test::with_master(&Config::default());
    let sock = UdpSocket::bind(UNSPECIFIED).unwrap();
    let mut challenges = [0; 3];
    for (i, j) in challenges.iter_mut().enumerate() {
        let challenge = Some(i as u32);
        let packet = server::Challenge::new(challenge);
        let mut buf = [0; 512];
        let p = packet.encode(&mut buf).unwrap();
        sock.send_to(p, test.master_addr).unwrap();

        let (len, _) = sock.recv_from(&mut buf).unwrap();
        let resp = master::ChallengeResponse::decode(&buf[..len]).unwrap();
        assert_eq!(resp.server_challenge, challenge);
        *j = resp.master_challenge;
    }

    assert!(challenges.iter().all(|i| *i == challenges[0]));
}

#[test]
fn client_rate_limit() {
    log::set_logger(&LOGGER).ok();
    log::set_max_level(log::LevelFilter::Trace);

    let mut cfg = Config::default();
    cfg.master.server.client_rate_limit = 10;
    info!("client rate limit {}", cfg.master.server.client_rate_limit);

    let test = Test::with_master_and_server(&cfg);
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
        let p = game::QueryServers::new(Filter {
            gamedir: Some(Str(b"valve")),
            clver: Some(xash3d_protocol::CLIENT_VERSION),
            client_os: Some(Str(b"linux")),
            client_arch: Some(Str(b"amd64")),
            client_buildnum: Some(cfg.master.client.min_engine_buildnum),
            key: game_key,
            ..Filter::default()
        });
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
