use std::{
    net::{Ipv4Addr, SocketAddr, SocketAddrV4, UdpSocket},
    sync::atomic::AtomicBool,
    thread,
};

use xash3d_master::{Config, MasterServer};
use xash3d_protocol::{filter::Filter, game, master, server, wrappers::Str};

#[test]
fn server_add() {
    // create master
    let cfg = Config::default();
    let addr = SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0);
    let mut master = MasterServer::new(cfg.clone(), addr).unwrap();
    let master_addr = master.local_addr().unwrap();
    let sig_flag = AtomicBool::new(false);
    thread::spawn(move || master.run(&sig_flag).unwrap());

    let mut buf = [0; 1024];

    // add server
    let sock = UdpSocket::bind(addr).unwrap();
    let SocketAddr::V4(server_addr) = sock.local_addr().unwrap() else {
        todo!()
    };
    let challenge = Some(0xdeadbeef);
    let p = server::Challenge::new(challenge);
    let l = p.encode(&mut buf).unwrap();
    sock.send_to(&buf[..l], master_addr).unwrap();

    let (l, _) = sock.recv_from(&mut buf).unwrap();
    let r = master::ChallengeResponse::decode(&buf[..l]).unwrap();
    assert_eq!(r.server_challenge, challenge);

    let p = server::ServerAdd {
        gamedir: "valve",
        map: "crossfile",
        version: cfg.server.min_version,
        challenge: r.master_challenge,
        server_type: server::ServerType::Dedicated,
        os: server::Os::Linux,
        region: server::Region::RestOfTheWorld,
        protocol: xash3d_protocol::PROTOCOL_VERSION,
        players: 8,
        max: 32,
        flags: server::ServerFlags::empty(),
    };
    let l = p.encode(&mut buf).unwrap();
    sock.send_to(&buf[..l], master_addr).unwrap();

    // query servers
    let sock = UdpSocket::bind(addr).unwrap();
    let game_key = Some(0xbeefdead);
    let p = game::QueryServers {
        region: server::Region::RestOfTheWorld,
        last: addr.into(),
        filter: Filter {
            gamedir: Some(Str(b"valve")),
            clver: Some(cfg.client.min_version),
            protocol: Some(xash3d_protocol::PROTOCOL_VERSION),
            client_os: Some(Str(b"linux")),
            client_arch: Some(Str(b"amd64")),
            client_buildnum: Some(cfg.client.min_engine_buildnum),
            key: game_key,
            ..Filter::default()
        },
    };
    let l = p.encode(&mut buf).unwrap();
    sock.send_to(&buf[..l], master_addr).unwrap();

    let (l, _) = sock.recv_from(&mut buf).unwrap();
    let r = master::QueryServersResponse::decode(&buf[..l]).unwrap();
    assert_eq!(r.key, game_key);
    let servers = r.iter::<SocketAddrV4>().collect::<Vec<_>>();
    assert_eq!(servers.len(), 1);
    assert_eq!(servers[0].port(), server_addr.port());
}
