use std::{
    fmt::Write,
    hint::black_box,
    net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6},
};

use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion, Throughput,
};
use xash3d_protocol::{
    admin,
    filter::{Filter, FilterFlags},
    game, master,
    server::{self, PlayerInfo, Region},
    wrappers::{Hide, Str, StrSlice},
    Error, CLIENT_VERSION, PROTOCOL_VERSION,
};

const UNSPECIFIED_V4: SocketAddrV4 = SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0);
const UNSPECIFIED_V6: SocketAddrV6 = SocketAddrV6::new(Ipv6Addr::UNSPECIFIED, 0, 0, 0);
const UNSPECIFIED: SocketAddr = SocketAddr::V4(UNSPECIFIED_V4);

struct Group<'a> {
    group: BenchmarkGroup<'a, WallTime>,
}

impl<'a> Group<'a> {
    fn new(c: &'a mut Criterion, name: impl Into<String>) -> Self {
        Self {
            group: c.benchmark_group(name),
        }
    }

    fn bench<D, E>(&mut self, name: &str, decode: D, encode: E)
    where
        D: Fn(&[u8]),
        E: Fn(&mut [u8]) -> Result<&[u8], Error>,
    {
        let buf = &mut [0; 2048][..];
        let data = encode(buf).unwrap();
        self.group.throughput(Throughput::Bytes(data.len() as u64));
        self.group
            .bench_function(format!("{name}/decode/{}", data.len()), |b| {
                b.iter(|| {
                    decode(black_box(data));
                });
            });
        self.group
            .bench_function(format!("{name}/encode/{}", data.len()), |b| {
                b.iter(|| {
                    black_box(encode(black_box(buf)).unwrap());
                });
            });
    }

    #[allow(dead_code)]
    fn finish(self) {
        self.group.finish();
    }
}

fn benchmark_filter(c: &mut Criterion) {
    let mut group = c.benchmark_group("filter");
    let mut bench = |raw: &[u8]| {
        group.throughput(Throughput::Bytes(raw.len() as u64));
        group.bench_function(format!("decode/{}", raw.len()), |b| {
            b.iter(|| {
                black_box(Filter::try_from(black_box(raw)).unwrap());
            })
        });

        let filter = Filter::try_from(raw).unwrap();
        let mut buf = String::with_capacity(raw.len());
        group.bench_function(format!("encode/{}", raw.len()), |b| {
            b.iter(|| {
                buf.clear();
                write!(&mut buf, "{}", black_box(&filter)).unwrap();
                black_box(&buf);
            })
        });
    };

    let mut raw = String::new();
    raw.push_str("\\gamedir\\valve");
    raw.push_str("\\map\\crossfire");
    raw.push_str("\\protocol\\49");
    raw.push_str("\\clver\\0.21");
    raw.push_str("\\key\\12345");
    raw.push_str("\\secure\\1");
    raw.push_str("\\empty\\1");
    raw.push_str("\\full\\0");
    raw.push_str("\\noplayers\\1");
    raw.push_str("\\bots\\0");
    raw.push_str("\\password\\1");
    raw.push_str("\\dedicated\\1");
    raw.push_str("\\os\\w");
    raw.push_str("\\nat\\1");
    raw.push_str("\\lan\\0");
    bench(raw.as_bytes());

    let mut raw = String::new();
    raw.push_str("\\gamedir\\cstrike");
    raw.push_str("\\map\\dust");
    raw.push_str("\\protocol\\49");
    raw.push_str("\\clver\\0.21");
    raw.push_str("\\dedicated\\1");
    raw.push_str("\\secure\\1");
    raw.push_str("\\key\\deadbeef");
    raw.push_str("\\empty\\0");
    raw.push_str("\\full\\0");
    raw.push_str("\\foobar\\123abc");
    raw.push_str("\\password\\0");
    raw.push_str("\\noplayers\\0");
    raw.push_str("\\os\\l");
    raw.push_str("\\arch\\x86_64");
    raw.push_str("\\branch\\bench");
    raw.push_str("\\commit\\a0763a14199b9b43aeca82f763b0259e724a068e");
    raw.push_str("\\buildnum\\5000");
    raw.push_str("\\nat\\0");
    raw.push_str("\\lan\\0");
    raw.push_str("\\bots\\0");
    bench(raw.as_bytes());
}

fn benchmark_master_packets(c: &mut Criterion) {
    fn decode(buf: &[u8]) {
        black_box(master::Packet::decode(buf).unwrap().unwrap());
    }

    fn decode_query_servers_response<A: master::ServerAddress>(buf: &[u8]) {
        let result = master::Packet::decode(buf);
        let master::Packet::QueryServersResponse(list) = result.unwrap().unwrap() else {
            panic!();
        };
        for i in list.iter::<A>() {
            black_box(i);
        }
    }

    let mut group = Group::new(c, "master");

    let msg = master::ChallengeResponse::new(0x12345678, Some(0xdeadbeef));
    group.bench("ChallengeResponse", decode, |buf| msg.encode(buf));

    let empty = [];
    group.bench(
        "QueryServersResponseV4",
        decode_query_servers_response::<SocketAddrV4>,
        |buf| {
            let mut msg = master::QueryServersResponse::new(Some(0x12345678));
            let (buf, count) = msg.encode::<SocketAddrV4>(buf, &empty)?;
            black_box(count);
            Ok(buf)
        },
    );

    let list = [UNSPECIFIED_V4; 50];
    group.bench(
        "QueryServersResponseV4",
        decode_query_servers_response::<SocketAddrV4>,
        |buf| {
            let mut msg = master::QueryServersResponse::new(Some(0x12345678));
            let (buf, count) = msg.encode::<SocketAddrV4>(buf, &list)?;
            black_box(count);
            Ok(buf)
        },
    );

    let empty = [];
    group.bench(
        "QueryServersResponseV6",
        decode_query_servers_response::<SocketAddrV6>,
        |buf| {
            let mut msg = master::QueryServersResponse::new(Some(0x12345678));
            let (buf, count) = msg.encode::<SocketAddrV6>(buf, &empty)?;
            black_box(count);
            Ok(buf)
        },
    );

    let list = [UNSPECIFIED_V6; 50];
    group.bench(
        "QueryServersResponseV6",
        decode_query_servers_response::<SocketAddrV6>,
        |buf| {
            let mut msg = master::QueryServersResponse::new(Some(0x12345678));
            let (buf, count) = msg.encode::<SocketAddrV6>(buf, &list)?;
            black_box(count);
            Ok(buf)
        },
    );

    let addr = "123.234.210.132:12345".parse().unwrap();
    let msg = master::ClientAnnounce::new(addr);
    group.bench("ClientAnnounce", decode, |buf| msg.encode(buf));

    let msg = master::AdminChallengeResponse::new(0x12345678, 0xdeadbeef);
    group.bench("AdminChallengeResponse", decode, |buf| msg.encode(buf));
}

fn benchmark_game_packets(c: &mut Criterion) {
    type QueryServers<'a> = game::QueryServers<Filter<'a>>;

    fn decode(buf: &[u8]) {
        black_box(game::Packet::decode(buf).unwrap().unwrap());
    }

    let mut group = Group::new(c, "game");

    let msg = QueryServers {
        region: Region::RestOfTheWorld,
        last: UNSPECIFIED,
        filter: Filter {
            gamedir: Some(Str(b"valve")),
            clver: Some(CLIENT_VERSION),
            protocol: Some(PROTOCOL_VERSION),
            key: Some(0xdeadbeef),
            ..Filter::default()
        },
    };
    group.bench("QueryServers", decode, |buf| msg.encode(buf));

    let msg = QueryServers {
        region: server::Region::RestOfTheWorld,
        last: UNSPECIFIED,
        filter: Filter {
            gamedir: Some(Str(b"valve")),
            map: Some(Str(b"crossfire")),
            clver: Some(CLIENT_VERSION),
            protocol: Some(PROTOCOL_VERSION),
            client_os: Some(Str(b"l")),
            client_arch: Some(Str(b"x86")),
            client_branch: Some(Str(b"bench")),
            client_commit: Some(Str(b"1c754558d8fc9757a3d456bb59ac386ad7650609")),
            client_buildnum: Some(8000),
            key: Some(0xdeadbeef),
            flags: FilterFlags::all(),
            flags_mask: FilterFlags::all(),
        },
    };
    group.bench("QueryServers", decode, |buf| msg.encode(buf));

    let msg = game::GetChallenge::new();
    group.bench("GetChallenge", decode, |buf| msg.encode(buf));

    let msg = game::GetServerInfo::new(PROTOCOL_VERSION);
    group.bench("GetServerInfo", decode, |buf| msg.encode(buf));

    let msg = game::GetServerInfo2::with_challenge(0x12345678);
    group.bench("GetServerInfo2", decode, |buf| msg.encode(buf));

    let msg = game::GetPlayers::new(0x87654321).unwrap();
    group.bench("GetPlayers", decode, |buf| msg.encode(buf));
}

fn benchmark_server_packets(c: &mut Criterion) {
    fn decode(buf: &[u8]) {
        black_box(server::Packet::decode(buf).unwrap().unwrap());
    }

    let mut group = Group::new(c, "server");

    let msg = server::Challenge::new(Some(0x87654321));
    group.bench("Challenge", decode, |buf| msg.encode(buf));

    let msg = server::ServerAdd::<StrSlice> {
        gamedir: Str(b"valve"),
        map: Str(b"crossfire"),
        version: CLIENT_VERSION,
        challenge: 0xdeadbeef,
        server_type: server::ServerType::Dedicated,
        os: server::Os::Linux,
        region: server::Region::RestOfTheWorld,
        protocol: PROTOCOL_VERSION,
        players: 8,
        max: 32,
        bots: 0,
        flags: server::ServerFlags::all(),
    };
    group.bench("ServerAdd", decode, |buf| msg.encode(buf));

    let msg = server::ServerRemove;
    group.bench("ServerRemove", decode, |buf| msg.encode(buf));

    let msg = server::GetChallengeResponse::new(0x12345678);
    group.bench("GetChallengeResponse", decode, |buf| msg.encode(buf));

    let msg = server::GetServerInfoResponse::<StrSlice> {
        gamedir: Str(b"valve"),
        map: Str(b"crossfire"),
        host: Str(b"Test server title"),
        protocol: PROTOCOL_VERSION,
        numcl: 8,
        maxcl: 32,
        dm: true,
        team: true,
        coop: false,
        password: false,
        dedicated: true,
    };
    group.bench("GetChallengeResponse", decode, |buf| msg.encode(buf));

    let msg = server::GetServerInfo2Response {
        protocol: PROTOCOL_VERSION,
        host: Str(b"Test server title"),
        map: Str(b"crossfire"),
        gamedir: Str(b"valve"),
        game: Str(b"Half-Life"),
        app_id: 123,
        players: 4,
        max_players: 32,
        bots: 1,
        ty: server::ServerType::Dedicated,
        os: server::Os::Windows,
        password: false,
        secure: true,
        version: Str(b"1.2.3-r1"),
        port: Some(27015),
        steam_id: Some(123),
        source_tv: None,
        keywords: Some(Str(b"abc 123")),
    };
    group.bench("GetServerInfo2Response", decode, |buf| msg.encode(buf));

    let msg = server::GetServerInfo2ResponseOld {
        address: Str(b"123.123.123.123:27016"),
        host: Str(b"Test server title"),
        map: Str(b"crossfire"),
        gamedir: Str(b"valve"),
        game: Str(b"Half-Life"),
        players: 4,
        max_players: 32,
        protocol: PROTOCOL_VERSION,
        ty: server::ServerType::Dedicated,
        os: server::Os::Windows,
        password: false,
        mod_info: None,
        secure: true,
        bots: 1,
    };
    group.bench("GetServerInfo2ResponseOld", decode, |buf| msg.encode(buf));

    let players = [
        PlayerInfo::new(0, "freeman", 123, 100.0),
        PlayerInfo::new(1, "calhoun", 1, 123.0),
        PlayerInfo::new(2, "gman", 0, -1.0),
        PlayerInfo::new(3, "alex", 100, -1.0),
    ];
    let msg = server::GetPlayersResponse::new(players.iter().copied());
    group.bench(
        "GetPlayersResponse",
        |buf| {
            let players = server::GetPlayersResponse::decode(buf).unwrap();
            for i in players.players() {
                black_box(i.unwrap());
            }
        },
        |buf| msg.clone().encode(buf),
    );
}

fn benchmark_admin_packets(c: &mut Criterion) {
    const HASH_LEN: usize = 64;

    fn decode(buf: &[u8]) {
        black_box(admin::Packet::decode(HASH_LEN, buf).unwrap().unwrap());
    }

    let mut group = Group::new(c, "admin");

    let msg = admin::AdminChallenge;
    group.bench("AdminChallenge", decode, |buf| msg.encode(buf));

    let msg = admin::AdminCommand {
        master_challenge: 0x12345678,
        hash: Hide(&[1; HASH_LEN]),
        command: "foobar 123 baz quux",
    };
    group.bench("AdminCommand", decode, |buf| msg.encode(buf));
}

fn criterion_benchmark(c: &mut Criterion) {
    benchmark_filter(c);
    benchmark_master_packets(c);
    benchmark_game_packets(c);
    benchmark_server_packets(c);
    benchmark_admin_packets(c);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
