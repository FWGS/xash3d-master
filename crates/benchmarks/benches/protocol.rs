use std::{
    fmt::Write,
    hint::black_box,
    net::{Ipv4Addr, Ipv6Addr, SocketAddrV4, SocketAddrV6},
};

use criterion::{criterion_group, criterion_main, measurement::WallTime, Criterion, Throughput};
use xash3d_protocol::{
    cursor::{Cursor, CursorError, CursorMut},
    filter::Filter,
    game,
    map::MapIter,
    master, server,
    wrappers::Str,
    CLIENT_VERSION, PROTOCOL_VERSION,
};

type BenchmarkGroup<'a> = criterion::BenchmarkGroup<'a, WallTime>;

const UNSPECIFIED_V4: SocketAddrV4 = SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0);
const UNSPECIFIED_V6: SocketAddrV6 = SocketAddrV6::new(Ipv6Addr::UNSPECIFIED, 0, 0, 0);

fn gen_input<T>(len: usize, f: impl Fn(usize) -> T) -> Vec<T> {
    (0..len).map(f).collect()
}

fn bench_get_bytes(group: &mut BenchmarkGroup) {
    const M: usize = 8;
    const N: usize = 8;

    fn func<'a>(buf: &mut [&'a [u8]; M], src: &'a [u8]) -> Result<(), CursorError> {
        let mut cur = Cursor::new(src);
        assert_eq!(M, 8);
        buf[0] = cur.get_bytes(N)?;
        buf[1] = cur.get_bytes(N)?;
        buf[2] = cur.get_bytes(N)?;
        buf[3] = cur.get_bytes(N)?;
        buf[4] = cur.get_bytes(N)?;
        buf[5] = cur.get_bytes(N)?;
        buf[6] = cur.get_bytes(N)?;
        buf[7] = cur.get_bytes(N)?;
        cur.expect_empty()
    }

    let src = gen_input(M * N, |i| i as u8);
    let mut buf: [&[u8]; M] = [&[]; M];
    group.throughput(Throughput::Elements(M as u64));
    group.bench_function(format!("get_bytes/{M}"), |b| {
        // check errors
        func(&mut buf, &src).unwrap();

        b.iter(|| func(black_box(&mut buf), black_box(&src)))
    });
}

fn bench_get_array<const N: usize>(group: &mut BenchmarkGroup) {
    const M: usize = 8;

    fn func<const N: usize>(buf: &mut [[u8; N]; M], src: &[u8]) -> Result<(), CursorError> {
        let mut cur = Cursor::new(src);
        assert_eq!(M, 8);
        buf[0] = cur.get_array()?;
        buf[1] = cur.get_array()?;
        buf[2] = cur.get_array()?;
        buf[3] = cur.get_array()?;
        buf[4] = cur.get_array()?;
        buf[5] = cur.get_array()?;
        buf[6] = cur.get_array()?;
        buf[7] = cur.get_array()?;
        cur.expect_empty()
    }

    let src = gen_input(M * N, |i| i as u8);
    let mut buf = [[0_u8; N]; M];
    group.throughput(Throughput::Bytes((M * N) as u64));
    group.bench_function(format!("get_array/{M}x{N}"), |b| {
        // check errors
        func::<N>(&mut buf, &src).unwrap();

        b.iter(|| func::<N>(black_box(&mut buf), black_box(&src)));
    });
}

fn bench_cursor_read(c: &mut Criterion) {
    let mut group = c.benchmark_group("Cursor");
    bench_get_bytes(&mut group);

    // Results should be similar to put_bytes benchmarks.
    bench_get_array::<1>(&mut group);
    bench_get_array::<2>(&mut group);
    bench_get_array::<4>(&mut group);
    bench_get_array::<8>(&mut group);
}

fn bench_put_bytes<const N: usize>(group: &mut BenchmarkGroup) {
    const M: usize = 8;

    fn func<const N: usize>(buf: &mut [u8], src: &[[u8; N]]) -> Result<(), CursorError> {
        let mut cur = CursorMut::new(buf);
        assert_eq!(M, 8);
        cur.put_bytes(&src[0])?;
        cur.put_bytes(&src[1])?;
        cur.put_bytes(&src[2])?;
        cur.put_bytes(&src[3])?;
        cur.put_bytes(&src[4])?;
        cur.put_bytes(&src[5])?;
        cur.put_bytes(&src[6])?;
        cur.put_bytes(&src[7])?;
        cur.expect_full()
    }

    let src = gen_input(M, |i| [i as u8; N]);
    let mut buf = vec![0; M * N];
    group.throughput(Throughput::Bytes((M * N) as u64));
    group.bench_function(format!("put_bytes/{M}x{N}"), |b| {
        // check errors
        func::<N>(&mut buf, &src).unwrap();

        b.iter(|| func::<N>(black_box(&mut buf), black_box(&src)))
    });
}

fn bench_cursor_write(c: &mut Criterion) {
    let mut group = c.benchmark_group("CursorMut");

    // Results should be similar to get_array benchmarks.
    bench_put_bytes::<1>(&mut group);
    bench_put_bytes::<2>(&mut group);
    bench_put_bytes::<4>(&mut group);
    bench_put_bytes::<8>(&mut group);
}

const FILTER_SHORT: &str = "\
    \\gamedir\\valve\
    \\map\\crossfire\
    \\protocol\\49\
    \\clver\\0.21\
    \\key\\12345\
    \\secure\\1\
    \\empty\\1\
    \\full\\0\
    \\noplayers\\1\
    \\bots\\0\
    \\password\\1\
    \\dedicated\\1\
    \\os\\w\
    \\nat\\1\
    \\lan\\0";

const FILTER_LONG: &str = "\
   \\gamedir\\cstrike\
   \\map\\dust\
   \\protocol\\49\
   \\clver\\0.21\
   \\dedicated\\1\
   \\secure\\1\
   \\key\\deadbeef\
   \\empty\\0\
   \\full\\0\
   \\foobar\\123abc\
   \\password\\0\
   \\noplayers\\0\
   \\os\\l\
   \\arch\\x86_64\
   \\branch\\bench\
   \\commit\\a0763a14199b9b43aeca82f763b0259e724a068e\
   \\buildnum\\5000\
   \\nat\\0\
   \\lan\\0\
   \\bots\\0";

fn bench_map_iter(c: &mut Criterion) {
    let mut group = c.benchmark_group("MapIter");
    for (expected_count, raw) in [(15, FILTER_SHORT), (20, FILTER_LONG)] {
        let raw = raw.as_bytes();

        // check errors
        let mut count = 0;
        for i in MapIter::from_slice(raw).unwrap() {
            i.unwrap();
            count += 1;
        }
        assert_eq!(count, expected_count);

        group.throughput(Throughput::ElementsAndBytes {
            elements: count,
            bytes: raw.len() as u64,
        });
        group.bench_function(format!("{}", raw.len()), |b| {
            b.iter(|| MapIter::from_slice(black_box(raw)).unwrap().count())
        });
    }
}

fn bench_filter(c: &mut Criterion) {
    let mut group = c.benchmark_group("Filter");
    for raw in [FILTER_SHORT, FILTER_LONG] {
        let raw = raw.as_bytes();

        // check errors
        let filter = Filter::from_slice(raw).unwrap();

        group.throughput(Throughput::Bytes(raw.len() as u64));
        group.bench_function(format!("parse/{}", raw.len()), |b| {
            b.iter(|| Filter::from_slice(black_box(raw)))
        });

        group.bench_function(format!("fmt/{}", raw.len()), |b| {
            let mut buf = String::with_capacity(raw.len());
            b.iter(|| {
                buf.clear();
                write!(&mut buf, "{}", black_box(&filter)).unwrap();
                black_box(buf.as_bytes());
                buf.len()
            })
        });
    }
}

fn bench_str_wrapper(c: &mut Criterion) {
    let mut group = c.benchmark_group("Str");
    for src in [FILTER_SHORT, FILTER_LONG] {
        let src = src.as_bytes();
        group.throughput(Throughput::Bytes(src.len() as u64));
        group.bench_function(format!("fmt/{}", src.len()), |b| {
            let mut buf = String::with_capacity(src.len());
            b.iter(|| {
                buf.clear();
                write!(&mut buf, "{}", black_box(Str(src))).unwrap();
                black_box(buf.as_bytes());
                buf.len()
            })
        });
    }
}

fn bench_master_query_servers_response(group: &mut BenchmarkGroup) {
    enum ServerList<'a> {
        V4(&'a [SocketAddrV4]),
        V6(&'a [SocketAddrV6]),
    }

    let runs = [
        (512, ServerList::V4(&[UNSPECIFIED_V4; 90][..]), 82),
        (512, ServerList::V4(&[]), 0),
        (1280, ServerList::V6(&[UNSPECIFIED_V6; 90][..]), 69),
        (1280, ServerList::V6(&[]), 0),
    ];
    let mut buf: Vec<u8> = vec![];
    for (capacity, list, expected_count) in runs {
        buf.resize(capacity, 0);
        let buf = &mut buf[..];

        let key = Some(0x12345678);
        let msg = master::QueryServersResponse::new(key);

        // check errors
        let (data, count) = match list {
            ServerList::V4(list) => msg.encode(buf, list).unwrap(),
            ServerList::V6(list) => msg.encode(buf, list).unwrap(),
        };
        assert_eq!(count, expected_count);
        group.throughput(Throughput::Bytes(data.len() as u64));

        let version = match list {
            ServerList::V4(..) => "ipv4",
            ServerList::V6(..) => "ipv6",
        };
        let name = format!("QueryServersResponse/{version}/encode/{}", data.len());
        group.bench_function(name, |b| {
            match list {
                ServerList::V4(list) => {
                    b.iter(|| {
                        let msg = black_box(&msg);
                        let result = msg.encode(black_box(buf), black_box(list));
                        let _ = black_box(result);
                    });
                }
                ServerList::V6(list) => {
                    b.iter(|| {
                        let msg = black_box(&msg);
                        let result = msg.encode(black_box(buf), black_box(list));
                        let _ = black_box(result);
                    });
                }
            };
        });
    }
}

fn bench_master_packets(c: &mut Criterion) {
    let mut group = c.benchmark_group("master");
    bench_master_query_servers_response(&mut group);
}

fn bench_game_query_servers(group: &mut BenchmarkGroup) {
    for raw in [FILTER_LONG, FILTER_SHORT] {
        let filter = Filter::try_from(raw.as_bytes()).unwrap();
        let msg = game::QueryServers::new(filter);
        let mut buf = [0; 1024];
        let data = msg.encode(&mut buf).unwrap();
        group.throughput(Throughput::Bytes(data.len() as u64));

        // check errors
        let tmp = game::QueryServers::<Filter>::decode(data).unwrap();
        assert_eq!(tmp, msg);

        let name = format!("QueryServers/decode/{}", data.len());
        group.bench_function(name, |b| {
            b.iter(|| game::QueryServers::<Filter>::decode(black_box(data)));
        });
    }
}

fn bench_game_packets(c: &mut Criterion) {
    let mut group = c.benchmark_group("game");
    bench_game_query_servers(&mut group);
}

fn bench_server_add(group: &mut BenchmarkGroup) {
    let msg = server::ServerAdd {
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
        bots: 1,
        flags: server::ServerFlags::all(),
    };

    let mut buf = [0; 1024];
    let data = msg.encode(&mut buf).unwrap();
    group.throughput(Throughput::Bytes(data.len() as u64));

    // check errors
    let tmp = server::ServerAdd::decode(data).unwrap();
    assert_eq!(tmp, msg);

    let name = format!("ServerAdd/decode/{}", data.len());
    group.bench_function(name, |b| {
        b.iter(|| server::ServerAdd::decode(black_box(data)));
    });
}

fn bench_get_server_info_response(group: &mut BenchmarkGroup) {
    let msg = server::GetServerInfoResponse {
        gamedir: Str(b"valve"),
        map: Str(b"crossfire"),
        host: Str(b"Server title"),
        protocol: PROTOCOL_VERSION,
        numcl: 8,
        maxcl: 32,
        dm: true,
        team: true,
        coop: false,
        password: false,
        dedicated: true,
    };

    let mut buf = [0; 1024];
    let data = msg.encode(&mut buf).unwrap();
    group.throughput(Throughput::Bytes(data.len() as u64));

    // check errors
    let tmp = server::GetServerInfoResponse::decode(data).unwrap();
    assert_eq!(tmp, msg);

    let name = format!("GetServerInfoResponse/decode/{}", data.len());
    group.bench_function(name, |b| {
        b.iter(|| server::GetServerInfoResponse::decode(black_box(data)));
    });
}

fn bench_server_packets(c: &mut Criterion) {
    let mut group = c.benchmark_group("server");
    bench_server_add(&mut group);
    bench_get_server_info_response(&mut group);
}

fn criterion_benchmark(c: &mut Criterion) {
    bench_cursor_read(c);
    bench_cursor_write(c);
    bench_map_iter(c);
    bench_filter(c);
    bench_str_wrapper(c);
    bench_master_packets(c);
    bench_game_packets(c);
    bench_server_packets(c);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
