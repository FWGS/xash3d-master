use std::{
    collections::{HashMap, HashSet},
    io,
    time::{Duration, Instant},
};

use xash3d_observer::{event::Event, Buffer, Observer, Server};
use xash3d_test_utils::{logger::init_logger, server::FakeServer};

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
        let name = server.name().to_string();
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
