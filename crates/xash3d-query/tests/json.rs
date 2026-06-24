use std::{process::Command, str};

use serde::Deserialize;
use xash3d_test_utils::server::FakeServer;

const QUERY_PATH: &str = env!("CARGO_BIN_EXE_xash3d-query");

#[derive(Debug, Deserialize, PartialEq, Eq)]
struct ServerResult {
    // ignore time: u32,
    // ignore ping: Duration,
    address: String,
    status: String,
    gamedir: String,
    map: String,
    host: String,
    protocol: u8,
    numcl: u8,
    maxcl: u8,
    // ignore dm: bool,
    // ignore team: bool,
    // ignore coop: bool,
    password: bool,
    dedicated: bool,
}

#[derive(Debug, Deserialize)]
struct QueryResult {
    servers: Vec<ServerResult>,
}

#[test]
fn query_json() {
    let mut query = Command::new(QUERY_PATH);
    query.args(["info", "-j", "-P"]);

    let fake_servers = [
        FakeServer::new(48),
        FakeServer::new(49),
        FakeServer::new_gs(false, false),
        FakeServer::new_gs(true, false),
        FakeServer::new_gs(false, true),
        FakeServer::new_gs(true, true),
    ];
    let mut expect = Vec::new();
    for server in fake_servers {
        let server = ServerResult {
            status: String::from("ok"),
            gamedir: server.gamedir().to_string(),
            map: server.map().to_string(),
            host: server.name().to_string(),
            protocol: server.protocol(),
            numcl: server.players(),
            maxcl: server.max_players(),
            password: server.password(),
            dedicated: server.dedicated(),
            address: server.run().to_string(),
        };
        println!("FAKE SERVER: {} {}", server.address, server.host);
        query.arg(&server.address);
        expect.push(server);
    }

    let output = query.output().unwrap();
    if !output.stderr.is_empty() {
        println!("stderr:");
        println!("{}", str::from_utf8(&output.stderr).unwrap());
    }

    if !output.status.success() {
        panic!("error: query failed with status {}", output.status);
    }

    let result = serde_json::from_slice::<QueryResult>(&output.stdout).unwrap();
    for expect in &expect {
        let server = result
            .servers
            .iter()
            .find(|server| server.address == expect.address)
            .unwrap();
        assert_eq!(server, expect);
        println!("CHECKED: {} {}", server.address, server.host);
    }
}
