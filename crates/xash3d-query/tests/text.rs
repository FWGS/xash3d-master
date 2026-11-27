use std::{
    io::{BufRead, BufReader},
    process::{Command, Stdio},
    str,
    sync::mpsc,
    thread,
    time::Duration,
};

use xash3d_test_utils::server::FakeServer;

const QUERY_PATH: &str = env!("CARGO_BIN_EXE_xash3d-query");

// the .invalid TLD is reserved and never resolves
const UNRESOLVED: &str = "unresolved.invalid:27015";

const LINE_TIMEOUT: Duration = Duration::from_secs(10);

/// An address that cannot be resolved must not prevent other servers from being queried.
#[test]
fn query_text_unresolved() {
    let server = FakeServer::new(49);
    let name = server.name().to_string();
    let server = server.run().to_string();

    let output = Command::new(QUERY_PATH)
        .args(["info", "-P", UNRESOLVED, &server])
        .output()
        .unwrap();

    if !output.status.success() {
        panic!("error: query failed with status {}", output.status);
    }

    let stdout = str::from_utf8(&output.stdout).unwrap();
    println!("{stdout}");
    assert!(stdout.contains(&format!("server: {server} ")));
    assert!(stdout.contains(&format!("name: {name}\n")));
    assert!(stdout.contains(&format!("server: {UNRESOLVED} [unresolved]\n")));
}

/// Monitor must report an address that cannot be resolved and keep monitoring other servers.
#[test]
fn monitor_text_unresolved() {
    let server = FakeServer::new(49).run().to_string();

    let mut child = Command::new(QUERY_PATH)
        .args(["monitor", UNRESOLVED, &server])
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();

    // text mode prints nothing until a server changes, so never wait for a line forever
    let stdout = BufReader::new(child.stdout.take().unwrap());
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        for line in stdout.lines() {
            if tx.send(line.unwrap()).is_err() {
                break;
            }
        }
    });
    let lines: Vec<String> = (0..2)
        .map_while(|_| rx.recv_timeout(LINE_TIMEOUT).ok())
        .collect();

    child.kill().unwrap();
    child.wait().unwrap();

    assert_eq!(lines.len(), 2, "expected two lines, got {lines:?}");
    assert_eq!(lines[0], format!("{UNRESOLVED:24} !!! unresolved"));
    assert!(lines[1].starts_with(&format!("{server:24} +++ ")));
}
