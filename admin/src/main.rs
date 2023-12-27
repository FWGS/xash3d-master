// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

mod cli;

use std::io::{self, Write};
use std::net::UdpSocket;

use blake2b_simd::Params;
use termion::input::TermRead;
use thiserror::Error;
use xash3d_protocol::{admin, master};

#[derive(Error, Debug)]
enum Error {
    #[error("Unexpected response from master server")]
    UnexpectedPacket,
    #[error(transparent)]
    Protocol(#[from] xash3d_protocol::Error),
    #[error(transparent)]
    Io(#[from] io::Error),
}

fn send_command(cli: &cli::Cli) -> Result<(), Error> {
    let sock = UdpSocket::bind("0.0.0.0:0")?;
    sock.connect(&cli.address)?;

    let mut buf = [0; 512];
    let n = admin::AdminChallenge.encode(&mut buf)?;
    sock.send(&buf[..n])?;

    let n = sock.recv(&mut buf)?;
    let (master_challenge, hash_challenge) = match master::Packet::decode(&buf[..n])? {
        Some(master::Packet::AdminChallengeResponse(p)) => (p.master_challenge, p.hash_challenge),
        _ => return Err(Error::UnexpectedPacket),
    };

    let stdout = io::stdout();
    let stdin = io::stdin();
    let mut stdout = stdout.lock();
    let mut stdin = stdin.lock();

    stdout.write_all(b"Password:\n")?;
    stdout.flush()?;

    let password = match stdin.read_passwd(&mut stdout)? {
        Some(pass) => pass,
        None => return Ok(()),
    };

    let hash = Params::new()
        .hash_length(cli.hash_len)
        .key(cli.hash_key.as_bytes())
        .personal(cli.hash_personal.as_bytes())
        .to_state()
        .update(password.as_bytes())
        .update(&hash_challenge.to_le_bytes())
        .finalize();

    let n = admin::AdminCommand::new(master_challenge, hash.as_bytes(), &cli.command)
        .encode(&mut buf)?;
    sock.send(&buf[..n])?;

    Ok(())
}

fn main() {
    let cli = cli::parse();

    if let Err(e) = send_command(&cli) {
        eprintln!("error: {}", e);
        std::process::exit(1);
    }
}
