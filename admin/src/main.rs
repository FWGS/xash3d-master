// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

mod cli;

use std::io;
use std::net::UdpSocket;

use blake2b_simd::Params;
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
    let challenge = match master::Packet::decode(&buf[..n])? {
        master::Packet::AdminChallengeResponse(p) => p.challenge,
        _ => return Err(Error::UnexpectedPacket),
    };

    println!("Password:");
    let mut password = String::new();
    io::stdin().read_line(&mut password)?;
    if password.ends_with('\n') {
        password.pop();
    }

    let hash = Params::new()
        .hash_length(cli.hash_len)
        .key(cli.hash_key.as_bytes())
        .personal(cli.hash_personal.as_bytes())
        .to_state()
        .update(password.as_bytes())
        .update(&challenge.to_le_bytes())
        .finalize();

    let n = admin::AdminCommand::new(hash.as_bytes(), &cli.command).encode(&mut buf)?;
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
