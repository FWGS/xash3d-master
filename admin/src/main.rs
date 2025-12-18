// SPDX-License-Identifier: GPL-3.0-only
// SPDX-FileCopyrightText: 2023 Denis Drakhnia <numas13@gmail.com>

mod cli;

use std::env;
use std::io::{self, Write};
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

fn read_password() -> Result<Option<String>, Error> {
    use crossterm::event::{read, Event, KeyCode, KeyEventKind, KeyModifiers};
    use crossterm::terminal::{disable_raw_mode, enable_raw_mode};

    if let Ok(password) = env::var("XASH3D_ADMIN_PASSWORD") {
        return Ok(Some(password));
    }

    print!("Password: ");
    io::stdout().flush().unwrap();

    enable_raw_mode()?;

    let mut buf = String::with_capacity(32);
    loop {
        let event = match read() {
            Ok(event) => event,
            Err(err) => {
                disable_raw_mode()?;
                return Err(err.into());
            }
        };

        match event {
            Event::Key(key) => {
                if key.kind != KeyEventKind::Press {
                    continue;
                }

                let is_ctrl = key.modifiers.contains(KeyModifiers::CONTROL);
                match key.code {
                    KeyCode::Esc => break,
                    KeyCode::Enter => break,
                    KeyCode::Char('c' | 'd') if is_ctrl => break,
                    KeyCode::Char('w') if is_ctrl => buf.clear(),
                    KeyCode::Char(c) => buf.push(c),
                    KeyCode::Backspace => {
                        buf.pop();
                    }
                    _ => {}
                }
            }
            Event::Paste(s) => buf.push_str(&s),
            _ => {}
        }
    }

    disable_raw_mode()?;

    println!();

    Ok(match buf.len() {
        0 => None,
        _ => Some(buf),
    })
}

fn send_command(cli: &cli::Cli) -> Result<(), Error> {
    let sock = UdpSocket::bind("0.0.0.0:0")?;
    sock.connect(&cli.address)?;

    let mut buf = [0; 512];
    let packet = admin::AdminChallenge.encode(&mut buf)?;
    sock.send(packet)?;

    let n = sock.recv(&mut buf)?;
    let (master_challenge, hash_challenge) = match master::Packet::decode(&buf[..n])? {
        Some(master::Packet::AdminChallengeResponse(p)) => (p.master_challenge, p.hash_challenge),
        _ => return Err(Error::UnexpectedPacket),
    };

    let password = match read_password()? {
        Some(s) => s,
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

    let packet = admin::AdminCommand::new(master_challenge, hash.as_bytes(), &cli.command)
        .encode(&mut buf)?;
    sock.send(packet)?;

    Ok(())
}

fn main() {
    let cli = cli::parse();

    if let Err(e) = send_command(&cli) {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}
