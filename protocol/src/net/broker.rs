//! Steam API broker packets.
//!
//! For more information read [specification][1].
//!
//! [1]: https://github.com/FWGS/xash3d-fwgs/blob/master/Documentation/extensions/steam-broker.md

// TODO: document broker api
#![allow(missing_docs)]

use std::{
    fmt,
    net::SocketAddr,
    str::{self, FromStr},
};

use crate::{
    cursor::{Cursor, CursorMut},
    wrappers::StrSlice,
    CursorError, Error,
};

/// A simple wrapper for handling command arguments.
#[derive(Copy, Clone)]
struct Args<'a> {
    cur: Cursor<'a>,
}

impl<'a> Args<'a> {
    fn new(raw: &'a [u8]) -> Self {
        Self {
            cur: Cursor::new(raw),
        }
    }

    fn is_empty(&self) -> bool {
        !self.cur.has_remaining()
    }

    fn try_next(&mut self) -> Option<&'a [u8]> {
        self.cur.take_while(|c| c == b' ').ok();

        if !self.cur.has_remaining() {
            return None;
        }

        match self.cur.take_while(|c| c != b' ') {
            Ok(i) => Some(i),
            Err(_) => Some(self.cur.get_tail()),
        }
    }

    fn next(&mut self) -> Result<&'a [u8], CursorError> {
        self.try_next().ok_or(CursorError::Expect)
    }

    fn parse_next<T: FromStr>(&mut self) -> Result<T, CursorError> {
        self.next()
            .and_then(|s| str::from_utf8(s).map_err(|_| CursorError::InvalidString))
            // TODO: add CursorError::ParseError
            .and_then(|s| s.parse().map_err(|_| CursorError::InvalidString))
    }

    fn expect_empty(&self) -> Result<(), CursorError> {
        if !self.cur.has_remaining() {
            Ok(())
        } else {
            Err(CursorError::ExpectEmpty)
        }
    }
}

pub struct Frame<'a> {
    data: &'a [u8],
}

impl<'a> Frame<'a> {
    const HEADER: &'static [u8] = b"SBRK";
    const FIXED_SIZE: usize = Self::HEADER.len() + 2;

    /// Returns a shared byte slice to frame data.
    pub fn as_bytes(&self) -> &'a [u8] {
        self.data
    }

    /// Returns a shared byte slice to payload data.
    pub fn payload(&self) -> &'a [u8] {
        &self.data[Self::FIXED_SIZE..]
    }

    fn expect_command(&self, expect: impl AsRef<[u8]>) -> Result<Args<'a>, CursorError> {
        let mut args = Args::new(self.payload());
        let name = args.next()?;
        if name == expect.as_ref() {
            Ok(args)
        } else {
            Err(CursorError::Expect)
        }
    }

    fn expect_command_no_args(&self, expect: impl AsRef<[u8]>) -> Result<(), CursorError> {
        self.expect_command(expect.as_ref()).and_then(|args| {
            if args.is_empty() {
                Ok(())
            } else {
                Err(CursorError::ExpectEmpty)
            }
        })
    }

    /// Decode a new frame from a buffer.
    pub fn decode(src: &'a [u8]) -> Result<Self, CursorError> {
        if src.len() < Self::FIXED_SIZE {
            let need = Self::FIXED_SIZE - src.len();
            return Err(CursorError::NeedMoreBytes(need));
        }
        let mut cur = Cursor::new(src);
        cur.expect(Self::HEADER)?;
        let payload_len = usize::from(cur.get_u16_le()?);
        cur.get_bytes(payload_len)?;
        let len = cur.pos();
        Ok(Self { data: &src[..len] })
    }

    fn encode<F>(buf: &'a mut [u8], payload: F) -> Result<Self, CursorError>
    where
        F: FnOnce(CursorMut) -> Result<CursorMut, CursorError>,
    {
        let (mut head, tail) = CursorMut::new(buf).split(Self::FIXED_SIZE)?;
        let tail = payload(tail)?;
        let len = u16::try_from(tail.current_pos()).map_err(|_| CursorError::InvalidNumber)?;

        head.put_bytes(Self::HEADER)?;
        head.put_u16_le(len)?;
        head.expect_full().expect("header must be full");

        let pos = tail.pos();
        Ok(Self { data: &buf[..pos] })
    }

    fn encode_fmt<F: fmt::Display>(buf: &'a mut [u8], payload: F) -> Result<Self, CursorError> {
        Self::encode(buf, |mut cur| {
            cur.put_as_str(payload)?;
            Ok(cur)
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Gamedir<'a> {
    gamedir: StrSlice<'a>,
}

impl<'a> Gamedir<'a> {
    const HEADER: &'static str = "sb_gamedir";

    pub fn new(gamedir: &'a [u8]) -> Self {
        Self {
            gamedir: StrSlice::from(gamedir),
        }
    }

    pub fn gamedir(&self) -> StrSlice<'a> {
        self.gamedir
    }

    pub fn decode(frame: Frame<'a>) -> Result<Self, Error> {
        let mut args = frame.expect_command(Self::HEADER)?;
        let gamedir = args.next()?;
        args.expect_empty()?;
        Ok(Self::new(gamedir))
    }

    pub fn encode<'b>(&self, buf: &'b mut [u8]) -> Result<Frame<'b>, CursorError> {
        Frame::encode_fmt(buf, format_args!("{} {}", Self::HEADER, self.gamedir))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Connect {
    server_address: SocketAddr,
    server_steam_id: u64,
    challenge: u32,
    secure: bool,
}

impl Connect {
    const HEADER: &'static str = "sb_connect";

    pub fn new(
        server_address: SocketAddr,
        server_steam_id: u64,
        secure: bool,
        challenge: u32,
    ) -> Self {
        Self {
            server_address,
            server_steam_id,
            challenge,
            secure,
        }
    }

    pub fn server_address(&self) -> &SocketAddr {
        &self.server_address
    }

    pub fn server_steam_id(&self) -> u64 {
        self.server_steam_id
    }

    pub fn secure(&self) -> bool {
        self.secure
    }

    pub fn challenge(&self) -> u32 {
        self.challenge
    }

    pub fn decode(frame: Frame<'_>) -> Result<Self, Error> {
        let mut args = frame.expect_command(Self::HEADER)?;
        let server_address = args.parse_next()?;
        let server_steam_id = args.parse_next()?;
        let secure = match args.next()? {
            b"0" => false,
            b"1" => true,
            _ => return Err(CursorError::InvalidBool.into()),
        };
        let challenge = args.parse_next()?;
        args.expect_empty()?;
        Ok(Self::new(
            server_address,
            server_steam_id,
            secure,
            challenge,
        ))
    }

    pub fn encode<'a>(&self, buf: &'a mut [u8]) -> Result<Frame<'a>, CursorError> {
        Frame::encode_fmt(
            buf,
            format_args!(
                "{} {} {} {} {}",
                Self::HEADER,
                self.server_address,
                self.server_steam_id,
                self.secure as u8,
                self.challenge
            ),
        )
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ConnectResponse<'a> {
    client_steam_id: u64,
    ticket: &'a [u8],
    challenge: u32,
}

impl<'a> ConnectResponse<'a> {
    const HEADER: &'static str = "sb_connect\n";

    pub fn new(client_steam_id: u64, challenge: u32, ticket: &'a [u8]) -> Self {
        Self {
            client_steam_id,
            challenge,
            ticket,
        }
    }

    pub fn client_steam_id(&self) -> u64 {
        self.client_steam_id
    }

    pub fn challenge(&self) -> u32 {
        self.challenge
    }

    pub fn ticket(&self) -> &'a [u8] {
        self.ticket
    }

    pub fn decode(frame: Frame<'a>) -> Result<Self, Error> {
        let mut cur = Cursor::new(frame.payload());
        cur.expect(Self::HEADER.as_bytes())?;
        let challenge = cur.get_u32_le()?;
        let client_steam_id = cur.get_u64_le()?;
        let len = usize::try_from(cur.get_u32_le()?).map_err(|_| CursorError::InvalidNumber)?;
        let ticket = cur.get_bytes(len)?;
        cur.expect_empty()?;
        Ok(Self::new(client_steam_id, challenge, ticket))
    }

    pub fn encode<'b>(&self, buf: &'b mut [u8]) -> Result<Frame<'b>, CursorError> {
        Frame::encode(buf, |mut cur| {
            cur.put_bytes(Self::HEADER.as_bytes())?;
            cur.put_u32_le(self.challenge)?;
            cur.put_u64_le(self.client_steam_id)?;
            let len = u32::try_from(self.ticket.len()).map_err(|_| CursorError::InvalidNumber)?;
            cur.put_u32_le(len)?;
            cur.put_bytes(self.ticket)?;
            Ok(cur)
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Disconnect {
    server_address: SocketAddr,
    challenge: u32,
}

impl Disconnect {
    const HEADER: &'static str = "sb_disconnect";

    pub fn new(server_address: SocketAddr, challenge: u32) -> Self {
        Self {
            server_address,
            challenge,
        }
    }

    pub fn server_address(&self) -> &SocketAddr {
        &self.server_address
    }

    pub fn challenge(&self) -> u32 {
        self.challenge
    }

    pub fn decode(frame: Frame) -> Result<Self, Error> {
        let mut args = frame.expect_command(Self::HEADER)?;
        let server_address = args.parse_next()?;
        let challenge = args.parse_next()?;
        args.expect_empty()?;
        Ok(Self::new(server_address, challenge))
    }

    pub fn encode<'a>(&self, buf: &'a mut [u8]) -> Result<Frame<'a>, CursorError> {
        Frame::encode_fmt(
            buf,
            format_args!(
                "{} {} {}",
                Self::HEADER,
                self.server_address,
                self.challenge
            ),
        )
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Terminate(());

impl Terminate {
    const HEADER: &'static str = "sb_terminate";

    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self(())
    }

    pub fn decode(frame: Frame<'_>) -> Result<Self, Error> {
        frame.expect_command_no_args(Self::HEADER)?;
        Ok(Self::new())
    }

    pub fn encode<'a>(&self, buf: &'a mut [u8]) -> Result<Frame<'a>, CursorError> {
        Frame::encode_fmt(buf, Self::HEADER)
    }
}

#[derive(Clone, Debug, PartialEq)]
#[non_exhaustive]
pub enum ClientPacket<'a> {
    Gamedir(Gamedir<'a>),
    Connect(Connect),
    Disconnect(Disconnect),
    Terminate(Terminate),
}

impl<'a> ClientPacket<'a> {
    pub fn decode(frame: Frame<'a>) -> Result<Self, Error> {
        match frame.payload() {
            s if s.starts_with(Gamedir::HEADER.as_bytes()) => {
                Gamedir::decode(frame).map(Self::Gamedir)
            }
            s if s.starts_with(Connect::HEADER.as_bytes()) => {
                Connect::decode(frame).map(Self::Connect)
            }
            s if s.starts_with(Disconnect::HEADER.as_bytes()) => {
                Disconnect::decode(frame).map(Self::Disconnect)
            }
            s if s.starts_with(Terminate::HEADER.as_bytes()) => {
                Terminate::decode(frame).map(Self::Terminate)
            }
            _ => Err(Error::InvalidPacket),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
#[non_exhaustive]
pub enum ServerPacket<'a> {
    ConnectResponse(ConnectResponse<'a>),
}

impl<'a> ServerPacket<'a> {
    pub fn decode(frame: Frame<'a>) -> Result<Self, Error> {
        match frame.payload() {
            s if s.starts_with(ConnectResponse::HEADER.as_bytes()) => {
                ConnectResponse::decode(frame).map(Self::ConnectResponse)
            }
            _ => Err(Error::InvalidPacket),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::net::{IpAddr, Ipv4Addr, SocketAddr};

    const TEST_ADDRESS: SocketAddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::LOCALHOST), 27010);

    #[test]
    fn frame() {
        let mut buf = [0; 128];
        let frame = Frame::encode_fmt(&mut buf, "test 123 abc").unwrap();
        let frame = Frame::decode(frame.as_bytes()).unwrap();
        assert_eq!(frame.as_bytes().len(), 18);
        assert_eq!(frame.payload(), b"test 123 abc");
    }

    #[test]
    fn gamedir() {
        let mut buf = [0; 128];
        let request = Gamedir::new(b"valve");
        let frame = request.encode(&mut buf).unwrap();
        let decoded = ClientPacket::decode(frame).unwrap();
        assert_eq!(decoded, ClientPacket::Gamedir(request));
    }

    #[test]
    fn connect() {
        let mut buf = [0; 128];
        let request = Connect::new(TEST_ADDRESS, 111222333, true, 123456);
        let frame = request.encode(&mut buf).unwrap();
        let decoded = ClientPacket::decode(frame).unwrap();
        assert_eq!(decoded, ClientPacket::Connect(request));
    }

    #[test]
    fn connect_response() {
        let mut buf = [0; 128];
        let request = ConnectResponse::new(12345, 0xdeadbeef, b"foobar_ticket_123");
        let frame = request.encode(&mut buf).unwrap();
        let decoded = ServerPacket::decode(frame).unwrap();
        assert_eq!(decoded, ServerPacket::ConnectResponse(request));
    }

    #[test]
    fn disconnect() {
        let mut buf = [0; 128];
        let request = Disconnect::new(TEST_ADDRESS, 123456);
        let frame = request.encode(&mut buf).unwrap();
        let decoded = ClientPacket::decode(frame).unwrap();
        assert_eq!(decoded, ClientPacket::Disconnect(request));
    }

    #[test]
    fn terminate() {
        let mut buf = [0; 128];
        let request = Terminate::new();
        let frame = request.encode(&mut buf).unwrap();
        let decoded = ClientPacket::decode(frame).unwrap();
        assert_eq!(decoded, ClientPacket::Terminate(request));
    }
}
