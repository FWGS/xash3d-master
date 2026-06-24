use std::{
    io,
    net::{SocketAddr, UdpSocket},
    thread,
};

use xash3d_protocol::{
    game,
    server::{self, Os, ServerType},
    wrappers::Str,
};

pub struct FakeServer {
    sock: UdpSocket,
    protocol: u8,
    /// GoldSrc server.
    gs: bool,
    /// Enable additional response to `GetServerInfo2` request with `GetServerInfo2ResponseOld`.
    dproto: bool,
    /// Enable response to `GetServerInfo` request.
    info: bool,
    gamedir: String,
    game: String,
    map: String,
    name: String,
}

impl FakeServer {
    fn new_impl(protocol: u8, gs: bool, dproto: bool, info: bool) -> Self {
        let addr = SocketAddr::from(([127, 0, 0, 1], 0));
        let sock = UdpSocket::bind(addr).unwrap();
        let mut name;
        if gs {
            name = format!("GoldSrc {protocol}");
        } else {
            name = format!("Xash3D {protocol}");
        }
        if dproto {
            name.push_str(" (dproto)");
        }
        if gs && info {
            name.push_str(" (info)");
        }
        Self {
            sock,
            protocol,
            gs,
            dproto,
            info,
            gamedir: String::from("valve"),
            game: String::from("Half-Life"),
            map: String::from("crossfire"),
            name,
        }
    }

    pub fn new(protocol: u8) -> Self {
        Self::new_impl(protocol, false, false, true)
    }

    pub fn new_gs(dproto: bool, info: bool) -> Self {
        Self::new_impl(48, true, dproto, info)
    }

    pub fn protocol(&self) -> u8 {
        self.protocol
    }

    pub fn gamedir(&self) -> &str {
        &self.gamedir
    }

    pub fn game(&self) -> &str {
        &self.game
    }

    pub fn map(&self) -> &str {
        &self.map
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn players(&self) -> u8 {
        0
    }

    pub fn max_players(&self) -> u8 {
        32
    }

    pub fn dm(&self) -> bool {
        false
    }

    pub fn team(&self) -> bool {
        false
    }

    pub fn coop(&self) -> bool {
        false
    }

    pub fn password(&self) -> bool {
        false
    }

    pub fn os(&self) -> Os {
        Os::Linux
    }

    pub fn server_type(&self) -> ServerType {
        ServerType::Dedicated
    }

    pub fn dedicated(&self) -> bool {
        self.server_type() == ServerType::Dedicated
    }

    pub fn handle_get_server_info(
        &self,
        req: &game::GetServerInfo,
        from: &SocketAddr,
    ) -> io::Result<()> {
        if req.protocol == self.protocol {
            let resp = server::GetServerInfoResponse {
                gamedir: Str(self.gamedir().as_bytes()),
                map: Str(self.map().as_bytes()),
                host: Str(self.name().as_bytes()),
                protocol: self.protocol,
                numcl: self.players(),
                maxcl: self.max_players(),
                dm: self.dm(),
                team: self.team(),
                coop: self.coop(),
                password: self.password(),
                dedicated: self.dedicated(),
            };
            let mut buf = [0; 512];
            let buf = resp.encode(&mut buf).unwrap();
            self.sock.send_to(buf, from)?;
        } else {
            let mut buf = [0; 512];
            let buf = server::GetServerInfoResponse::encode_wrong_version(
                self.name().as_bytes(),
                &mut buf,
            )
            .unwrap();
            self.sock.send_to(buf, from)?;
        }
        Ok(())
    }

    fn handle_get_server_info2(
        &self,
        _req: &game::GetServerInfo2,
        from: &SocketAddr,
    ) -> io::Result<()> {
        let mut buf = [0; 512];
        let resp = server::GetServerInfo2Response {
            protocol: self.protocol(),
            host: Str(self.name().as_bytes()),
            map: Str(self.map().as_bytes()),
            gamedir: Str(self.gamedir().as_bytes()),
            game: Str(self.game().as_bytes()),
            players: self.players(),
            max_players: self.max_players(),
            version: Str(b"1.2.3.4"),
            ty: self.server_type(),
            ..server::GetServerInfo2Response::default()
        };
        let msg = resp.encode(&mut buf).unwrap();
        self.sock.send_to(msg, from)?;

        if !self.dproto {
            return Ok(());
        }

        let addr = format!("{}", self.sock.local_addr()?);
        let resp = server::GetServerInfo2ResponseOld {
            address: Str(addr.as_bytes()),
            host: Str(self.name().as_bytes()),
            map: Str(self.map().as_bytes()),
            gamedir: Str(self.gamedir().as_bytes()),
            game: Str(self.game().as_bytes()),
            players: self.players(),
            max_players: self.max_players(),
            protocol: self.protocol() - 1,
            password: self.password(),
            ty: self.server_type(),
            ..server::GetServerInfo2ResponseOld::default()
        };
        let msg = resp.encode(&mut buf).unwrap();
        self.sock.send_to(msg, from)?;

        Ok(())
    }

    fn handle(&self, buf: &[u8], from: &SocketAddr) -> io::Result<()> {
        // TODO: GoldSrc engine has correct parser for `GetServerInfo` request.
        if self.gs && !self.info && buf.starts_with(game::Ping::HEADER) {
            let mut buf = [0; 128];
            let buf = server::PingResponse::encode(&mut buf).unwrap();
            self.sock.send_to(buf, from)?;
            return Ok(());
        }

        let Ok(Some(packet)) = game::Packet::decode(buf) else {
            panic!("failed to decode a packet");
        };

        match packet {
            game::Packet::GetServerInfo(ref req) if self.info => {
                self.handle_get_server_info(req, from)?;
            }
            game::Packet::GetServerInfo2(ref req) => {
                self.handle_get_server_info2(req, from)?;
            }
            _ => {}
        }

        Ok(())
    }

    pub fn run(self) -> SocketAddr {
        let addr = self.sock.local_addr().unwrap();
        thread::Builder::new()
            .name(format!("server {addr} {}", self.name()))
            .spawn(move || {
                let mut buf = [0; 1024];
                loop {
                    match self.sock.recv_from(&mut buf) {
                        Ok((n, ref from)) => {
                            if let Err(e) = self.handle(&buf[..n], from) {
                                panic!("error: {e}");
                            }
                        }
                        Err(e) => panic!("error: {e}"),
                    }
                }
            })
            .unwrap();
        addr
    }
}
