use std::{
    collections::{hash_map::Entry, HashMap},
    net::SocketAddr,
    time::Duration,
};

use xash3d_observer::{GetServerInfoResponse, Handler};

use crate::{
    cli::Cli,
    server_info::ServerInfo,
    server_result::{ServerResult, ServerResultKind},
    QueryError,
};

struct Monitor<'a> {
    cli: &'a Cli,
    servers: HashMap<SocketAddr, ServerInfo>,
}

impl<'a> Monitor<'a> {
    fn new(cli: &'a Cli) -> Self {
        Self {
            cli,
            servers: Default::default(),
        }
    }
}

impl Handler for Monitor<'_> {
    fn server_update(
        &mut self,
        addr: SocketAddr,
        info: &GetServerInfoResponse,
        _: bool,
        ping: Duration,
    ) {
        let info = ServerInfo::from(info);
        if self.cli.json {
            let result = ServerResult::ok(addr, ping, info);
            println!("{}", serde_json::to_string_pretty(&result).unwrap());
        } else {
            match self.servers.entry(addr) {
                Entry::Occupied(mut e) => {
                    let p = e.get().printer(self.cli);
                    println!("{:24?} --- {:>7.1} {}", addr, ' ', p,);
                    let p = info.printer(self.cli);
                    println!("{addr:24?} +++ {ping:>7.1?} {p}");
                    e.insert(info);
                }
                Entry::Vacant(e) => {
                    let p = info.printer(self.cli);
                    println!("{addr:24?} +++ {ping:>7.1?} {p}");
                    e.insert(info);
                }
            }
        }
    }

    fn server_timeout(&mut self, addr: SocketAddr) {
        if self.cli.json {
            let result = ServerResult::timeout(addr);
            println!("{}", serde_json::to_string_pretty(&result).unwrap());
        }
    }

    fn server_remove(&mut self, addr: SocketAddr) {
        if self.cli.json {
            let result = ServerResult::new(addr, None, ServerResultKind::Remove);
            println!("{}", serde_json::to_string_pretty(&result).unwrap());
        } else {
            self.servers.remove(&addr);
        }
    }
}

pub(crate) fn run(cli: &Cli) -> Result<(), QueryError> {
    let handler = Monitor::new(cli);
    let mut observer = crate::create_observer(cli, handler)?;
    observer.run()?;
    Ok(())
}
