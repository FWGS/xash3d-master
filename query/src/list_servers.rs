use std::{collections::HashSet, net::SocketAddr, time::Instant};

use serde::Serialize;
use xash3d_observer::Handler;

use crate::{cli::Cli, print_json, QueryError};

#[derive(Clone, Debug, Serialize)]
struct ListResult<'a> {
    master_timeout: u64,
    masters: &'a [Box<str>],
    filter: &'a str,
    servers: &'a [SocketAddr],
}

struct CollectServers {
    end_time: Instant,
    servers: HashSet<SocketAddr>,
}

impl CollectServers {
    fn new(cli: &Cli) -> Self {
        Self {
            end_time: Instant::now() + cli.master_timeout,
            servers: HashSet::with_capacity(256),
        }
    }
}

impl Handler for CollectServers {
    fn stop_observer(&mut self) -> bool {
        self.end_time < Instant::now()
    }

    fn query_info_for_server(&mut self, _: SocketAddr, server: SocketAddr) -> bool {
        self.servers.insert(server);
        false
    }
}

fn print_server_list(cli: &Cli, servers: &[SocketAddr]) {
    if cli.json || cli.debug {
        let result = ListResult {
            master_timeout: cli.master_timeout.as_secs(),
            masters: &cli.masters,
            filter: &cli.filter,
            servers,
        };

        if cli.json {
            print_json(cli, &result);
        } else if cli.debug {
            println!("{result:#?}");
        } else {
            todo!()
        }
    } else {
        for i in servers {
            println!("{i}");
        }
    }
}

pub(crate) fn run(cli: &Cli) -> Result<(), QueryError> {
    let handler = CollectServers::new(cli);
    let mut observer = crate::create_observer(cli, handler)?;
    observer.run()?;
    let handler = observer.into_handler();

    let mut servers: Vec<_> = handler.servers.into_iter().collect();
    servers.sort();
    print_server_list(cli, &servers);

    Ok(())
}
