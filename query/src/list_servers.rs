use std::{collections::HashSet, net::SocketAddr, time::Instant};

use serde::Serialize;
use xash3d_observer::{event::Event, Buffer};

use crate::{
    cli::Cli,
    utils::{self, print_json},
    QueryError,
};

#[derive(Clone, Debug, Serialize)]
struct ListResult<'a> {
    master_timeout: u64,
    masters: &'a [Box<str>],
    filter: &'a str,
    servers: &'a [SocketAddr],
}

fn print_server_list(cli: &Cli, servers: HashSet<SocketAddr>) {
    let mut servers: Vec<_> = servers.into_iter().collect();
    servers.sort();

    if cli.json || cli.debug {
        let result = ListResult {
            master_timeout: cli.master_timeout.as_secs(),
            masters: &cli.masters,
            filter: &cli.filter,
            servers: &servers,
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
    let mut observer = utils::create_observer_with_masters(cli)?;
    let mut servers = HashSet::with_capacity(256);

    let mut buffer = Buffer::new();
    let mut remaining = Some(cli.master_timeout);
    let start_time = Instant::now();
    while remaining.is_some() {
        match observer.wait_event(&mut buffer, remaining)? {
            Event::Timeout => break,
            Event::ServerList(list) => {
                for addr in list.iter() {
                    servers.insert(addr);
                }
            }
            _ => {}
        }
        remaining = cli.master_timeout.checked_sub(start_time.elapsed());
    }

    print_server_list(cli, servers);

    Ok(())
}
