use std::process;

use crate::{
    cli::{self, Cli},
    config::{self, Config},
    logger::{self, Logger},
    master_server::{Error, Master},
    signal_flags::SignalFlags,
};

fn load_config(cli: &Cli, logger: &Logger) -> Result<Config, config::Error> {
    let mut cfg = match cli.config_path {
        Some(ref p) => config::load(p.as_ref())?,
        None => Config::default(),
    };

    if let Some(level) = cli.log_level {
        cfg.log.level = level;
    }
    if let Some(ip) = cli.listen_ip {
        cfg.master.server.ip = ip;
    }
    if let Some(port) = cli.listen_port {
        cfg.master.server.port = port;
    }
    if let Some(format) = &cli.stats_format {
        cfg.stat.format = format.clone();
    }
    if let Some(interval) = cli.stats_interval {
        cfg.stat.interval = interval;
    }

    logger.update_config(&cfg.log);

    Ok(cfg)
}

pub fn run() -> Result<(), Error> {
    let cli = cli::parse().unwrap_or_else(|e| {
        eprintln!("{e}");
        process::exit(1);
    });

    let logger = logger::init();

    let cfg = load_config(&cli, logger).unwrap_or_else(|e| {
        match cli.config_path.as_deref() {
            Some(p) => eprintln!("Failed to load config \"{p}\": {e}"),
            None => eprintln!("{e}"),
        }
        process::exit(1);
    });

    let mut master = Master::new(cfg)?;
    let sig_flags = SignalFlags::init()?;
    while !sig_flags.is_exit() {
        master.run()?;

        if sig_flags.remove_reload() {
            if let Some(config_path) = cli.config_path.as_deref() {
                info!("Reloading config from {}", config_path);

                match load_config(&cli, logger) {
                    Ok(cfg) => {
                        if let Err(e) = master.update_config(cfg) {
                            error!("{}", e);
                        }
                    }
                    Err(e) => error!("failed to load config: {}", e),
                }
            }
        }
    }

    info!("Server stopped");
    Ok(())
}
