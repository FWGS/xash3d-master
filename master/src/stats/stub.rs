use crate::config::StatConfig;

#[allow(dead_code)]
#[derive(Default)]
struct Counters;

pub struct Stats;

impl Stats {
    pub fn new(_: StatConfig) -> Self {
        Self
    }
    pub fn update_config(&mut self, _: StatConfig) {}
    pub fn clear(&self) {}
    pub fn servers_count(&self, _: usize) {}
    pub fn on_server_add(&self) {}
    pub fn on_server_del(&self) {}
    pub fn on_query_servers(&self) {}
    pub fn on_error(&self) {}
}
