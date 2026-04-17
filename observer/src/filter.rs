use std::fmt;

use xash3d_protocol as proto;

pub use proto::filter::Version;

// TODO: use Filter from xash3d-protocol?
pub struct Filter {
    client_version: Option<Version>,
    client_build_number: Option<u32>,
    gamedir: Option<String>,
    nat: Option<bool>,
    raw: Option<String>,
}

impl Filter {
    /// Creates a new `Filter` with the default client version.
    ///
    /// See [Self::set_client_version] for more information.
    pub fn with_default_client_version() -> Self {
        Self {
            client_version: Some(proto::CLIENT_VERSION),
            ..Self::new()
        }
    }

    /// Creates an empty `Filter`.
    pub fn new() -> Self {
        Self {
            client_version: None,
            client_build_number: None,
            gamedir: None,
            nat: None,
            raw: None,
        }
    }

    // Sets a client version.
    //
    // # Note
    //
    // A master server may respond with a fake server if the client version is lower than
    // what is specified in the master server's configuration file.
    pub fn set_client_version(&mut self, version: Version) {
        self.client_version = Some(version);
    }

    // Sets a client build number.
    //
    // # Note
    //
    // A master server may respond with a fake server if the client build number is lower than
    // what is specified in the master server's configuration file.
    pub fn set_client_build_number(&mut self, build_number: u32) {
        self.client_build_number = Some(build_number);
    }

    pub fn set_gamedir(&mut self, value: &str) {
        self.gamedir = Some(value.to_string());
    }

    pub fn set_nat(&mut self, value: bool) {
        self.nat = Some(value);
    }

    pub fn set_raw(&mut self, value: &str) {
        self.raw = Some(value.to_string());
    }

    pub(crate) fn to_raw_string(&self) -> String {
        fn append<T: fmt::Display>(out: &mut String, key: &str, value: Option<T>) {
            use fmt::Write;
            if let Some(value) = value {
                write!(out, "\\{key}\\{value}").unwrap();
            }
        }

        let mut raw = String::new();
        append(&mut raw, "clver", self.client_version);
        append(&mut raw, "buildnum", self.client_build_number);
        append(&mut raw, "nat", self.nat.map(|i| i as u8));
        append(&mut raw, "gamedir", self.gamedir.as_deref());
        if let Some(s) = self.raw.as_deref() {
            raw.push_str(s);
        }

        raw
    }
}

impl Default for Filter {
    fn default() -> Self {
        Self::with_default_client_version()
    }
}
