//! Stateless challenges for source-address verification.
//!
//! Copies the pattern from engine's `SV_GetChallenge`: the challenge is derived
//! from src address, a salt generated at master startup, and a time window.
//! Validation accepts the current and previous window so
//! requests near the boundary still succeed.

use std::net::{IpAddr, SocketAddr};
use std::sync::OnceLock;
use std::time::Instant;

use blake2b_simd::Params;
use fastrand::Rng;

/// Per-master secret used to derive challenges.
#[derive(Clone)]
pub struct ChallengeKey {
    salt: [u8; 16],
}

impl ChallengeKey {
    pub fn random(rng: &mut Rng) -> Self {
        let mut salt = [0u8; 16];
        rng.fill(&mut salt);
        Self { salt }
    }

    pub fn compute(&self, addr: SocketAddr, time_window: u64) -> u32 {
        let mut state = Params::new().hash_length(4).to_state();
        match addr.ip() {
            IpAddr::V4(v4) => {
                state.update(&v4.octets());
            }
            IpAddr::V6(v6) => {
                state.update(&v6.octets());
            }
        }
        state.update(&addr.port().to_ne_bytes());
        state.update(&self.salt);
        state.update(&time_window.to_ne_bytes());
        let hash = state.finalize();
        let b = hash.as_bytes();
        u32::from_le_bytes([b[0], b[1], b[2], b[3]])
    }

    pub fn validate(&self, addr: SocketAddr, time_window: u64, challenge: u32) -> bool {
        self.compute(addr, time_window) == challenge
            || self.compute(addr, time_window.wrapping_sub(1)) == challenge
    }
}

/// Returns the current time window index
pub fn current_time_window(window_secs: u64) -> u64 {
    static BASE: OnceLock<Instant> = OnceLock::new();
    let base = BASE.get_or_init(Instant::now);
    Instant::now().duration_since(*base).as_secs() / window_secs
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixed_key() -> ChallengeKey {
        ChallengeKey {
            salt: *b"0123456789abcdef",
        }
    }

    fn addr(s: &str) -> SocketAddr {
        s.parse().unwrap()
    }

    #[test]
    fn deterministic() {
        let k = fixed_key();
        let a = addr("192.0.2.1:27015");
        assert_eq!(k.compute(a, 1000), k.compute(a, 1000));
    }

    #[test]
    fn ip_sensitive() {
        let k = fixed_key();
        assert_ne!(
            k.compute(addr("1.2.3.4:27015"), 1000),
            k.compute(addr("1.2.3.5:27015"), 1000),
        );
    }

    #[test]
    fn port_sensitive() {
        let k = fixed_key();
        assert_ne!(
            k.compute(addr("1.2.3.4:27015"), 1000),
            k.compute(addr("1.2.3.4:27016"), 1000),
        );
    }

    #[test]
    fn window_sensitive() {
        let k = fixed_key();
        let a = addr("1.2.3.4:27015");
        assert_ne!(k.compute(a, 1000), k.compute(a, 1001));
    }

    #[test]
    fn salt_sensitive() {
        let mut rng = Rng::with_seed(42);
        let a = ChallengeKey::random(&mut rng);
        let b = ChallengeKey::random(&mut rng);
        let src = addr("1.2.3.4:27015");
        assert_ne!(a.compute(src, 1000), b.compute(src, 1000));
    }

    #[test]
    fn validate_current_and_previous_window() {
        let k = fixed_key();
        let a = addr("10.0.0.1:27015");
        let now = 1000;
        let c_now = k.compute(a, now);
        let c_prev = k.compute(a, now - 1);
        assert!(k.validate(a, now, c_now));
        assert!(k.validate(a, now, c_prev));
        assert!(!k.validate(a, now, c_now.wrapping_add(1)));
    }

    #[test]
    fn validate_rejects_two_windows_old() {
        let k = fixed_key();
        let a = addr("10.0.0.1:27015");
        let stale = k.compute(a, 998);
        assert!(!k.validate(a, 1000, stale));
    }

    #[test]
    fn validate_rejects_different_port() {
        let k = fixed_key();
        let c = k.compute(addr("10.0.0.1:27015"), 1000);
        assert!(!k.validate(addr("10.0.0.1:27016"), 1000, c));
    }

    #[test]
    fn ipv6_works() {
        let k = fixed_key();
        let a = addr("[2001:db8::1]:27015");
        let c = k.compute(a, 1000);
        assert!(k.validate(a, 1000, c));
    }
}
