//! Stateless challenges for source-address verification.
//!
//! Copies the pattern from engine's `SV_GetChallenge`: the challenge is derived
//! from src address, a salt generated at master startup, and a time window.
//! Validation accepts the current and previous window so
//! requests near the boundary still succeed.

use std::{
    net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6},
    sync::OnceLock,
    time::Instant,
};

use blake2b_simd::{Params, State};
use fastrand::Rng;

/// A target for challenge.
pub trait Target {
    fn update_state(&self, state: &mut State);
}

impl Target for Ipv4Addr {
    fn update_state(&self, state: &mut State) {
        state.update(&self.octets());
    }
}

impl Target for Ipv6Addr {
    fn update_state(&self, state: &mut State) {
        state.update(&self.octets());
    }
}

impl Target for IpAddr {
    fn update_state(&self, state: &mut State) {
        match self {
            IpAddr::V4(v4) => v4.update_state(state),
            IpAddr::V6(v6) => v6.update_state(state),
        }
    }
}

impl Target for SocketAddrV4 {
    fn update_state(&self, state: &mut State) {
        self.ip().update_state(state);
        state.update(&self.port().to_ne_bytes());
    }
}

impl Target for SocketAddrV6 {
    fn update_state(&self, state: &mut State) {
        self.ip().update_state(state);
        state.update(&self.port().to_ne_bytes());
    }
}

impl Target for SocketAddr {
    fn update_state(&self, state: &mut State) {
        match self {
            SocketAddr::V4(v4) => v4.update_state(state),
            SocketAddr::V6(v6) => v6.update_state(state),
        }
    }
}

/// Create a challenge from hash.
pub trait Challenge: PartialEq {
    const HASH_SIZE: usize;

    fn from_hash(hash: &[u8]) -> Self;
}

impl Challenge for u32 {
    const HASH_SIZE: usize = 4;

    fn from_hash(hash: &[u8]) -> Self {
        u32::from_le_bytes([hash[0], hash[1], hash[2], hash[3]])
    }
}

impl<A: Challenge, B: Challenge> Challenge for (A, B) {
    const HASH_SIZE: usize = A::HASH_SIZE + B::HASH_SIZE;

    fn from_hash(hash: &[u8]) -> Self {
        let (a, tail) = hash.split_at(A::HASH_SIZE);
        let b = &tail[..B::HASH_SIZE];
        (A::from_hash(a), B::from_hash(b))
    }
}

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

    pub fn compute<T: Target, C: Challenge>(&self, target: &T, time_window: u64) -> C {
        let mut state = Params::new().hash_length(C::HASH_SIZE).to_state();
        target.update_state(&mut state);
        state.update(&self.salt);
        state.update(&time_window.to_ne_bytes());
        let hash = state.finalize();
        C::from_hash(&hash.as_bytes()[..C::HASH_SIZE])
    }

    pub fn compute_u32<T: Target>(&self, target: &T, time_window: u64) -> u32 {
        self.compute::<T, u32>(target, time_window)
    }

    pub fn validate<T: Target, C: Challenge>(
        &self,
        target: &T,
        time_window: u64,
        challenge: C,
    ) -> bool {
        self.compute::<T, C>(target, time_window) == challenge
            || self.compute::<T, C>(target, time_window.wrapping_sub(1)) == challenge
    }

    pub fn validate_u32<T: Target>(&self, target: &T, time_window: u64, challenge: u32) -> bool {
        self.validate(target, time_window, challenge)
    }
}

/// Returns the current time window index
pub fn current_time_window(window_secs: u64) -> u64 {
    static BASE: OnceLock<Instant> = OnceLock::new();
    BASE.get_or_init(Instant::now).elapsed().as_secs() / window_secs
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
        let a = &addr("192.0.2.1:27015");
        assert_eq!(k.compute_u32(a, 1000), k.compute_u32(a, 1000));
    }

    #[test]
    fn ip_sensitive() {
        let k = fixed_key();
        assert_ne!(
            k.compute_u32(&addr("1.2.3.4:27015"), 1000),
            k.compute_u32(&addr("1.2.3.5:27015"), 1000),
        );
    }

    #[test]
    fn port_sensitive() {
        let k = fixed_key();
        assert_ne!(
            k.compute_u32(&addr("1.2.3.4:27015"), 1000),
            k.compute_u32(&addr("1.2.3.4:27016"), 1000),
        );
    }

    #[test]
    fn window_sensitive() {
        let k = fixed_key();
        let a = &addr("1.2.3.4:27015");
        assert_ne!(k.compute_u32(a, 1000), k.compute(a, 1001));
    }

    #[test]
    fn salt_sensitive() {
        let mut rng = Rng::with_seed(42);
        let a = ChallengeKey::random(&mut rng);
        let b = ChallengeKey::random(&mut rng);
        let src = &addr("1.2.3.4:27015");
        assert_ne!(a.compute_u32(src, 1000), b.compute(src, 1000));
    }

    #[test]
    fn validate_current_and_previous_window() {
        let k = fixed_key();
        let a = &addr("10.0.0.1:27015");
        let now = 1000;
        let c_now = k.compute_u32(a, now);
        let c_prev = k.compute_u32(a, now - 1);
        assert!(k.validate_u32(a, now, c_now));
        assert!(k.validate_u32(a, now, c_prev));
        assert!(!k.validate_u32(a, now, c_now.wrapping_add(1)));
    }

    #[test]
    fn validate_rejects_two_windows_old() {
        let k = fixed_key();
        let a = &addr("10.0.0.1:27015");
        let stale = k.compute_u32(a, 998);
        assert!(!k.validate_u32(a, 1000, stale));
    }

    #[test]
    fn validate_rejects_different_port() {
        let k = fixed_key();
        let c = k.compute_u32(&addr("10.0.0.1:27015"), 1000);
        assert!(!k.validate_u32(&addr("10.0.0.1:27016"), 1000, c));
    }

    #[test]
    fn ipv6_works() {
        let k = fixed_key();
        let a = &addr("[2001:db8::1]:27015");
        let c = k.compute_u32(a, 1000);
        assert!(k.validate_u32(a, 1000, c));
    }
}
