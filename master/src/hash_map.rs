use std::{borrow::Borrow, collections::hash_map::Entry, hash::Hash, ops::Deref};

use ahash::AHashMap;

use crate::{periodic::Periodic, time::RelativeTime};

/// HashMap entry to keep tracking creation time.
#[derive(Copy, Clone, Debug)]
pub struct Timed<T> {
    time: RelativeTime,
    pub value: T,
}

impl<T> Timed<T> {
    pub fn new(value: T) -> Self {
        Self {
            time: RelativeTime::now(),
            value,
        }
    }

    fn is_valid(&self, now: RelativeTime, secs: u32) -> bool {
        now.duration_since(self.time).as_secs() < secs as u64
    }
}

impl<T> Deref for Timed<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> From<T> for Timed<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

pub struct TimedHashMap<K, V> {
    timeout: u32,
    map: Periodic<AHashMap<K, Timed<V>>>,
}

impl<K: Eq + Hash, V> Default for TimedHashMap<K, V> {
    fn default() -> Self {
        Self::new(10)
    }
}

impl<K: Eq + Hash, V> TimedHashMap<K, V> {
    pub fn new(timeout: u32) -> Self {
        Self {
            timeout,
            map: Default::default(),
        }
    }

    pub fn set_timeout(&mut self, timeout: u32) {
        self.timeout = timeout;
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn clear(&mut self) {
        self.map.clear();
    }

    fn cleanup(&mut self) {
        self.map.maybe_run(|map| {
            let now = RelativeTime::now();
            map.retain(|_, v| v.is_valid(now, self.timeout));
        });
    }

    pub fn insert(&mut self, k: K, v: V) {
        self.map.insert(k, Timed::new(v));

        // try to remove outdated entries
        self.cleanup();
    }

    pub fn remove<Q>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.remove(k).and_then(|i| {
            if i.is_valid(RelativeTime::now(), self.timeout) {
                Some(i.value)
            } else {
                None
            }
        })
    }

    pub fn entry(&mut self, key: K) -> Entry<'_, K, Timed<V>> {
        self.map.entry(key)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        let now = RelativeTime::now();
        self.map.iter().filter_map(move |(k, i)| {
            if i.is_valid(now, self.timeout) {
                Some((k, &i.value))
            } else {
                None
            }
        })
    }

    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|(k, _)| k)
    }

    pub fn get<Q>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.get(k).and_then(|i| {
            if i.is_valid(RelativeTime::now(), self.timeout) {
                Some(&i.value)
            } else {
                None
            }
        })
    }
}
