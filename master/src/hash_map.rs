use std::{
    borrow::Borrow,
    collections::hash_map::Entry,
    hash::Hash,
    ops::{Deref, DerefMut},
};

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

impl<T: Default> Default for Timed<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T> Deref for Timed<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> DerefMut for Timed<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<T> From<T> for Timed<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

pub struct TimedHashMap<K, V> {
    timeout: u32,
    periodic: Periodic,
    map: AHashMap<K, Timed<V>>,
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
            periodic: Default::default(),
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
        self.periodic.maybe_run(|| {
            let now = RelativeTime::now();
            self.map.retain(|_, v| v.is_valid(now, self.timeout));
        });
    }

    pub fn insert(&mut self, k: K, v: V) {
        self.map.insert(k, Timed::new(v));

        // try to remove outdated entries
        self.cleanup();
    }

    pub fn remove<Q>(&mut self, k: &Q) -> Option<Timed<V>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.remove(k).and_then(|i| {
            if i.is_valid(RelativeTime::now(), self.timeout) {
                Some(i)
            } else {
                None
            }
        })
    }

    pub fn entry(&mut self, key: K) -> Entry<'_, K, Timed<V>> {
        // not optimal but HashMap::entry API does not allow to replace
        // an occupied entry with vacant
        if let Some(v) = self.map.get(&key) {
            // try to remove the requested outdated entry
            if !v.is_valid(RelativeTime::now(), self.timeout) {
                self.map.remove(&key);
            }
        } else {
            // or try to remove other outdated entries
            self.cleanup();
        }
        self.map.entry(key)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &Timed<V>)> {
        let now = RelativeTime::now();
        self.map.iter().filter_map(move |(k, i)| {
            if i.is_valid(now, self.timeout) {
                Some((k, i))
            } else {
                None
            }
        })
    }

    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|(k, _)| k)
    }

    pub fn get<Q>(&self, k: &Q) -> Option<&Timed<V>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.get(k).and_then(|i| {
            if i.is_valid(RelativeTime::now(), self.timeout) {
                Some(i)
            } else {
                None
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use std::{thread, time::Duration};

    use super::*;

    #[test]
    fn cleanup() {
        let n = Periodic::DEFAULT_LIMIT as usize;
        let mut map = TimedHashMap::new(1);
        for i in (0..3).map(|i| i * n) {
            for j in 0..n {
                map.insert(i + j, ());
            }
            assert_eq!(map.len(), n);
            thread::sleep(Duration::from_secs(1));
        }
    }
}
