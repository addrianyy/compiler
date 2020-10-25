use std::hash::{Hasher, BuildHasherDefault};
use std::collections::{HashMap, HashSet};

pub struct FnvHasher(u64);

impl Default for FnvHasher {
    #[inline]
    fn default() -> FnvHasher {
        FnvHasher(0xcbf29ce484222325)
    }
}

impl Hasher for FnvHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes.iter() {
            self.0 ^= *byte as u64;
            self.0  = self.0.wrapping_mul(0x100000001b3);
        }
    }
}

type FnvBuildHasher = BuildHasherDefault<FnvHasher>;

pub type Map<K, V>         = HashMap<K, V, FnvBuildHasher>;
pub type Set<T>            = HashSet<T, FnvBuildHasher>;
pub type LargeKeyMap<K, V> = HashMap<K, V>;

pub trait CapacityExt {
    fn new_with_capacity(capacity: usize) -> Self;
}

impl<K, V> CapacityExt for Map<K, V> {
    fn new_with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, Default::default())
    }
}

impl<K> CapacityExt for Set<K> {
    fn new_with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, Default::default())
    }
}

impl<K, V> CapacityExt for LargeKeyMap<K, V> {
    fn new_with_capacity(capacity: usize) -> Self {
        Self::with_capacity(capacity)
    }
}
