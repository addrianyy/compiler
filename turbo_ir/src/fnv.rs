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

pub type FnvBuildHasher   = BuildHasherDefault<FnvHasher>;
pub type FnvHashMap<K, V> = HashMap<K, V, FnvBuildHasher>;
pub type FnvHashSet<T>    = HashSet<T, FnvBuildHasher>;
