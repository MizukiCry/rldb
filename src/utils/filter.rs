use std::rc::Rc;

pub trait FilterPolicy {
    fn name(&self) -> &'static str;

    /// Create a filter from the given keys
    fn create(&self, keys: &[u8], offsets: &[usize]) -> Vec<u8>;

    /// Whether the key may exist in the filter
    /// When returning false, the key definitely does not exist
    fn may_exist(&self, key: &[u8], filter: &[u8]) -> bool;
}

impl FilterPolicy for Rc<dyn FilterPolicy> {
    fn name(&self) -> &'static str {
        (**self).name()
    }

    fn create(&self, keys: &[u8], offsets: &[usize]) -> Vec<u8> {
        (**self).create(keys, offsets)
    }

    fn may_exist(&self, key: &[u8], filter: &[u8]) -> bool {
        (**self).may_exist(key, filter)
    }
}

impl FilterPolicy for Box<dyn FilterPolicy> {
    fn name(&self) -> &'static str {
        (**self).name()
    }

    fn create(&self, keys: &[u8], offsets: &[usize]) -> Vec<u8> {
        (**self).create(keys, offsets)
    }

    fn may_exist(&self, key: &[u8], filter: &[u8]) -> bool {
        (**self).may_exist(key, filter)
    }
}

#[derive(Clone, Copy)]
pub struct NoFilterPolicy;

impl FilterPolicy for NoFilterPolicy {
    fn name(&self) -> &'static str {
        "NoFilterPolicy"
    }

    fn create(&self, _keys: &[u8], _offsets: &[usize]) -> Vec<u8> {
        Vec::new()
    }

    fn may_exist(&self, _key: &[u8], _filter: &[u8]) -> bool {
        true
    }
}

/// A classic Bloom filter implementation
#[derive(Clone, Copy)]
pub struct BloomFilterPolicy {
    bits_per_key: u32,
    k: u32,
}

impl BloomFilterPolicy {
    pub fn new(bits_per_key: u32) -> Self {
        // When k = bits_per_key * ln(2), the miss rate is minimized
        // https://blog.mizuki.fun/posts/ffa9ccf7.html
        let mut k = (bits_per_key as f32 * std::f32::consts::LN_2) as u32;

        if k < 1 {
            k = 1;
        } else if k > 30 {
            k = 30;
        }

        Self { bits_per_key, k }
    }

    pub fn hash(key: &[u8]) -> u32 {
        fasthash::murmur3::hash32(key)
    }
}

/// Iterate over all keys in the given keys and offsets
fn for_all<F: FnMut(&[u8])>(keys: &[u8], offsets: &[usize], mut f: F) {
    for i in 0..offsets.len() {
        let end = if i + 1 < offsets.len() {
            offsets[i + 1]
        } else {
            keys.len()
        };
        f(&keys[offsets[i]..end]);
    }
}

impl FilterPolicy for BloomFilterPolicy {
    fn name(&self) -> &'static str {
        "rldb.BloomFilterPolicy"
    }

    fn create(&self, keys: &[u8], offsets: &[usize]) -> Vec<u8> {
        let filter_bits = offsets.len() * self.bits_per_key as usize;
        let filter_bytes = 8.max((filter_bits + 7) / 8);
        let mut filter: Vec<u8> = vec![0; filter_bytes];
        filter.push(self.k as u8);

        let real_filter_bits = (filter_bytes * 8) as u32;
        for_all(keys, offsets, |key| {
            let mut h = Self::hash(key);
            let delta = (h >> 17) | (h << 15);
            for _ in 0..self.k {
                let bitpos = (h % real_filter_bits) as usize;
                filter[bitpos / 8] |= 1 << (bitpos % 8);
                h = h.wrapping_add(delta);
            }
        });

        filter
    }

    fn may_exist(&self, key: &[u8], filter: &[u8]) -> bool {
        if filter.is_empty() {
            return true;
        }
        let bits = (filter.len() - 1) as u32 * 8;
        let k = *filter.last().unwrap();
        let filter = &filter[..filter.len() - 1];

        assert!(k <= 30, "BloomFilterPolicy: k should be less than 30");

        let mut h = Self::hash(key);

        let delta = (h >> 17) | (h << 15);
        for _ in 0..k {
            let bitpos = (h % bits) as usize;

            if (filter[bitpos / 8] & (1 << (bitpos % 8))) == 0 {
                return false;
            }
            h = h.wrapping_add(delta);
        }

        true
    }
}

/// A filter policy that wraps another filter policy and converts internal keys to user keys
pub struct InternalKeyFilterPolicy<FP: FilterPolicy> {
    inner: FP,
}

impl<FP: FilterPolicy> InternalKeyFilterPolicy<FP> {
    pub fn new(inner: FP) -> Self {
        Self { inner }
    }
}

impl<FP: FilterPolicy> FilterPolicy for InternalKeyFilterPolicy<FP> {
    fn name(&self) -> &'static str {
        self.inner.name()
    }

    fn create(&self, keys: &[u8], offsets: &[usize]) -> Vec<u8> {
        let mut real_keys = Vec::with_capacity(keys.len() - offsets.len() * 8);
        let mut real_offsets = Vec::with_capacity(offsets.len());

        for_all(keys, offsets, |key| {
            real_offsets.push(real_keys.len());
            real_keys.extend_from_slice(&key[..key.len() - 8]);
        });

        self.inner.create(&real_keys, &real_offsets)
    }

    fn may_exist(&self, key: &[u8], filter: &[u8]) -> bool {
        self.inner.may_exist(&key[..key.len() - 8], filter)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests_gpt_4o {
        use super::*;

        #[test]
        fn test_no_filter_policy() {
            let policy = NoFilterPolicy;

            assert_eq!(policy.name(), "NoFilterPolicy");

            let keys = b"testkey";
            let offsets = vec![0];
            let filter = policy.create(keys, &offsets);

            assert!(filter.is_empty());
            assert!(policy.may_exist(b"testkey", &filter));
        }

        #[test]
        fn test_bloom_filter_policy_create() {
            let policy = BloomFilterPolicy::new(10);

            let keys = b"key1key2key3";
            let offsets = vec![0, 4, 8];
            let filter = policy.create(keys, &offsets);

            assert!(!filter.is_empty());
            assert_eq!(filter.len(), 9);
        }

        #[test]
        fn test_bloom_filter_policy_may_exist() {
            let policy = BloomFilterPolicy::new(10);

            let keys = b"key1key2key3";
            let offsets = vec![0, 4, 8];
            let filter = policy.create(keys, &offsets);

            assert!(policy.may_exist(b"key1", &filter));
            assert!(policy.may_exist(b"key2", &filter));
            assert!(policy.may_exist(b"key3", &filter));
            assert!(!policy.may_exist(b"non-key", &filter));
        }

        #[test]
        fn test_internal_key_filter_policy() {
            let bloom_policy = BloomFilterPolicy::new(10);
            let policy = InternalKeyFilterPolicy::new(bloom_policy);

            let keys = b"key1suffix00000000key2suffix00000000key3suffix00000000";
            let offsets = vec![0, 18, 36];
            let filter = policy.create(keys, &offsets);

            assert!(policy.may_exist(b"key1suffix00000000", &filter));
            assert!(policy.may_exist(b"key2suffix00000000", &filter));
            assert!(policy.may_exist(b"key3suffix00000000", &filter));
            assert!(!policy.may_exist(b"key4suffix00000000", &filter));
        }

        #[test]
        fn test_boxed_filter_policy() {
            let policy: Box<dyn FilterPolicy> = Box::new(BloomFilterPolicy::new(10));

            let keys = b"key1key2key3";
            let offsets = vec![0, 4, 8];
            let filter = policy.create(keys, &offsets);

            assert!(policy.may_exist(b"key1", &filter));
            assert!(policy.may_exist(b"key2", &filter));
            assert!(policy.may_exist(b"key3", &filter));
            assert!(!policy.may_exist(b"non-key", &filter));
        }

        #[test]
        fn test_rc_filter_policy() {
            let policy: Rc<dyn FilterPolicy> = Rc::new(BloomFilterPolicy::new(10));

            let keys = b"key1key2key3";
            let offsets = vec![0, 4, 8];
            let filter = policy.create(keys, &offsets);

            assert!(policy.may_exist(b"key1", &filter));
            assert!(policy.may_exist(b"key2", &filter));
            assert!(policy.may_exist(b"key3", &filter));
        }

        #[test]
        fn test_bloom_filter_policy_edge_cases() {
            let policy = BloomFilterPolicy::new(0);
            assert_eq!(policy.k, 1);

            let policy = BloomFilterPolicy::new(100);
            assert_eq!(policy.k, 30);
        }
    }

    mod tests_claude_3_5_sonnet {
        use super::*;

        #[test]
        fn test_bloom_filter_creation() {
            let policy = BloomFilterPolicy::new(10);
            let keys = b"hello\0world";
            let offsets = vec![0, 6];
            let filter = policy.create(keys, &offsets);
            assert!(!filter.is_empty());
        }

        #[test]
        fn test_bloom_filter_may_exist() {
            let policy = BloomFilterPolicy::new(10);
            let keys = b"hello\0world";
            let offsets = vec![0, 6];
            let filter = policy.create(keys, &offsets);

            assert!(!policy.may_exist(b"hello", &filter));
            assert!(policy.may_exist(b"world", &filter));
            assert!(!policy.may_exist(b"foo", &filter));
        }

        #[test]
        fn test_bloom_filter_empty_key() {
            let policy = BloomFilterPolicy::new(10);
            let keys = b"\0";
            let offsets = vec![0];
            let filter = policy.create(keys, &offsets);

            assert!(!policy.may_exist(b"", &filter));
        }

        #[test]
        fn test_bloom_filter_large_key() {
            let policy = BloomFilterPolicy::new(10);
            let large_key = vec![b'a'; 1000];
            let keys = large_key.as_slice();
            let offsets = vec![0];
            let filter = policy.create(keys, &offsets);

            assert!(policy.may_exist(&large_key, &filter));
        }

        #[test]
        fn test_bloom_filter_many_keys() {
            let policy = BloomFilterPolicy::new(10);
            let mut keys = Vec::new();
            let mut offsets = Vec::new();
            for i in 0..1000 {
                offsets.push(keys.len());
                keys.extend_from_slice(format!("key{}", i).as_bytes());
            }
            let filter = policy.create(&keys, &offsets);

            for i in 0..1000 {
                assert!(policy.may_exist(format!("key{}", i).as_bytes(), &filter));
            }
        }

        #[test]
        fn test_no_filter_policy() {
            let policy = NoFilterPolicy;
            let keys = b"hello\0world";
            let offsets = vec![0, 6];
            let filter = policy.create(keys, &offsets);

            assert!(filter.is_empty());
            assert!(policy.may_exist(b"anything", &filter));
        }

        #[test]
        fn test_bloom_filter_different_bits_per_key() {
            let policy1 = BloomFilterPolicy::new(8);
            let policy2 = BloomFilterPolicy::new(16);
            let keys = b"hello\0world";
            let offsets = vec![0, 6];
            let filter1 = policy1.create(keys, &offsets);
            let filter2 = policy2.create(keys, &offsets);

            assert_ne!(filter1, filter2);
        }

        #[test]
        fn test_bloom_filter_hash_collision() {
            assert_ne!(
                BloomFilterPolicy::hash(b"hello"),
                BloomFilterPolicy::hash(b"world")
            );
        }

        #[test]
        fn test_bloom_filter_policy_name() {
            let policy = BloomFilterPolicy::new(10);
            assert_eq!(policy.name(), "rldb.BloomFilterPolicy");
        }

    }
}
