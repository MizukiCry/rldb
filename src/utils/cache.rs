use std::collections::HashMap;

use super::list::List;

pub type CacheKey = [u8; 16];
pub type CacheID = u64;

pub struct Cache<T> {
    list: List<CacheKey>,
    map: HashMap<CacheKey, (T, usize)>,
    capacity: usize,
    id: CacheID,
}

impl<T> Cache<T> {
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0, "capacity must be greater than 0");
        Cache {
            list: List::new(capacity),
            map: HashMap::with_capacity(1024),
            capacity,
            id: 0,
        }
    }

    pub fn new_cache_id(&mut self) -> CacheID {
        self.id += 1;
        self.id
    }

    pub fn size(&self) -> usize {
        self.list.size()
    }

    pub fn capacity(&self) -> usize {
        self.capacity
    }

    pub fn insert(&mut self, key: &CacheKey, value: T) {
        if self.size() == self.capacity {
            self.map.remove(&self.list.pop_back());
        }
        self.map.insert(*key, (value, self.list.push_front(*key)));
    }

    pub fn get<'a>(&'a mut self, key: &CacheKey) -> Option<&'a T> {
        self.map.get(key).map(|(value, pos)| {
            self.list.move_to_front(*pos);
            value
        })
    }

    pub fn remove(&mut self, key: &CacheKey) -> Option<T> {
        self.map.remove(key).map(|(value, pos)| {
            self.list.remove(pos);
            value
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_cache_key(key: Vec<u8>) -> CacheKey {
        assert!(
            key.len() <= 16,
            "key length must be less than or equal to 16"
        );
        let mut cache_key = [0; 16];
        for i in 0..key.len() {
            cache_key[i] = key[i];
        }
        cache_key
    }

    mod tests_gpt_4o {
        use super::*;

        #[test]
        fn test_new_cache() {
            let cache: Cache<i32> = Cache::new(10);
            assert_eq!(cache.capacity(), 10);
            assert_eq!(cache.size(), 0);
            assert_eq!(cache.id, 0);
        }

        #[test]
        #[should_panic(expected = "capacity must be greater than 0")]
        fn test_new_cache_with_zero_capacity() {
            let _cache: Cache<i32> = Cache::new(0);
        }

        #[test]
        fn test_new_cache_id() {
            let mut cache: Cache<i32> = Cache::new(10);
            assert_eq!(cache.new_cache_id(), 1);
            assert_eq!(cache.new_cache_id(), 2);
        }

        #[test]
        fn test_insert_and_get() {
            let mut cache: Cache<i32> = Cache::new(2);
            let key1 = make_cache_key(vec![1, 2, 3]);
            let key2 = make_cache_key(vec![4, 5, 6]);

            cache.insert(&key1, 10);
            cache.insert(&key2, 20);

            assert_eq!(cache.get(&key1), Some(&10));
            assert_eq!(cache.get(&key2), Some(&20));
        }

        #[test]
        fn test_insert_with_capacity_reached() {
            let mut cache: Cache<i32> = Cache::new(2);
            let key1 = make_cache_key(vec![1, 2, 3]);
            let key2 = make_cache_key(vec![4, 5, 6]);
            let key3 = make_cache_key(vec![7, 8, 9]);

            cache.insert(&key1, 10);
            cache.insert(&key2, 20);
            cache.insert(&key3, 30);

            assert_eq!(cache.size(), 2);
            assert!(cache.get(&key1).is_none());
            assert_eq!(cache.get(&key2), Some(&20));
            assert_eq!(cache.get(&key3), Some(&30));
        }

        #[test]
        fn test_get_updates_recently_used() {
            let mut cache: Cache<i32> = Cache::new(2);
            let key1 = make_cache_key(vec![1, 2, 3]);
            let key2 = make_cache_key(vec![4, 5, 6]);

            cache.insert(&key1, 10);
            cache.insert(&key2, 20);
            cache.get(&key1); // key1 is now recently used

            let key3 = make_cache_key(vec![7, 8, 9]);
            cache.insert(&key3, 30);

            assert!(cache.get(&key2).is_none()); // key2 should be evicted
            assert_eq!(cache.get(&key1), Some(&10));
            assert_eq!(cache.get(&key3), Some(&30));
        }

        #[test]
        fn test_remove() {
            let mut cache: Cache<i32> = Cache::new(2);
            let key1 = make_cache_key(vec![1, 2, 3]);
            let key2 = make_cache_key(vec![4, 5, 6]);

            cache.insert(&key1, 10);
            cache.insert(&key2, 20);

            assert_eq!(cache.remove(&key1), Some(10));
            assert!(cache.get(&key1).is_none());
            assert_eq!(cache.size(), 1);
        }

        #[test]
        fn test_remove_nonexistent_key() {
            let mut cache: Cache<i32> = Cache::new(2);
            let key1 = make_cache_key(vec![1, 2, 3]);

            assert!(cache.remove(&key1).is_none());
        }
    }

    mod tests_gemini_1_5_flash {
        use super::*;

        #[test]
        fn test_new() {
            let cache: Cache<i32> = Cache::new(10);
            assert_eq!(cache.capacity(), 10);
            assert_eq!(cache.size(), 0);
        }

        #[test]
        #[should_panic(expected = "capacity must be greater than 0")]
        fn test_new_with_zero_capacity() {
            let _cache: Cache<i32> = Cache::new(0);
        }

        #[test]
        fn test_new_cache_id() {
            let mut cache: Cache<i32> = Cache::new(10);
            assert_eq!(cache.new_cache_id(), 1);
            assert_eq!(cache.new_cache_id(), 2);
        }

        #[test]
        fn test_insert() {
            let mut cache: Cache<i32> = Cache::new(3);
            let key1 = make_cache_key(vec![1, 2, 3]);
            let key2 = make_cache_key(vec![4, 5, 6]);
            let key3 = make_cache_key(vec![7, 8, 9]);
            cache.insert(&key1, 1);
            cache.insert(&key2, 2);
            cache.insert(&key3, 3);
            assert_eq!(cache.size(), 3);
            assert_eq!(cache.get(&key1), Some(&1));
            assert_eq!(cache.get(&key2), Some(&2));
            assert_eq!(cache.get(&key3), Some(&3));
        }

        #[test]
        fn test_insert_with_full_capacity() {
            let mut cache: Cache<i32> = Cache::new(2);
            let key1 = make_cache_key(vec![1, 2, 3]);
            let key2 = make_cache_key(vec![4, 5, 6]);
            let key3 = make_cache_key(vec![7, 8, 9]);
            cache.insert(&key1, 1);
            cache.insert(&key2, 2);
            cache.insert(&key3, 3);
            assert_eq!(cache.size(), 2);
            assert_eq!(cache.get(&key1), None);
            assert_eq!(cache.get(&key2), Some(&2));
            assert_eq!(cache.get(&key3), Some(&3));
        }

        #[test]
        fn test_get() {
            let mut cache: Cache<i32> = Cache::new(3);
            let key1 = make_cache_key(vec![1, 2, 3]);
            let key2 = make_cache_key(vec![4, 5, 6]);
            cache.insert(&key1, 1);
            cache.insert(&key2, 2);
            assert_eq!(cache.get(&key1), Some(&1));
            assert_eq!(cache.get(&key2), Some(&2));
            assert_eq!(cache.get(&make_cache_key(vec![7, 8, 9])), None);
        }

        #[test]
        fn test_get_with_lru() {
            let mut cache: Cache<i32> = Cache::new(3);
            let key1 = make_cache_key(vec![1, 2, 3]);
            let key2 = make_cache_key(vec![4, 5, 6]);
            let key3 = make_cache_key(vec![7, 8, 9]);
            cache.insert(&key1, 1);
            cache.insert(&key2, 2);
            cache.insert(&key3, 3);
            cache.get(&key1);
            cache.insert(&key2, 4);
            assert_eq!(cache.get(&key1), Some(&1));
            assert_eq!(cache.get(&key2), Some(&4));
            assert_eq!(cache.get(&key3), Some(&3));
        }

        #[test]
        fn test_remove() {
            let mut cache: Cache<i32> = Cache::new(3);
            let key1 = make_cache_key(vec![1, 2, 3]);
            let key2 = make_cache_key(vec![4, 5, 6]);
            cache.insert(&key1, 1);
            cache.insert(&key2, 2);
            assert_eq!(cache.remove(&key1), Some(1));
            assert_eq!(cache.size(), 1);
            assert_eq!(cache.get(&key1), None);
            assert_eq!(cache.get(&key2), Some(&2));
        }

        #[test]
        fn test_remove_non_existent_key() {
            let mut cache: Cache<i32> = Cache::new(3);
            let key1 = make_cache_key(vec![1, 2, 3]);
            let key2 = make_cache_key(vec![4, 5, 6]);
            cache.insert(&key1, 1);
            assert_eq!(cache.remove(&key2), None);
            assert_eq!(cache.size(), 1);
            assert_eq!(cache.get(&key1), Some(&1));
        }
    }
}
