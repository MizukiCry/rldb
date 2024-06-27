use std::rc::Rc;

use crate::coredef::cmp::{Cmp, MemtableKeyCmp};
use crate::coredef::key::{
    build_memtable_key, parse_internal_key, parse_memtable_key, InternalKey, LookupKey, UserKey,
    ValueType,
};
use crate::coredef::types::{DbIterator, SeqNum};
use crate::utils::skip_list::{SkipList, SkipListIter};

/// Memtable is a sorted table that stores key-value pairs in memory.
/// Based on SkipList and uses MemtableKey internally.
pub struct Memtable(SkipList);

impl Memtable {
    /// Wraps cmp in a MemtableKeyCmp
    pub fn new(cmp: Rc<dyn Cmp>) -> Self {
        Self::new_raw(Rc::new(MemtableKeyCmp(cmp)))
    }

    /// Does not wrap cmp
    pub fn new_raw(cmp: Rc<dyn Cmp>) -> Self {
        Self(SkipList::new(cmp))
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn approx_size(&self) -> usize {
        self.0.approx_size()
    }

    pub fn add(&mut self, key: UserKey, value: &[u8], t: ValueType, seqnum: SeqNum) {
        self.0
            .insert(build_memtable_key(key, value, t, seqnum), Vec::new());
    }

    /// Returns the value and whether the entry is deleted
    pub fn get(&self, key: &LookupKey) -> (Option<Vec<u8>>, bool) {
        let mut iter = self.0.iter();
        iter.seek(key.memtable_key());

        if let Some((mkey, _)) = iter.current_kv() {
            let (key_len, key_offset, tag, value_len, value_offset) = parse_memtable_key(&mkey);

            if key.user_key() == &mkey[key_offset..key_offset + key_len] {
                return if tag & 0xff == ValueType::TypeValue as u64 {
                    (
                        Some(mkey[value_offset..value_offset + value_len].to_vec()),
                        false,
                    )
                } else {
                    (None, true)
                };
            }
        }

        (None, false)
    }

    pub fn iter(&self) -> MemtableIterator {
        MemtableIterator(self.0.iter())
    }
}

pub struct MemtableIterator(SkipListIter);

impl DbIterator for MemtableIterator {
    fn advance(&mut self) -> bool {
        self.0.advance()
    }

    fn reset(&mut self) {
        self.0.reset();
    }

    fn prev(&mut self) -> bool {
        let mut key = Vec::new();
        let mut value = Vec::new();

        loop {
            if !self.0.prev() {
                return false;
            }
            if !self.0.current(&mut key, &mut value) {
                return false;
            }

            let tag = parse_memtable_key(&key).2;

            if tag & 0xff == ValueType::TypeValue as u64 {
                return true;
            }
        }
    }

    fn valid(&self) -> bool {
        self.0.valid()
    }

    /// Get the InternalKey and value
    fn current(&self, key: &mut Vec<u8>, value: &mut Vec<u8>) -> bool {
        if !self.valid() {
            return false;
        }

        assert!(
            self.0.current(key, value),
            "MemtableIterator::current failed"
        );

        let (key_len, key_offset, _, value_len, value_offset) = parse_memtable_key(key);
        *value = key[value_offset..value_offset + value_len].to_vec();
        *key = key[key_offset..key_offset + key_len + 8].to_vec();

        true
    }

    fn seek(&mut self, key: InternalKey) {
        let (_, seqnum, user_key) = parse_internal_key(key);
        self.0.seek(LookupKey::new(user_key, seqnum).memtable_key());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests_leveldb_rs {
        use crate::{
            coredef::{
                key::{parse_tag, truncate_ikey_to_key},
                options,
                types::DbIteratorWrapper,
            },
            utils::test_iterator_properties,
        };

        use super::*;
        // #[test]
        // fn test_shift_left() {
        //     let mut v = vec![1, 2, 3, 4, 5];
        //     shift_left(&mut v, 1);
        //     assert_eq!(v, vec![2, 3, 4, 5]);

        //     let mut v = vec![1, 2, 3, 4, 5];
        //     shift_left(&mut v, 4);
        //     assert_eq!(v, vec![5]);
        // }

        fn get_memtable() -> Memtable {
            let mut mt = Memtable::new(options::Options::for_test().cmp);
            let entries = vec![
                (ValueType::TypeValue, 115, "abc", "122"),
                (ValueType::TypeValue, 120, "abc", "123"),
                (ValueType::TypeValue, 121, "abd", "124"),
                (ValueType::TypeDeletion, 122, "abe", "125"),
                (ValueType::TypeValue, 123, "abf", "126"),
            ];

            for e in entries.iter() {
                mt.add(e.2.as_bytes(), e.3.as_bytes(), e.0, e.1);
            }
            mt
        }

        #[test]
        fn test_memtable_parse_tag() {
            let tag = (12345 << 8) | 1;
            assert_eq!(parse_tag(tag), (ValueType::TypeValue, 12345));
        }

        #[test]
        fn test_memtable_add() {
            let mut mt = Memtable::new(options::Options::for_test().cmp);
            mt.add(
                "abc".as_bytes(),
                "123".as_bytes(),
                ValueType::TypeValue,
                123,
            );

            assert_eq!(
                mt.0.iter().next().unwrap().0,
                &[11, 97, 98, 99, 1, 123, 0, 0, 0, 0, 0, 0, 3, 49, 50, 51]
            );
            assert_eq!(
                mt.iter().next().unwrap().0,
                &[97, 98, 99, 1, 123, 0, 0, 0, 0, 0, 0]
            );
        }

        #[test]
        fn test_memtable_add_get() {
            let mt = get_memtable();

            // Smaller sequence number doesn't find entry
            if let Some(v) = mt.get(&LookupKey::new("abc".as_bytes(), 110)).0 {
                eprintln!("{:?}", v);
                panic!("found");
            }

            if let Some(v) = mt.get(&LookupKey::new("abf".as_bytes(), 110)).0 {
                eprintln!("{:?}", v);
                panic!("found");
            }

            // Bigger sequence number falls back to next smaller
            if let Some(v) = mt.get(&LookupKey::new("abc".as_bytes(), 116)).0 {
                assert_eq!(v, "122".as_bytes());
            } else {
                panic!("not found");
            }

            // Exact match works
            if let (Some(v), deleted) = mt.get(&LookupKey::new("abc".as_bytes(), 120)) {
                assert_eq!(v, "123".as_bytes());
                assert!(!deleted);
            } else {
                panic!("not found");
            }

            if let (None, deleted) = mt.get(&LookupKey::new("abe".as_bytes(), 122)) {
                assert!(deleted);
            } else {
                panic!("found deleted");
            }

            if let Some(v) = mt.get(&LookupKey::new("abf".as_bytes(), 129)).0 {
                assert_eq!(v, "126".as_bytes());
            } else {
                panic!("not found");
            }
        }

        #[test]
        fn test_memtable_iterator_init() {
            let mt = get_memtable();
            let mut iter = mt.iter();

            assert!(!iter.valid());
            iter.next();
            assert!(iter.valid());
            assert_eq!(
                iter.current_kv().unwrap().0,
                vec![97, 98, 99, 1, 120, 0, 0, 0, 0, 0, 0].as_slice()
            );
            iter.reset();
            assert!(!iter.valid());
        }

        #[test]
        fn test_memtable_iterator_seek() {
            let mt = get_memtable();
            let mut iter = mt.iter();

            assert!(!iter.valid());

            iter.seek(LookupKey::new("abc".as_bytes(), 400).internal_key());
            let (mut gotkey, gotval) = iter.current_kv().unwrap();
            truncate_ikey_to_key(&mut gotkey);
            assert_eq!(
                ("abc".as_bytes(), "123".as_bytes()),
                (gotkey.as_slice(), gotval.as_slice())
            );

            iter.seek(LookupKey::new("xxx".as_bytes(), 400).internal_key());
            assert!(!iter.valid());

            iter.seek(LookupKey::new("abd".as_bytes(), 400).internal_key());
            let (mut gotkey, gotval) = iter.current_kv().unwrap();
            truncate_ikey_to_key(&mut gotkey);
            assert_eq!(
                ("abd".as_bytes(), "124".as_bytes()),
                (gotkey.as_slice(), gotval.as_slice())
            );
        }

        #[test]
        fn test_memtable_iterator_fwd() {
            let mt = get_memtable();
            let mut iter = mt.iter();

            let expected = vec![
                "123".as_bytes(), /* i.e., the abc entry with
                                   * higher sequence number comes first */
                "122".as_bytes(),
                "124".as_bytes(),
                // deleted entry:
                "125".as_bytes(),
                "126".as_bytes(),
            ];
            let mut i = 0;

            for (_, v) in DbIteratorWrapper::new(&mut iter) {
                assert_eq!(v, expected[i]);
                i += 1;
            }
        }

        #[test]
        fn test_memtable_iterator_reverse() {
            let mt = get_memtable();
            let mut iter = mt.iter();

            // Bigger sequence number comes first
            iter.next();
            assert!(iter.valid());
            assert_eq!(
                iter.current_kv().unwrap().0,
                vec![97, 98, 99, 1, 120, 0, 0, 0, 0, 0, 0].as_slice()
            );

            iter.next();
            assert!(iter.valid());
            assert_eq!(
                iter.current_kv().unwrap().0,
                vec![97, 98, 99, 1, 115, 0, 0, 0, 0, 0, 0].as_slice()
            );

            iter.next();
            assert!(iter.valid());
            assert_eq!(
                iter.current_kv().unwrap().0,
                vec![97, 98, 100, 1, 121, 0, 0, 0, 0, 0, 0].as_slice()
            );

            iter.prev();
            assert!(iter.valid());
            assert_eq!(
                iter.current_kv().unwrap().0,
                vec![97, 98, 99, 1, 115, 0, 0, 0, 0, 0, 0].as_slice()
            );

            iter.prev();
            assert!(iter.valid());
            assert_eq!(
                iter.current_kv().unwrap().0,
                vec![97, 98, 99, 1, 120, 0, 0, 0, 0, 0, 0].as_slice()
            );

            iter.prev();
            assert!(!iter.valid());
        }

        #[test]
        fn test_memtable_parse_key() {
            let key = vec![11, 1, 2, 3, 1, 123, 0, 0, 0, 0, 0, 0, 3, 4, 5, 6];
            let (keylen, keyoff, tag, vallen, valoff) = parse_memtable_key(&key);
            assert_eq!(keylen, 3);
            assert_eq!(&key[keyoff..keyoff + keylen], vec![1, 2, 3].as_slice());
            assert_eq!(tag, 123 << 8 | 1);
            assert_eq!(vallen, 3);
            assert_eq!(&key[valoff..valoff + vallen], vec![4, 5, 6].as_slice());
        }

        #[test]
        fn test_memtable_iterator_behavior() {
            let mut mt = Memtable::new(options::Options::for_test().cmp);
            let entries = vec![
                (115, "abc", "122"),
                (120, "abd", "123"),
                (121, "abe", "124"),
                (123, "abf", "126"),
            ];

            for e in entries.iter() {
                mt.add(e.1.as_bytes(), e.2.as_bytes(), ValueType::TypeValue, e.0);
            }

            test_iterator_properties(mt.iter());
        }
    }
}
