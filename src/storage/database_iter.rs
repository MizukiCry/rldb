use std::cmp::Ordering;
use std::{cell::RefCell, rc::Rc};

use rand::random;

use crate::coredef::cmp::Cmp;

use crate::coredef::key::{parse_internal_key, truncate_ikey_to_key, LookupKey, ValueType};
use crate::coredef::types::{DbIterator, Direction, MergingIterator};
use crate::storage::version_set::VersionSet;

use crate::storage::snapshot::Snapshot;

const READ_BYTES_PERIOD: isize = 1 << 20;

/// Iterator of a database.
pub struct DatabaseIter {
    cmp: Rc<dyn Cmp>,
    version_set: Rc<RefCell<VersionSet>>,
    iter: MergingIterator,
    snapshot: Snapshot,
    direction: Direction,
    byte_count: isize,

    valid: bool,
    key: Vec<u8>,
    key_buf: Vec<u8>,
    value: Vec<u8>,
    value_buf: Vec<u8>,
}

impl DatabaseIter {
    pub fn new(
        cmp: Rc<dyn Cmp>,
        version_set: Rc<RefCell<VersionSet>>,
        iter: MergingIterator,
        snapshot: Snapshot,
    ) -> Self {
        Self {
            cmp,
            version_set,
            iter,
            snapshot,
            direction: Direction::Forward,
            byte_count: random::<isize>() % (2 * READ_BYTES_PERIOD),
            valid: false,
            key: Vec::new(),
            key_buf: Vec::new(),
            value: Vec::new(),
            value_buf: Vec::new(),
        }
    }

    fn record_read_sample(&mut self, len: usize) {
        self.byte_count -= len as isize;
        if self.byte_count < 0 {
            self.version_set
                .borrow()
                .current()
                .borrow_mut()
                .record_read_sample(&self.key_buf);
            while self.byte_count < 0 {
                self.byte_count += random::<isize>() % (2 * READ_BYTES_PERIOD);
            }
        }
    }

    fn find_next_user_entry(&mut self, mut skipping: bool) -> bool {
        assert!(self.iter.valid());
        assert!(self.direction == Direction::Forward);

        while self.iter.valid() {
            self.iter.current(&mut self.key_buf, &mut self.value);
            self.record_read_sample(self.key_buf.len() + self.value.len());
            let (t, seqnum, key) = parse_internal_key(&self.key_buf);

            if seqnum <= self.snapshot.seqnum() {
                if t == ValueType::TypeDeletion {
                    self.key = key.to_vec();
                    skipping = true;
                } else if t == ValueType::TypeValue
                    && (!skipping || self.cmp.cmp(key, &self.key) == Ordering::Greater)
                {
                    self.valid = true;
                    self.key.clear();
                    return true;
                }
            }
            self.iter.advance();
        }
        self.key.clear();
        self.valid = false;
        false
    }

    fn find_prev_user_entry(&mut self) -> bool {
        assert!(self.direction == Direction::Backward);

        let mut value_type = ValueType::TypeDeletion;
        while self.iter.valid() {
            self.iter.current(&mut self.key_buf, &mut self.value_buf);
            self.record_read_sample(self.key_buf.len() + self.value_buf.len());
            let (t, seqnum, key) = parse_internal_key(&self.key_buf);

            if seqnum > 0 && seqnum <= self.snapshot.seqnum() {
                if value_type == ValueType::TypeValue
                    && self.cmp.cmp(key, &self.key) == Ordering::Less
                {
                    break;
                }
                value_type = t;
                if t == ValueType::TypeDeletion {
                    self.key.clear();
                    self.value.clear();
                } else {
                    self.key = key.to_vec();
                    std::mem::swap(&mut self.value, &mut self.value_buf);
                }
            }
            self.iter.prev();
        }

        if value_type == ValueType::TypeDeletion {
            self.valid = false;
            self.key.clear();
            self.value.clear();
            self.direction = Direction::Forward;
        } else {
            self.valid = true;
        }
        true
    }
}

impl DbIterator for DatabaseIter {
    fn advance(&mut self) -> bool {
        if !self.valid() {
            self.seek_to_first();
            return self.valid();
        }

        if self.direction == Direction::Backward {
            self.direction = Direction::Forward;
            if !self.iter.valid() {
                self.iter.seek_to_first();
            } else {
                self.iter.advance();
            }
            if !self.iter.valid() {
                self.valid = false;
                self.key.clear();
                return false;
            }
        } else {
            assert!(self.iter.current(&mut self.key, &mut self.value));
            truncate_ikey_to_key(&mut self.key);
        }
        self.find_next_user_entry(true)
    }

    fn current(&self, key: &mut Vec<u8>, value: &mut Vec<u8>) -> bool {
        if !self.valid() {
            return false;
        }
        if self.direction == Direction::Forward {
            self.iter.current(key, value);
            truncate_ikey_to_key(key);
        } else {
            *key = self.key.clone();
            *value = self.value.clone();
        }
        true
    }

    fn prev(&mut self) -> bool {
        if !self.valid() {
            return false;
        }

        if self.direction == Direction::Forward {
            self.iter.current(&mut self.key, &mut self.value);
            truncate_ikey_to_key(&mut self.key);
            loop {
                self.iter.prev();
                if !self.iter.valid() {
                    self.valid = false;
                    self.key.clear();
                    self.value.clear();
                    return false;
                }
                self.iter.current(&mut self.key_buf, &mut self.value);
                truncate_ikey_to_key(&mut self.key_buf);
                if self.cmp.cmp(&self.key_buf, &self.key) == Ordering::Less {
                    break;
                }
            }
            self.direction = Direction::Backward;
        }
        self.find_prev_user_entry()
    }

    fn valid(&self) -> bool {
        self.valid
    }

    fn seek(&mut self, key: &[u8]) {
        self.direction = Direction::Forward;
        self.key.clear();
        self.value.clear();
        self.key
            .extend_from_slice(LookupKey::new(key, self.snapshot.seqnum()).internal_key());
        self.iter.seek(&self.key);
        if self.iter.valid() {
            self.find_next_user_entry(false);
        } else {
            self.valid = false;
        }
    }

    fn seek_to_first(&mut self) {
        self.direction = Direction::Forward;
        self.value.clear();
        self.iter.seek_to_first();
        if self.iter.valid() {
            self.find_next_user_entry(false);
        } else {
            self.valid = false;
        }
    }

    fn reset(&mut self) {
        self.iter.reset();
        self.valid = false;
        self.key.clear();
        self.key_buf.clear();
        self.value.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod test_database_iter {
        use crate::coredef::options::Options;
        use crate::coredef::types::DbIteratorWrapper;
        use crate::storage::database::testutil::build_db;
        use crate::storage::database::Database;

        use super::*;

        use std::collections::HashMap;
        use std::collections::HashSet;
        use std::iter::FromIterator;

        #[test]
        fn db_iter_basic_test() {
            let mut db = build_db().0;
            let mut iter = db.new_iter().unwrap();

            // keys and values come from make_version(); they are each the latest entry.
            let keys: &[&[u8]] = &[
                b"aaa", b"aab", b"aax", b"aba", b"bab", b"bba", b"cab", b"cba",
            ];
            let vals: &[&[u8]] = &[
                b"val1", b"val2", b"val2", b"val3", b"val4", b"val5", b"val2", b"val3",
            ];

            for (k, v) in keys.iter().zip(vals.iter()) {
                assert!(iter.advance());
                assert_eq!((k.to_vec(), v.to_vec()), iter.current_kv().unwrap());
            }
        }

        #[test]
        fn db_iter_reset() {
            let mut db = build_db().0;
            let mut iter = db.new_iter().unwrap();

            assert!(iter.advance());
            assert!(iter.valid());
            iter.reset();
            assert!(!iter.valid());
            assert!(iter.advance());
            assert!(iter.valid());
        }

        #[test]
        fn db_iter_test_fwd_backwd() {
            let mut db = build_db().0;
            let mut iter = db.new_iter().unwrap();

            // keys and values come from make_version(); they are each the latest entry.
            let keys: &[&[u8]] = &[
                b"aaa", b"aab", b"aax", b"aba", b"bab", b"bba", b"cab", b"cba",
            ];
            let vals: &[&[u8]] = &[
                b"val1", b"val2", b"val2", b"val3", b"val4", b"val5", b"val2", b"val3",
            ];

            // This specifies the direction that the iterator should move to. Based on this, an index
            // into keys/vals is incremented/decremented so that we get a nice test checking iterator
            // move correctness.
            let dirs: &[Direction] = &[
                Direction::Forward,
                Direction::Forward,
                Direction::Forward,
                Direction::Backward,
                Direction::Backward,
                Direction::Backward,
                Direction::Forward,
                Direction::Forward,
                Direction::Backward,
                Direction::Forward,
                Direction::Forward,
                Direction::Forward,
                Direction::Forward,
            ];
            let mut i = 0;
            iter.advance();
            for d in dirs {
                assert_eq!(
                    (keys[i].to_vec(), vals[i].to_vec()),
                    iter.current_kv().unwrap()
                );
                match *d {
                    Direction::Forward => {
                        assert!(iter.advance());
                        i += 1;
                    }
                    Direction::Backward => {
                        assert!(iter.prev());
                        i -= 1;
                    }
                }
            }
        }

        #[test]
        fn db_iter_test_seek() {
            let mut db = build_db().0;
            let mut iter = db.new_iter().unwrap();

            // gca is the deleted entry.
            let keys: &[&[u8]] = &[b"aab", b"aaa", b"cab", b"eaa", b"aaa", b"iba", b"fba"];
            let vals: &[&[u8]] = &[
                b"val2", b"val1", b"val2", b"val1", b"val1", b"val2", b"val3",
            ];

            for (k, v) in keys.iter().zip(vals.iter()) {
                eprintln!("{:?}", String::from_utf8(k.to_vec()).unwrap());
                iter.seek(k);
                assert_eq!((k.to_vec(), v.to_vec()), iter.current_kv().unwrap());
            }

            // seek past last.
            iter.seek(b"xxx");
            assert!(!iter.valid());
            iter.seek(b"aab");
            assert!(iter.valid());

            // Seek skips over deleted entry.
            iter.seek(b"gca");
            assert!(iter.valid());
            assert_eq!(
                (b"gda".to_vec(), b"val5".to_vec()),
                iter.current_kv().unwrap()
            );
        }

        #[test]
        fn db_iter_deleted_entry_not_returned() {
            let mut db = build_db().0;
            let mut iter = db.new_iter().unwrap();
            let must_not_appear = b"gca";

            for (k, _) in DbIteratorWrapper::new(&mut iter) {
                assert!(k.as_slice() != must_not_appear);
            }
        }

        #[test]
        fn db_iter_deleted_entry_not_returned_memtable() {
            let mut db = build_db().0;

            db.insert(b"xyz", b"123").unwrap();
            db.delete(b"xyz").unwrap();

            let mut iter = db.new_iter().unwrap();
            let must_not_appear = b"xyz";

            for (k, _) in DbIteratorWrapper::new(&mut iter) {
                assert!(k.as_slice() != must_not_appear);
            }
        }

        #[test]
        fn db_iter_repeated_open_close() {
            let opt;
            {
                let (mut db, opt_) = build_db();
                opt = opt_;

                db.insert(b"xx1", b"111").unwrap();
                db.insert(b"xx2", b"112").unwrap();
                db.insert(b"xx3", b"113").unwrap();
                db.insert(b"xx4", b"114").unwrap();
                db.delete(b"xx2").unwrap();
            }

            {
                let mut db = Database::open("db", opt.clone()).unwrap();
                db.insert(b"xx4", b"222").unwrap();
            }

            {
                let mut db = Database::open("db", opt).unwrap();

                let ss = db.get_snapshot();
                // xx5 should not be visible.
                db.insert(b"xx5", b"223").unwrap();

                let expected: HashMap<Vec<u8>, Vec<u8>> = HashMap::from_iter(
                    vec![
                        (b"xx1".to_vec(), b"111".to_vec()),
                        (b"xx4".to_vec(), b"222".to_vec()),
                        (b"aaa".to_vec(), b"val1".to_vec()),
                        (b"cab".to_vec(), b"val2".to_vec()),
                    ]
                    .into_iter(),
                );
                let non_existing: HashSet<Vec<u8>> = HashSet::from_iter(
                    vec![b"gca".to_vec(), b"xx2".to_vec(), b"xx5".to_vec()].into_iter(),
                );

                let mut iter = db.new_iter_at(ss.clone()).unwrap();
                for (k, v) in DbIteratorWrapper::new(&mut iter) {
                    if let Some(ev) = expected.get(&k) {
                        assert_eq!(ev, &v);
                    }
                    assert!(!non_existing.contains(&k));
                }
            }
        }

        #[test]
        fn db_iter_allow_empty_key() {
            let opt = Options::for_test();
            let mut db = Database::open("db", opt).unwrap();
            assert!(db.new_iter().unwrap().next().is_none());
            db.insert(&[], &[]).unwrap();
            assert!(db.new_iter().unwrap().next().is_some());
        }
    }
}
