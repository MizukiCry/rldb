use std::{cmp::Ordering, rc::Rc};

use super::{
    cmp::Cmp,
    error::{err, Result, StatusCode},
};

/// A larger sequence number is more recent
pub type SeqNum = u64;
pub const MAX_SEQNUM: SeqNum = (1 << 56) - 1;

#[derive(Clone, Copy, PartialEq)]
pub enum Direction {
    Forward,
    Backward,
}

/// Universal iterator trait
/// An iterator is invalid before first `advance` call (positioned before the first element)
pub trait DbIterator {
    /// Move one step to the next element
    /// Returns false if no more element
    fn advance(&mut self) -> bool;

    fn current(&self, key: &mut Vec<u8>, value: &mut Vec<u8>) -> bool;

    fn current_kv(&self) -> Option<(Vec<u8>, Vec<u8>)> {
        let mut key = Vec::new();
        let mut value = Vec::new();
        if self.current(&mut key, &mut value) {
            Some((key, value))
        } else {
            None
        }
    }

    // Move to the first element >= key
    fn seek(&mut self, key: &[u8]);

    fn seek_to_first(&mut self) {
        self.reset();
        self.advance();
    }

    /// Move to the position before the first element
    /// Will be `!valid()` after this operation
    fn reset(&mut self);

    fn valid(&self) -> bool;

    /// Inefficient for single direction iterator
    fn prev(&mut self) -> bool;

    fn next(&mut self) -> Option<(Vec<u8>, Vec<u8>)> {
        if !self.advance() {
            return None;
        }
        let mut key = Vec::new();
        let mut value = Vec::new();
        if self.current(&mut key, &mut value) {
            Some((key, value))
        } else {
            None
        }
    }
}

pub struct DbIteratorWrapper<'a, It: 'a> {
    inner: &'a mut It,
}

impl<'a, It: DbIterator> DbIteratorWrapper<'a, It> {
    #[allow(dead_code)]
    pub fn new(inner: &'a mut It) -> Self {
        Self { inner }
    }
}

impl<'a, It: DbIterator> Iterator for DbIteratorWrapper<'a, It> {
    type Item = (Vec<u8>, Vec<u8>);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl DbIterator for Box<dyn DbIterator> {
    fn advance(&mut self) -> bool {
        self.as_mut().advance()
    }

    fn current(&self, key: &mut Vec<u8>, value: &mut Vec<u8>) -> bool {
        self.as_ref().current(key, value)
    }

    fn seek(&mut self, key: &[u8]) {
        self.as_mut().seek(key)
    }

    fn reset(&mut self) {
        self.as_mut().reset()
    }

    fn valid(&self) -> bool {
        self.as_ref().valid()
    }

    fn prev(&mut self) -> bool {
        self.as_mut().prev()
    }
}

pub struct MergingIterator {
    iters: Vec<Box<dyn DbIterator>>,
    current: Option<usize>,
    direction: Direction,
    cmp: Rc<dyn Cmp>,
}

impl MergingIterator {
    pub fn new(cmp: Rc<dyn Cmp>, iters: Vec<Box<dyn DbIterator>>) -> Self {
        Self {
            iters,
            current: None,
            direction: Direction::Forward,
            cmp,
        }
    }

    fn init(&mut self) {
        for iter in &mut self.iters {
            iter.reset();
            iter.advance();
            if !iter.valid() {
                iter.reset();
            }
        }
        self.find(true);
    }

    fn find(&mut self, smallest: bool) {
        if self.iters.is_empty() {
            return;
        }

        let ord = if smallest {
            Ordering::Less
        } else {
            Ordering::Greater
        };

        self.current = None;
        let mut current_key = Vec::new();
        let mut scratch = Vec::new();
        for i in 0..self.iters.len() {
            let mut new_key = Vec::new();
            if !self.iters[i].current(&mut new_key, &mut scratch) {
                continue;
            }
            if self.current.is_none() || self.cmp.cmp(&new_key, &current_key) == ord {
                self.current = Some(i);
                current_key = new_key;
            }
        }
    }

    fn update_direction(&mut self, direction: Direction) {
        if self.direction == direction {
            return;
        }

        if let Some(current) = self.current {
            if let Some((key, _)) = self.current_kv() {
                self.direction = direction;
                for (i, iter) in self.iters.iter_mut().enumerate() {
                    if i != current {
                        iter.seek(&key);

                        if direction == Direction::Forward {
                            if let Some((temp_key, _)) = iter.current_kv() {
                                if self.cmp.cmp(&temp_key, &key) == Ordering::Equal {
                                    iter.advance();
                                }
                            }
                        } else if iter.valid() {
                            iter.prev();
                        } else {
                            while iter.advance() {}
                        }
                    }
                }
            }
        }
    }
}

impl DbIterator for MergingIterator {
    fn advance(&mut self) -> bool {
        if let Some(i) = self.current {
            self.update_direction(Direction::Forward);
            if !self.iters[i].advance() {
                self.iters[i].reset();
            }
            self.find(true);
        } else {
            self.init();
        }
        self.valid()
    }

    fn valid(&self) -> bool {
        self.current.is_some_and(|i| self.iters[i].valid())
    }

    fn seek(&mut self, key: &[u8]) {
        for iter in &mut self.iters {
            iter.seek(key);
        }
        self.find(true);
    }

    fn reset(&mut self) {
        for iter in &mut self.iters {
            iter.reset();
        }
        self.current = None;
    }

    fn current(&self, key: &mut Vec<u8>, value: &mut Vec<u8>) -> bool {
        self.current
            .is_some_and(|i| self.iters[i].current(key, value))
    }

    fn prev(&mut self) -> bool {
        if let Some(i) = self.current {
            if self.iters[i].valid() {
                self.update_direction(Direction::Backward);
                self.iters[i].prev();
                self.find(false);
                return self.valid();
            }
        }
        false
    }
}

pub type FileID = u64;

#[derive(Clone, Debug, Default, PartialEq)]
pub struct FileMetaData {
    pub allowed_seeks: usize,
    pub id: FileID,
    pub size: usize,
    // Internal key format
    pub smallest: Vec<u8>,
    pub largest: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum FileType {
    Log,
    DBLock,
    Table,
    Descriptor,
    Current,
    Temp,
    InfoLog,
}

pub fn parse_file_name(name: &str) -> Result<(FileID, FileType)> {
    if name == "CURRENT" {
        Ok((0, FileType::Current))
    } else if name == "LOCK" {
        Ok((0, FileType::DBLock))
    } else if name == "LOG" || name == "LOG.old" {
        Ok((0, FileType::InfoLog))
    } else if name.starts_with("MANIFEST-") {
        if let Some(i) = name.find('-') {
            if let Ok(id) = FileID::from_str_radix(&name[i + 1..], 10) {
                Ok((id, FileType::Descriptor))
            } else {
                err(StatusCode::InvalidArgument, "manifest file has invalid id")
            }
        } else {
            err(StatusCode::InvalidArgument, "manifest file has no dash")
        }
    } else if let Some(i) = name.find('.') {
        if let Ok(id) = FileID::from_str_radix(&name[..i], 10) {
            let file_type = match &name[i + 1..] {
                "log" => FileType::Log,
                "sst" | "ldb" => FileType::Table,
                "dbtmp" => FileType::Temp,
                _ => return err(StatusCode::InvalidArgument, "Invalid file type"),
            };
            Ok((id, file_type))
        } else {
            err(StatusCode::InvalidArgument, "Invalid file id or temp file")
        }
    } else {
        err(StatusCode::InvalidArgument, "Invalid file name")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests_leveldb_rs {
        use super::*;

        #[test]
        fn test_types_parse_file_name() {
            for c in &[
                ("CURRENT", (0, FileType::Current)),
                ("LOCK", (0, FileType::DBLock)),
                ("LOG", (0, FileType::InfoLog)),
                ("LOG.old", (0, FileType::InfoLog)),
                ("MANIFEST-01234", (1234, FileType::Descriptor)),
                ("001122.sst", (1122, FileType::Table)),
                ("001122.ldb", (1122, FileType::Table)),
                ("001122.dbtmp", (1122, FileType::Temp)),
            ] {
                assert_eq!(parse_file_name(c.0).unwrap(), c.1);
            }
            assert!(parse_file_name("xyz.LOCK").is_err());
            assert!(parse_file_name("01a.sst").is_err());
            assert!(parse_file_name("0011.abc").is_err());
            assert!(parse_file_name("MANIFEST-trolol").is_err());
        }

        mod merging_iterator {
            use crate::coredef::cmp::DefaultCmp;
            use crate::utils::skip_list::SkipList;
            use crate::utils::test_iterator_properties;

            use super::*;

            fn make_skiplist() -> SkipList {
                let mut skm = SkipList::new(Rc::new(DefaultCmp));
                let keys = vec![
                    "aba", "abb", "abc", "abd", "abe", "abf", "abg", "abh", "abi", "abj", "abk",
                    "abl", "abm", "abn", "abo", "abp", "abq", "abr", "abs", "abt", "abu", "abv",
                    "abw", "abx", "aby", "abz",
                ];

                for k in keys {
                    skm.insert(k.as_bytes().to_vec(), "def".as_bytes().to_vec());
                }
                skm
            }

            struct TestDbIter<'a> {
                v: Vec<(&'a [u8], &'a [u8])>,
                ix: usize,
                init: bool,
            }

            impl<'a> TestDbIter<'a> {
                pub fn new(c: Vec<(&'a [u8], &'a [u8])>) -> TestDbIter<'a> {
                    TestDbIter {
                        v: c,
                        ix: 0,
                        init: false,
                    }
                }
            }

            impl<'a> DbIterator for TestDbIter<'a> {
                fn advance(&mut self) -> bool {
                    if self.ix == self.v.len() - 1 {
                        self.ix += 1;
                        false
                    } else if !self.init {
                        self.init = true;
                        true
                    } else {
                        self.ix += 1;
                        true
                    }
                }
                fn reset(&mut self) {
                    self.ix = 0;
                    self.init = false;
                }
                fn current(&self, key: &mut Vec<u8>, val: &mut Vec<u8>) -> bool {
                    if self.init && self.ix < self.v.len() {
                        key.clear();
                        val.clear();
                        key.extend_from_slice(self.v[self.ix].0);
                        val.extend_from_slice(self.v[self.ix].1);
                        true
                    } else {
                        false
                    }
                }
                fn valid(&self) -> bool {
                    self.init && self.ix < self.v.len()
                }
                fn seek(&mut self, k: &[u8]) {
                    self.ix = 0;
                    self.init = true;
                    while self.ix < self.v.len()
                        && DefaultCmp.cmp(self.v[self.ix].0, k) == Ordering::Less
                    {
                        self.ix += 1;
                    }
                }
                fn prev(&mut self) -> bool {
                    if !self.init || self.ix == 0 {
                        self.init = false;
                        false
                    } else {
                        self.ix -= 1;
                        true
                    }
                }
            }

            #[test]
            fn test_merging_one() {
                let skm = make_skiplist();
                let iter = skm.iter();
                let mut iter2 = skm.iter();

                let mut miter = MergingIterator::new(Rc::new(DefaultCmp), vec![Box::new(iter)]);

                loop {
                    if let Some((k, v)) = miter.next() {
                        if let Some((k2, v2)) = iter2.next() {
                            assert_eq!(k, k2);
                            assert_eq!(v, v2);
                        } else {
                            panic!("Expected element from iter2");
                        }
                    } else {
                        break;
                    }
                }
            }

            #[test]
            fn test_merging_two() {
                let skm = make_skiplist();
                let iter = skm.iter();
                let iter2 = skm.iter();

                let mut miter = MergingIterator::new(
                    Rc::new(DefaultCmp),
                    vec![Box::new(iter), Box::new(iter2)],
                );

                loop {
                    if let Some((k, v)) = miter.next() {
                        if let Some((k2, v2)) = miter.next() {
                            assert_eq!(k, k2);
                            assert_eq!(v, v2);
                        } else {
                            panic!("Odd number of elements");
                        }
                    } else {
                        break;
                    }
                }
            }

            #[test]
            fn test_merging_zero() {
                let mut miter = MergingIterator::new(Rc::new(DefaultCmp), vec![]);
                assert_eq!(0, DbIteratorWrapper::new(&mut miter).count());
            }

            #[test]
            fn test_merging_behavior() {
                let val = "def".as_bytes();
                let iter = TestDbIter::new(vec![(b("aba"), val), (b("abc"), val)]);
                let iter2 = TestDbIter::new(vec![(b("abb"), val), (b("abd"), val)]);
                let miter = MergingIterator::new(
                    Rc::new(DefaultCmp),
                    vec![Box::new(iter), Box::new(iter2)],
                );
                test_iterator_properties(miter);
            }

            #[test]
            fn test_merging_forward_backward() {
                let val = "def".as_bytes();
                let iter = TestDbIter::new(vec![(b("aba"), val), (b("abc"), val), (b("abe"), val)]);
                let iter2 = TestDbIter::new(vec![(b("abb"), val), (b("abd"), val)]);

                let mut miter = MergingIterator::new(
                    Rc::new(DefaultCmp),
                    vec![Box::new(iter), Box::new(iter2)],
                );

                // miter should return the following sequence: [aba, abb, abc, abd, abe]

                // -> aba
                let first = miter.next();
                // -> abb
                let second = miter.next();
                // -> abc
                let third = miter.next();
                // eprintln!("{:?} {:?} {:?}", first, second, third);

                assert!(first != third);
                // abb <-
                assert!(miter.prev());
                assert_eq!(second, miter.current_kv());
                // aba <-
                assert!(miter.prev());
                assert_eq!(first, miter.current_kv());
                // -> abb
                assert!(miter.advance());
                assert_eq!(second, miter.current_kv());
                // -> abc
                assert!(miter.advance());
                assert_eq!(third, miter.current_kv());
                // -> abd
                assert!(miter.advance());
                assert_eq!(Some((b("abd").to_vec(), val.to_vec())), miter.current_kv());
            }

            fn b(s: &'static str) -> &'static [u8] {
                s.as_bytes()
            }

            #[test]
            fn test_merging_real() {
                let val = "def".as_bytes();

                let it1 =
                    TestDbIter::new(vec![(&b("aba"), val), (&b("abc"), val), (&b("abe"), val)]);
                let it2 = TestDbIter::new(vec![(&b("abb"), val), (&b("abd"), val)]);
                let expected = vec![b("aba"), b("abb"), b("abc"), b("abd"), b("abe")];

                let mut iter =
                    MergingIterator::new(Rc::new(DefaultCmp), vec![Box::new(it1), Box::new(it2)]);

                let mut i = 0;
                for (k, _) in DbIteratorWrapper::new(&mut iter) {
                    assert_eq!(k, expected[i]);
                    i += 1;
                }
            }

            #[test]
            fn test_merging_seek_reset() {
                let val = "def".as_bytes();

                let it1 = TestDbIter::new(vec![(b("aba"), val), (b("abc"), val), (b("abe"), val)]);
                let it2 = TestDbIter::new(vec![(b("abb"), val), (b("abd"), val)]);

                let mut iter =
                    MergingIterator::new(Rc::new(DefaultCmp), vec![Box::new(it1), Box::new(it2)]);

                assert!(!iter.valid());
                iter.advance();
                assert!(iter.valid());
                assert!(iter.current_kv().is_some());

                iter.seek("abc".as_bytes());
                assert_eq!(iter.current_kv(), Some((b("abc").to_vec(), val.to_vec())));
                iter.seek("ab0".as_bytes());
                assert_eq!(iter.current_kv(), Some((b("aba").to_vec(), val.to_vec())));
                iter.seek("abx".as_bytes());
                assert_eq!(iter.current_kv(), None);

                iter.reset();
                assert!(!iter.valid());
                iter.next();
                assert_eq!(iter.current_kv(), Some((b("aba").to_vec(), val.to_vec())));
            }
        }
    }
}
