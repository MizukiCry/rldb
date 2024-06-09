use rand::{rngs::StdRng, RngCore, SeedableRng};
use std::{cell::RefCell, cmp::Ordering, mem::size_of, rc::Rc};

use crate::coredef::{cmp::Cmp, types::DbIterator};

const MAX_HEIGHT: usize = 12;
const GROW_FACTOR: u32 = 4;

/// Skiplist node
struct Node {
    key: Vec<u8>,
    value: Vec<u8>,
    next: Option<Box<Node>>,
    skips: Vec<Option<*mut Node>>,
}

struct InnerSkipList {
    head: Box<Node>,
    rand_rng: StdRng,
    len: usize,

    // Approximate memory usage
    approx_size: usize,
    cmp: Rc<dyn Cmp>,
}

impl InnerSkipList {
    fn random_height(&mut self) -> usize {
        let mut height = 1;
        while height < MAX_HEIGHT && self.rand_rng.next_u32() % GROW_FACTOR == 0 {
            height += 1;
        }
        height
    }

    /// Whether a key starts with the given prefix exists
    fn contains(&self, key: &[u8]) -> bool {
        if let Some(node) = self.seek_ge(key) {
            node.key.starts_with(key)
        } else {
            false
        }
    }

    fn insert(&mut self, key: Vec<u8>, value: Vec<u8>) {
        assert!(!key.is_empty(), "Key cannot be empty");

        let mut current: *mut Node = self.head.as_mut();
        let mut level = MAX_HEIGHT - 1;

        let new_height = self.random_height();
        let mut prevs: Vec<*mut Node> = vec![std::ptr::null_mut(); MAX_HEIGHT];

        self.approx_size += size_of::<Node>()
            + size_of::<Option<*mut Node>>() * new_height
            + key.len()
            + value.len();
        self.len += 1;

        loop {
            unsafe {
                if let Some(next) = (*current).skips[level] {
                    match self.cmp.cmp(&(*next).key, &key) {
                        Ordering::Less => {
                            current = next;
                            continue;
                        }
                        Ordering::Equal => {
                            panic!("Key already exists");
                        }
                        Ordering::Greater => (),
                    }
                }
            }
            if level < new_height {
                prevs[level] = current;
            }
            if level == 0 {
                break;
            }
            level -= 1;
        }

        let mut new_node = Box::new(Node {
            key,
            value,
            next: None,
            skips: vec![None; new_height],
        });

        for i in 0..new_height {
            unsafe {
                new_node.skips[i] = (*prevs[i]).skips[i];
                (*prevs[i]).skips[i] = Some(new_node.as_mut());
            }
        }

        unsafe {
            new_node.next = (*current).next.take();
            (*current).next = Some(new_node);
        }
    }

    /// Find the first node with the key >= given key
    fn seek_ge<'a>(&'a self, key: &[u8]) -> Option<&'a Node> {
        let mut current: *const Node = self.head.as_ref();
        let mut level = MAX_HEIGHT - 1;

        loop {
            unsafe {
                if let Some(next) = (*current).skips[level] {
                    match self.cmp.cmp(&(*next).key, key) {
                        Ordering::Less => {
                            current = next;
                            continue;
                        }
                        Ordering::Equal => return Some(&*next),
                        Ordering::Greater => {
                            if level == 0 {
                                return Some(&*next);
                            }
                        }
                    }
                }
            }
            if level == 0 {
                return None;
            }
            level -= 1;
        }
    }

    /// Find the last node with the key < given key
    fn seek_l<'a>(&'a self, key: &[u8]) -> Option<&'a Node> {
        let mut current: *const Node = self.head.as_ref();
        let mut level = MAX_HEIGHT - 1;

        loop {
            unsafe {
                if let Some(next) = (*current).skips[level] {
                    if self.cmp.cmp(&(*next).key, key) == Ordering::Less {
                        current = next;
                        continue;
                    }
                }
                if level == 0 {
                    if current == self.head.as_ref() {
                        return None;
                    } else {
                        return Some(&*current);
                    };
                }
            }
            level -= 1;
        }
    }
}

// Avoid stack overflow
impl Drop for InnerSkipList {
    fn drop(&mut self) {
        let mut node = self.head.next.take();
        while let Some(mut n) = node {
            node = n.next.take();
        }
    }
}

#[derive(Clone)]
pub struct SkipList(Rc<RefCell<InnerSkipList>>);

impl SkipList {
    pub fn new(cmp: Rc<dyn Cmp>) -> Self {
        SkipList(Rc::new(RefCell::new(InnerSkipList {
            head: Box::new(Node {
                key: Vec::new(),
                value: Vec::new(),
                next: None,
                skips: vec![None; MAX_HEIGHT],
            }),
            rand_rng: StdRng::seed_from_u64(0x00c0ffee),
            len: 0,
            approx_size: size_of::<Self>() + MAX_HEIGHT * size_of::<Option<*mut Node>>(),
            cmp,
        })))
    }

    pub fn len(&self) -> usize {
        self.0.borrow().len
    }

    pub fn approx_size(&self) -> usize {
        self.0.borrow().approx_size
    }

    /// Whether a key starts with the given prefix exists
    pub fn contains(&self, key: &[u8]) -> bool {
        self.0.borrow().contains(key)
    }

    pub fn insert(&mut self, key: Vec<u8>, value: Vec<u8>) {
        assert!(!key.is_empty(), "Key cannot be empty");
        self.0.borrow_mut().insert(key, value)
    }

    pub fn iter(&self) -> SkipListIter {
        SkipListIter {
            list: self.clone(),
            current: self.0.borrow().head.as_ref(),
        }
    }
}

pub struct SkipListIter {
    list: SkipList,
    current: *const Node,
}

impl DbIterator for SkipListIter {
    fn advance(&mut self) -> bool {
        if let Some(next) = unsafe { (*self.current).next.as_ref() } {
            self.current = next.as_ref();
            return true;
        }
        self.reset();
        false
    }

    fn current(&self, key: &mut Vec<u8>, value: &mut Vec<u8>) -> bool {
        if !self.valid() {
            return false;
        }
        unsafe {
            key.clone_from(&(*self.current).key);
            value.clone_from(&(*self.current).value);
        }
        true
    }

    /// Inefficiently implemented with `seek_l`
    fn prev(&mut self) -> bool {
        if self.valid() {
            if let Some(prev) = self.list.0.borrow().seek_l(unsafe { &(*self.current).key }) {
                self.current = prev;
                return true;
            }
        }
        self.reset();
        false
    }

    fn reset(&mut self) {
        self.current = self.list.0.borrow().head.as_ref();
    }

    /// Find the first node with the key >= given key
    fn seek(&mut self, key: &[u8]) {
        if let Some(node) = self.list.0.borrow().seek_ge(key) {
            self.current = node;
            return;
        }
        self.reset();
    }

    fn valid(&self) -> bool {
        self.current != self.list.0.borrow().head.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests_leveldb_rs {
        use crate::{
            coredef::{
                cmp::{DefaultCmp, MemtableKeyCmp},
                types::DbIteratorWrapper,
            },
            utils::test_iterator_properties,
        };

        use super::*;

        pub fn make_skiplist() -> SkipList {
            let mut skm = SkipList::new(Rc::new(DefaultCmp));
            let keys = vec![
                "aba", "abb", "abc", "abd", "abe", "abf", "abg", "abh", "abi", "abj", "abk", "abl",
                "abm", "abn", "abo", "abp", "abq", "abr", "abs", "abt", "abu", "abv", "abw", "abx",
                "aby", "abz",
            ];

            for k in keys {
                skm.insert(k.as_bytes().to_vec(), "def".as_bytes().to_vec());
            }
            skm
        }

        #[test]
        fn test_insert() {
            let skm = make_skiplist();
            assert_eq!(skm.len(), 26);
        }

        #[test]
        #[should_panic]
        fn test_no_dupes() {
            let mut skm = make_skiplist();
            // this should panic
            skm.insert("abc".as_bytes().to_vec(), "def".as_bytes().to_vec());
            skm.insert("abf".as_bytes().to_vec(), "def".as_bytes().to_vec());
        }

        #[test]
        fn test_contains() {
            let skm = make_skiplist();
            assert!(skm.contains(&"aby".as_bytes().to_vec()));
            assert!(skm.contains(&"abc".as_bytes().to_vec()));
            assert!(skm.contains(&"abz".as_bytes().to_vec()));
            assert!(!skm.contains(&"ab{".as_bytes().to_vec()));
            assert!(!skm.contains(&"123".as_bytes().to_vec()));
            assert!(!skm.contains(&"aaa".as_bytes().to_vec()));
            assert!(!skm.contains(&"456".as_bytes().to_vec()));
        }

        #[test]
        fn test_find() {
            let skm = make_skiplist();
            assert_eq!(
                skm.0
                    .borrow()
                    .seek_ge(&"abf".as_bytes().to_vec())
                    .unwrap()
                    .key,
                "abf".as_bytes().to_vec()
            );
            assert!(skm.0.borrow().seek_ge(&"ab{".as_bytes().to_vec()).is_none());
            assert_eq!(
                skm.0
                    .borrow()
                    .seek_ge(&"aaa".as_bytes().to_vec())
                    .unwrap()
                    .key,
                "aba".as_bytes().to_vec()
            );
            assert_eq!(
                skm.0
                    .borrow()
                    .seek_ge(&"ab".as_bytes())
                    .unwrap()
                    .key
                    .as_slice(),
                "aba".as_bytes()
            );
            assert_eq!(
                skm.0
                    .borrow()
                    .seek_ge(&"abc".as_bytes())
                    .unwrap()
                    .key
                    .as_slice(),
                "abc".as_bytes()
            );
            assert!(skm.0.borrow().seek_l(&"ab0".as_bytes()).is_none());
            assert_eq!(
                skm.0
                    .borrow()
                    .seek_l(&"abd".as_bytes())
                    .unwrap()
                    .key
                    .as_slice(),
                "abc".as_bytes()
            );
            assert_eq!(
                skm.0
                    .borrow()
                    .seek_l(&"ab{".as_bytes())
                    .unwrap()
                    .key
                    .as_slice(),
                "abz".as_bytes()
            );
        }

        #[test]
        fn test_empty_skiplist_find_memtable_cmp() {
            // Regression test: Make sure comparator isn't called with empty key.
            let skm = SkipList::new(Rc::new(MemtableKeyCmp(Rc::new(DefaultCmp))));

            let mut it = skm.iter();
            it.seek("abc".as_bytes());
            assert!(!it.valid());
        }

        #[test]
        fn test_skiplist_iterator_0() {
            let skm = SkipList::new(Rc::new(DefaultCmp));
            let mut i = 0;

            for (_, _) in DbIteratorWrapper::new(&mut skm.iter()) {
                i += 1;
            }

            assert_eq!(i, 0);
            assert!(!skm.iter().valid());
        }

        #[test]
        fn test_skiplist_iterator_init() {
            let skm = make_skiplist();
            let mut iter = skm.iter();

            assert!(!iter.valid());
            iter.next();
            assert!(iter.valid());
            iter.reset();
            assert!(!iter.valid());

            iter.next();
            assert!(iter.valid());
            iter.prev();
            assert!(!iter.valid());
        }

        #[test]
        fn test_skiplist_iterator() {
            let skm = make_skiplist();
            let mut i = 0;

            for (k, v) in DbIteratorWrapper::new(&mut skm.iter()) {
                assert!(!k.is_empty());
                assert!(!v.is_empty());
                i += 1;
            }
            assert_eq!(i, 26);
        }

        #[test]
        fn test_skiplist_iterator_seek_valid() {
            let skm = make_skiplist();
            let mut iter = skm.iter();

            iter.next();
            assert!(iter.valid());
            assert_eq!(iter.current_kv().unwrap().0, "aba".as_bytes().to_vec());
            iter.seek(&"abz".as_bytes().to_vec());
            assert_eq!(
                iter.current_kv().unwrap(),
                ("abz".as_bytes().to_vec(), "def".as_bytes().to_vec())
            );
            // go back to beginning
            iter.seek(&"aba".as_bytes().to_vec());
            assert_eq!(
                iter.current_kv().unwrap(),
                ("aba".as_bytes().to_vec(), "def".as_bytes().to_vec())
            );

            iter.seek(&"".as_bytes().to_vec());
            assert!(iter.valid());
            iter.prev();
            assert!(!iter.valid());

            while iter.advance() {}
            assert!(!iter.valid());
            assert!(!iter.prev());
            assert_eq!(iter.current_kv(), None);
        }

        #[test]
        fn test_skiplist_behavior() {
            let mut skm = SkipList::new(Rc::new(DefaultCmp));
            let keys = vec!["aba", "abb", "abc", "abd"];
            for k in keys {
                skm.insert(k.as_bytes().to_vec(), "def".as_bytes().to_vec());
            }
            test_iterator_properties(skm.iter());
        }

        #[test]
        fn test_skiplist_iterator_prev() {
            let skm = make_skiplist();
            let mut iter = skm.iter();

            iter.next();
            assert!(iter.valid());
            iter.prev();
            assert!(!iter.valid());
            iter.seek(&"abc".as_bytes());
            iter.prev();
            assert_eq!(
                iter.current_kv().unwrap(),
                ("abb".as_bytes().to_vec(), "def".as_bytes().to_vec())
            );
        }

        #[test]
        fn test_skiplist_iterator_concurrent_insert() {
            // time_test!();
            // Asserts that the list can be mutated while an iterator exists; this is intentional.
            let mut skm = make_skiplist();
            let mut iter = skm.iter();

            assert!(iter.advance());
            skm.insert("abccc".as_bytes().to_vec(), "defff".as_bytes().to_vec());
            // Assert that value inserted after obtaining iterator is present.
            for (k, _) in DbIteratorWrapper::new(&mut iter) {
                if k == "abccc".as_bytes() {
                    return;
                }
            }
            panic!("abccc not found in list.");
        }
    }

    mod tests_gpt_4o {
        use super::*;
        use crate::coredef::cmp::Cmp;
        use std::rc::Rc;

        struct TestComparator;

        impl Cmp for TestComparator {
            fn cmp(&self, a: &[u8], b: &[u8]) -> Ordering {
                a.cmp(b)
            }

            fn find_shortest_separator(&self, _a: &[u8], _b: &[u8]) -> Vec<u8> {
                unimplemented!()
            }

            fn find_shortest_successor(&self, _a: &[u8]) -> Vec<u8> {
                unimplemented!()
            }

            fn name(&self) -> &'static str {
                unimplemented!()
            }
        }

        fn new_skiplist() -> SkipList {
            SkipList::new(Rc::new(TestComparator))
        }

        #[test]
        fn test_new_skiplist() {
            let skiplist = new_skiplist();
            assert_eq!(skiplist.len(), 0);
            assert_eq!(
                skiplist.approx_size(),
                size_of::<SkipList>() + MAX_HEIGHT * size_of::<Option<*mut Node>>()
            );
        }

        #[test]
        fn test_insert_and_len() {
            let mut skiplist = new_skiplist();
            skiplist.insert(vec![1], vec![10]);
            assert_eq!(skiplist.len(), 1);
            skiplist.insert(vec![2], vec![20]);
            assert_eq!(skiplist.len(), 2);
        }

        #[test]
        fn test_insert_and_contains() {
            let mut skiplist = new_skiplist();
            skiplist.insert(vec![1], vec![10]);
            assert!(skiplist.contains(&[1]));
            assert!(!skiplist.contains(&[2]));
        }

        #[test]
        #[should_panic(expected = "Key cannot be empty")]
        fn test_insert_empty_key() {
            let mut skiplist = new_skiplist();
            skiplist.insert(vec![], vec![10]);
        }

        #[test]
        #[should_panic(expected = "Key already exists")]
        fn test_insert_duplicate_key() {
            let mut skiplist = new_skiplist();
            skiplist.insert(vec![1], vec![10]);
            skiplist.insert(vec![1], vec![20]);
        }

        #[test]
        fn test_contains_nonexistent_key() {
            let skiplist = new_skiplist();
            assert!(!skiplist.contains(&[1]));
        }

        #[test]
        fn test_approx_size() {
            let mut skiplist = new_skiplist();
            let initial_size = skiplist.approx_size();
            skiplist.insert(vec![1], vec![10]);
            assert!(skiplist.approx_size() > initial_size);
        }

        #[test]
        fn test_iterator_basic() {
            let mut skiplist = new_skiplist();
            skiplist.insert(vec![1], vec![10]);
            skiplist.insert(vec![2], vec![20]);

            let mut iter = skiplist.iter();
            let mut key = Vec::new();
            let mut value = Vec::new();

            assert!(iter.advance());
            iter.current(&mut key, &mut value);
            assert_eq!(key, vec![1]);
            assert_eq!(value, vec![10]);

            assert!(iter.advance());
            iter.current(&mut key, &mut value);
            assert_eq!(key, vec![2]);
            assert_eq!(value, vec![20]);

            assert!(!iter.advance());
        }

        #[test]
        fn test_iterator_seek() {
            let mut skiplist = new_skiplist();
            skiplist.insert(vec![1], vec![10]);
            skiplist.insert(vec![2], vec![20]);
            skiplist.insert(vec![3], vec![30]);

            let mut iter = skiplist.iter();
            let mut key = Vec::new();
            let mut value = Vec::new();

            iter.seek(&[2]);
            iter.current(&mut key, &mut value);
            assert_eq!(key, vec![2]);
            assert_eq!(value, vec![20]);

            iter.seek(&[3]);
            iter.current(&mut key, &mut value);
            assert_eq!(key, vec![3]);
            assert_eq!(value, vec![30]);
        }

        #[test]
        fn test_iterator_prev() {
            let mut skiplist = new_skiplist();
            skiplist.insert(vec![1], vec![10]);
            skiplist.insert(vec![2], vec![20]);
            skiplist.insert(vec![3], vec![30]);

            let mut iter = skiplist.iter();
            iter.seek(&[3]);
            assert!(iter.prev());

            let mut key = Vec::new();
            let mut value = Vec::new();
            iter.current(&mut key, &mut value);
            assert_eq!(key, vec![2]);
            assert_eq!(value, vec![20]);
        }

        #[test]
        fn test_iterator_reset() {
            let mut skiplist = new_skiplist();
            skiplist.insert(vec![1], vec![10]);
            skiplist.insert(vec![2], vec![20]);

            let mut iter = skiplist.iter();
            iter.seek(&[2]);

            iter.reset();
            assert!(!iter.valid());
            let mut key = Vec::new();
            let mut value = Vec::new();
            iter.current(&mut key, &mut value);
            assert_eq!(key, vec![]);
            assert_eq!(value, vec![]);
        }

        #[test]
        fn test_iterator_valid() {
            let mut skiplist = new_skiplist();
            skiplist.insert(vec![1], vec![10]);
            skiplist.insert(vec![2], vec![20]);

            let mut iter = skiplist.iter();
            assert!(!iter.valid());

            iter.advance();
            assert!(iter.valid());
        }
    }

    mod tests_gemini_1_5_flash {
        use crate::coredef::cmp::DefaultCmp;

        use super::*;

        #[test]
        fn test_skiplist_basic() {
            let mut skiplist = SkipList::new(Rc::new(DefaultCmp));
            assert_eq!(skiplist.len(), 0);

            skiplist.insert(vec![1, 2, 3], vec![4, 5, 6]);
            assert_eq!(skiplist.len(), 1);

            assert!(skiplist.contains(&[1, 2, 3]));
            assert!(skiplist.contains(&[1, 2]));

            let mut iter = skiplist.iter();
            iter.advance();
            assert!(iter.valid());
            let mut key = vec![];
            let mut value = vec![];
            assert!(iter.current(&mut key, &mut value));
            assert_eq!(key, vec![1, 2, 3]);
            assert_eq!(value, vec![4, 5, 6]);
            assert!(!iter.advance());
        }

        #[test]
        #[should_panic(expected = "Key already exists")]
        fn test_skiplist_insert_duplicates() {
            let mut skiplist = SkipList::new(Rc::new(DefaultCmp));
            skiplist.insert(vec![1, 2, 3], vec![4, 5, 6]);
            assert_eq!(skiplist.len(), 1);

            // Inserting a duplicate key should panic
            skiplist.insert(vec![1, 2, 3], vec![7, 8, 9]);
        }

        #[test]
        fn test_skiplist_iter() {
            let mut skiplist = SkipList::new(Rc::new(DefaultCmp));
            skiplist.insert(vec![1, 2, 3], vec![4, 5, 6]);
            skiplist.insert(vec![7, 8, 9], vec![10, 11, 12]);
            skiplist.insert(vec![4, 5, 6], vec![13, 14, 15]);

            let mut iter = skiplist.iter();
            iter.advance();
            let mut key = vec![];
            let mut value = vec![];

            assert!(iter.valid());
            assert!(iter.current(&mut key, &mut value));
            assert_eq!(key, vec![1, 2, 3]);
            assert_eq!(value, vec![4, 5, 6]);

            assert!(iter.advance());
            assert!(iter.current(&mut key, &mut value));
            assert_eq!(key, vec![4, 5, 6]);
            assert_eq!(value, vec![13, 14, 15]);

            assert!(iter.advance());
            assert!(iter.current(&mut key, &mut value));
            assert_eq!(key, vec![7, 8, 9]);
            assert_eq!(value, vec![10, 11, 12]);

            assert!(!iter.advance());
            assert!(!iter.valid());
        }

        // #[test]
        // fn test_skiplist_iter_prev() {
        //     let mut skiplist = SkipList::new(Rc::new(DefaultCmp));
        //     skiplist.insert(vec![1, 2, 3], vec![4, 5, 6]);
        //     skiplist.insert(vec![7, 8, 9], vec![10, 11, 12]);
        //     skiplist.insert(vec![4, 5, 6], vec![13, 14, 15]);

        //     let mut iter = skiplist.iter();

        //     // Move to the last element
        //     while iter.advance() {}

        //     let mut key = vec![];
        //     let mut value = vec![];

        //     assert!(iter.valid());
        //     assert!(iter.current(&mut key, &mut value));
        //     assert_eq!(key, vec![7, 8, 9]);
        //     assert_eq!(value, vec![10, 11, 12]);

        //     assert!(iter.prev());
        //     assert!(iter.current(&mut key, &mut value));
        //     assert_eq!(key, vec![4, 5, 6]);
        //     assert_eq!(value, vec![13, 14, 15]);

        //     assert!(iter.prev());
        //     assert!(iter.current(&mut key, &mut value));
        //     assert_eq!(key, vec![1, 2, 3]);
        //     assert_eq!(value, vec![4, 5, 6]);

        //     assert!(!iter.prev());
        //     assert!(!iter.valid());
        // }

        #[test]
        fn test_skiplist_iter_seek() {
            let mut skiplist = SkipList::new(Rc::new(DefaultCmp));
            skiplist.insert(vec![1, 2, 3], vec![4, 5, 6]);
            skiplist.insert(vec![7, 8, 9], vec![10, 11, 12]);
            skiplist.insert(vec![4, 5, 6], vec![13, 14, 15]);

            let mut iter = skiplist.iter();

            iter.seek(&[4, 5]);
            let mut key = vec![];
            let mut value = vec![];
            assert!(iter.current(&mut key, &mut value));
            assert_eq!(key, vec![4, 5, 6]);
            assert_eq!(value, vec![13, 14, 15]);

            iter.seek(&[7, 8]);
            assert!(iter.current(&mut key, &mut value));
            assert_eq!(key, vec![7, 8, 9]);
            assert_eq!(value, vec![10, 11, 12]);

            iter.seek(&[100]);
            assert!(!iter.valid());
        }
    }
}
