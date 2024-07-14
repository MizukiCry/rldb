use crate::coredef::{
    cmp::{Cmp, InternalKeyCmp},
    error::Result,
    key::{parse_internal_key, InternalKey, LookupKey, UserKey, ValueType},
    types::{DbIterator, FileMetaData, MAX_SEQNUM},
    NUM_LEVELS,
};
use crate::storage::table::TableCache;
use std::{cell::RefCell, cmp::Ordering, rc::Rc};

use super::table::TableIterator;

pub type FileMetaHandle = Rc<RefCell<FileMetaData>>;

/// Contains statistics about seeks occurred in a file.
pub struct GetStats {
    file: Option<FileMetaHandle>,
    level: usize,
}

pub struct Version {
    cache: Rc<RefCell<TableCache>>,
    cmp: Rc<dyn Cmp>,
    pub files: [Vec<FileMetaHandle>; NUM_LEVELS],
    pub file_to_compact: Option<FileMetaHandle>,
    pub file_to_compact_level: usize,
    pub compaction_score: Option<f64>,
    pub compaction_level: Option<usize>,
}

impl Version {
    pub fn new(cache: Rc<RefCell<TableCache>>, cmp: Rc<dyn Cmp>) -> Self {
        Self {
            cache,
            cmp,
            files: Default::default(),
            file_to_compact: None,
            file_to_compact_level: 0,
            compaction_score: None,
            compaction_level: None,
        }
    }

    pub fn num_level_bytes(&self, level: usize) -> usize {
        self.files[level].iter().map(|f| f.borrow().size).sum()
    }

    pub fn num_level_files(&self, level: usize) -> usize {
        self.files[level].len()
    }

    pub fn get(&self, key: InternalKey) -> Result<Option<(Vec<u8>, GetStats)>> {
        let levels = self.get_overlapping(key);
        let user_key = parse_internal_key(key).2;

        let mut stats = GetStats {
            file: None,
            level: 0,
        };

        for (level, files) in levels.iter().enumerate() {
            for file in files {
                if let Ok(Some((k, v))) = self.cache.borrow_mut().get(file.borrow().id, key) {
                    let (t, _, k) = parse_internal_key(&k);
                    if t == ValueType::TypeValue && self.cmp.cmp(k, user_key) == Ordering::Equal {
                        return Ok(Some((v, stats)));
                    } else if t == ValueType::TypeDeletion {
                        return Ok(None);
                    }
                }

                // todo
                stats = GetStats {
                    file: Some(file.clone()),
                    level,
                };
            }
        }

        Ok(None)
    }

    /// Returns files that overlap with the given key.
    fn get_overlapping(&self, key: InternalKey) -> [Vec<FileMetaHandle>; NUM_LEVELS] {
        let mut levels: [Vec<FileMetaHandle>; NUM_LEVELS] = Default::default();
        let user_key = parse_internal_key(key).2;

        levels[0].reserve(self.files[0].len());
        for file in self.files[0].iter() {
            let inner = file.borrow();
            let smallest = parse_internal_key(&inner.smallest).2;
            let largest = parse_internal_key(&inner.largest).2;
            if self.cmp.cmp(user_key, smallest) != Ordering::Less
                && self.cmp.cmp(user_key, largest) != Ordering::Greater
            {
                levels[0].push(file.clone());
            }
        }
        levels[0].sort_by(|a, b| b.borrow().id.cmp(&a.borrow().id));

        let internal_cmp = InternalKeyCmp(self.cmp.clone());
        for (level, files) in self.files.iter().enumerate().skip(1) {
            if let Some(i) = find_file(&internal_cmp, files, key) {
                if self
                    .cmp
                    .cmp(key, parse_internal_key(&files[i].borrow().smallest).2)
                    != Ordering::Less
                {
                    levels[level].push(files[i].clone());
                }
            }
        }

        levels
    }

    /// Returns true if a compaction should be triggered.
    pub fn update_stats(&mut self, stats: GetStats) -> bool {
        if let Some(file) = stats.file {
            if file.borrow().allowed_seeks <= 1 && self.file_to_compact.is_none() {
                self.file_to_compact = Some(file);
                self.file_to_compact_level = stats.level;
                return true;
            } else if file.borrow().allowed_seeks > 0 {
                file.borrow_mut().allowed_seeks -= 1;
            }
        }
        false
    }

    /// Returns true if the given range overlaps with any of the files in the given level.
    pub fn overlaps_in_level(&self, level: usize, smallest: UserKey, largest: UserKey) -> bool {
        assert!(level < NUM_LEVELS);
        let cmp = InternalKeyCmp(self.cmp.clone());
        if level == 0 {
            overlaps_range_disjoint(&cmp, &self.files[level], smallest, largest)
        } else {
            overlaps_range(&cmp, &self.files[level], smallest, largest)
        }
    }

    pub fn pick_memtable_output_level(&self, min: UserKey, max: UserKey) -> usize {
        let mut level = 0;
        if !self.overlaps_in_level(0, min, max) {
            let smallest = LookupKey::new(min, MAX_SEQNUM);
            let largest = LookupKey::new_with_type(max, 0, ValueType::TypeDeletion);

            const MAX_COMPACT_LEVEL: usize = 2;
            while level < MAX_COMPACT_LEVEL {
                if self.overlaps_in_level(level + 1, min, max) {
                    break;
                }
                if level + 2 < NUM_LEVELS {
                    let size = self
                        .overlapping_inputs(
                            level + 2,
                            smallest.internal_key(),
                            largest.internal_key(),
                        )
                        .iter()
                        .map(|f| f.borrow().size)
                        .sum::<usize>();
                    if size > 10 * 1024 * 1024 {
                        break;
                    }
                }
                level += 1;
            }
        }
        level
    }

    /// Returns files that overlap with the given range.
    pub fn overlapping_inputs(
        &self,
        level: usize,
        begin: InternalKey,
        end: InternalKey,
    ) -> Vec<FileMetaHandle> {
        assert!(level < NUM_LEVELS);

        let mut begin = parse_internal_key(begin).2.to_vec();
        let mut end = parse_internal_key(end).2.to_vec();

        'outer: loop {
            let mut inputs = Vec::new();
            for file in self.files[level].iter() {
                let f = file.borrow();
                let smallest = parse_internal_key(&f.smallest).2;
                let largest = parse_internal_key(&f.largest).2;
                if !begin.is_empty() && self.cmp.cmp(largest, &begin) == Ordering::Less {
                    continue;
                }
                if !end.is_empty() && self.cmp.cmp(smallest, &end) == Ordering::Greater {
                    continue;
                }
                inputs.push(file.clone());
                if level == 0 {
                    if !begin.is_empty() && self.cmp.cmp(smallest, &begin) == Ordering::Less {
                        begin = smallest.to_vec();
                        continue 'outer;
                    }
                    if !end.is_empty() && self.cmp.cmp(largest, &end) == Ordering::Greater {
                        end = largest.to_vec();
                        continue 'outer;
                    }
                }
            }
            return inputs;
        }
    }

    /// Returns true if there is a new file to be compacted.
    pub fn record_read_sample(&mut self, key: InternalKey) -> bool {
        let mut first_file = GetStats {
            file: None,
            level: 0,
        };
        let mut count = 0;

        for (level, files) in self.get_overlapping(key).iter().enumerate() {
            if !files.is_empty() && first_file.file.is_none() {
                first_file = GetStats {
                    file: Some(files[0].clone()),
                    level,
                };
            }
            count += files.len();
        }

        if count > 1 {
            self.update_stats(first_file)
        } else {
            false
        }
    }

    /// Returns an iterator that concatenates the files in the given level > 0.
    fn new_level_iter(&self, level: usize) -> VersionIterator {
        assert!(level > 0 && level < NUM_LEVELS);
        VersionIterator::new(
            self.files[level].clone(),
            self.cache.clone(),
            self.cmp.clone(),
        )
    }

    /// Returns iterators that iterate over all files in the version.
    pub fn new_iters(&self) -> Result<Vec<Box<dyn DbIterator>>> {
        let mut iters: Vec<Box<dyn DbIterator>> = Vec::new();
        for file in self.files[0].iter() {
            iters.push(Box::new(
                self.cache.borrow_mut().get_table(file.borrow().id)?.iter(),
            ));
        }

        for level in 1..NUM_LEVELS {
            if !self.files[level].is_empty() {
                iters.push(Box::new(self.new_level_iter(level)));
            }
        }

        Ok(iters)
    }

    // #[cfg(test)]
    // pub fn summary(&self) -> String {
    //     let mut res = String::with_capacity(256);
    //     for (level, files) in self.files.iter().enumerate() {
    //         if files.is_empty() {
    //             continue;
    //         }
    //         res.push_str(&format!(
    //             "level {level}: {} files, {} bytes ({:?}); ",
    //             files.len(),
    //             files.iter().map(|f| f.borrow().size).sum::<usize>(),
    //             files
    //                 .iter()
    //                 .map(|f| (f.borrow().id, f.borrow().size))
    //                 .collect::<Vec<_>>()
    //         ));
    //     }
    //     res
    // }

    // #[cfg(test)]
    // fn max_next_level_overlapping_bytes(&self) -> usize {
    //     let mut max = 0;
    //     for level in 1..NUM_LEVELS - 1 {
    //         for file in self.files[level].iter() {
    //             let f = file.borrow();
    //             let sum = self
    //                 .overlapping_inputs(level + 1, &f.smallest, &f.largest)
    //                 .iter()
    //                 .map(|f| f.borrow().size)
    //                 .sum::<usize>();
    //             if sum > max {
    //                 max = sum;
    //             }
    //         }
    //     }
    //     max
    // }
}

/// Returns the index of the first file in `files` that contains the given key.
/// Binary search is used to find the file.
fn find_file(cmp: &InternalKeyCmp, files: &[FileMetaHandle], key: InternalKey) -> Option<usize> {
    let mut left = 0;
    let mut right = files.len();
    while left < right {
        let mid = (left + right) / 2;
        if cmp.cmp(&files[mid].borrow().largest, key) == Ordering::Less {
            left = mid + 1;
        } else {
            right = mid;
        }
    }

    if right != files.len() {
        Some(right)
    } else {
        None
    }
}

fn key_is_before_file(cmp: &InternalKeyCmp, key: UserKey, f: &FileMetaHandle) -> bool {
    !key.is_empty() && cmp.0.cmp(key, parse_internal_key(&f.borrow().smallest).2) == Ordering::Less
}

fn key_is_after_file(cmp: &InternalKeyCmp, key: UserKey, f: &FileMetaHandle) -> bool {
    !key.is_empty()
        && cmp.0.cmp(key, parse_internal_key(&f.borrow().largest).2) == Ordering::Greater
}

// Returns if the given range [smallest, largest] overlaps with any of the files.
fn overlaps_range(
    cmp: &InternalKeyCmp,
    files: &[FileMetaHandle],
    smallest: UserKey,
    largest: UserKey,
) -> bool {
    for f in files {
        if !key_is_after_file(cmp, smallest, f) && !key_is_before_file(cmp, largest, f) {
            return true;
        }
    }
    false
}

/// Like `overlaps_range`, but given files are disjoint.
fn overlaps_range_disjoint(
    cmp: &InternalKeyCmp,
    files: &[FileMetaHandle],
    smallest: UserKey,
    largest: UserKey,
) -> bool {
    let key = LookupKey::new(smallest, MAX_SEQNUM);
    find_file(cmp, files, key.internal_key())
        .is_some_and(|i| !key_is_before_file(cmp, largest, &files[i]))
}

pub struct VersionIterator {
    files: Vec<FileMetaHandle>,
    cache: Rc<RefCell<TableCache>>,
    cmp: InternalKeyCmp,
    current: Option<TableIterator>,
    current_index: usize,
}

impl VersionIterator {
    pub fn new(
        files: Vec<FileMetaHandle>,
        cache: Rc<RefCell<TableCache>>,
        user_cmp: Rc<dyn Cmp>,
    ) -> Self {
        assert!(!files.is_empty());
        Self {
            files,
            cache,
            cmp: InternalKeyCmp(user_cmp),
            current: None,
            current_index: 0,
        }
    }
}

impl DbIterator for VersionIterator {
    fn advance(&mut self) -> bool {
        if let Some(i) = self.current.as_mut() {
            if i.advance() {
                return true;
            }
            if self.current_index + 1 == self.files.len() {
                return false;
            }
            self.current_index += 1;
        }

        if let Ok(table) = self
            .cache
            .borrow_mut()
            .get_table(self.files[self.current_index].borrow().id)
        {
            self.current = Some(table.iter());
        } else {
            return false;
        }

        self.advance()
    }

    fn current(&self, key: &mut Vec<u8>, value: &mut Vec<u8>) -> bool {
        if let Some(i) = self.current.as_ref() {
            i.current(key, value)
        } else {
            false
        }
    }

    fn seek(&mut self, key: &[u8]) {
        if let Some(i) = find_file(&self.cmp, &self.files, key) {
            if let Ok(table) = self.cache.borrow_mut().get_table(self.files[i].borrow().id) {
                let mut iter = table.iter();
                iter.seek(key);
                if iter.valid() {
                    self.current = Some(iter);
                    self.current_index = i;
                    return;
                }
            }
        }
        self.reset();
    }

    fn reset(&mut self) {
        self.current = None;
        self.current_index = 0;
    }

    fn valid(&self) -> bool {
        self.current.as_ref().is_some_and(|i| i.valid())
    }

    fn prev(&mut self) -> bool {
        if let Some(i) = self.current.as_mut() {
            if i.prev() {
                return true;
            }
            if self.current_index > 0 {
                let file = &self.files[self.current_index - 1];
                if let Ok(table) = self.cache.borrow_mut().get_table(file.borrow().id) {
                    let mut iter = table.iter();
                    iter.seek(&file.borrow().largest);
                    assert!(iter.valid());
                    self.current = Some(iter);
                    self.current_index -= 1;
                    return true;
                }
            }
        }
        self.reset();
        false
    }
}

#[cfg(test)]
pub mod testutil {
    use crate::{
        coredef::{cmp::DefaultCmp, env::Env, options::Options, types::FileID},
        storage::table::{TableBuilder, TableCache},
    };

    use super::*;
    use std::path::Path;

    pub fn new_file(
        id: u64,
        smallest: &[u8],
        smallestix: u64,
        largest: &[u8],
        largestix: u64,
    ) -> FileMetaHandle {
        Rc::new(RefCell::new(FileMetaData {
            allowed_seeks: 10,
            size: 163840,
            id,
            smallest: LookupKey::new(smallest, smallestix).internal_key().to_vec(),
            largest: LookupKey::new(largest, largestix).internal_key().to_vec(),
        }))
    }

    /// write_table creates a table with the given number and contents (must be sorted!) in the
    /// memenv. The sequence numbers given to keys start with startseq.
    pub fn write_table(
        me: &Rc<dyn Env>,
        contents: &[(&[u8], &[u8], ValueType)],
        startseq: u64,
        num: FileID,
    ) -> FileMetaHandle {
        let dst = me
            .open_writable_file(Path::new(&TableCache::table_file_name("db", num)))
            .unwrap();
        let mut seq = startseq;
        let keys: Vec<Vec<u8>> = contents
            .iter()
            .map(|&(k, _, typ)| {
                seq += 1;
                LookupKey::new_with_type(k, seq - 1, typ)
                    .internal_key()
                    .to_vec()
            })
            .collect();

        let mut tbl = TableBuilder::new(Options::for_test(), dst);
        for i in 0..contents.len() {
            tbl.add(&keys[i], contents[i].1).unwrap();
            seq += 1;
        }

        let f = new_file(
            num,
            contents[0].0,
            startseq,
            contents[contents.len() - 1].0,
            startseq + (contents.len() - 1) as u64,
        );
        f.borrow_mut().size = tbl.build().unwrap();
        f
    }

    pub fn make_version() -> (Version, Options) {
        let opts = Options::for_test();
        let env = opts.env.clone();

        // The different levels overlap in a sophisticated manner to be able to test compactions
        // and so on.
        // The sequence numbers are in "natural order", i.e. highest levels have lowest sequence
        // numbers.

        // Level 0 (overlapping)
        let f2: &[(&[u8], &[u8], ValueType)] = &[
            ("aac".as_bytes(), "val1".as_bytes(), ValueType::TypeDeletion),
            ("aax".as_bytes(), "val2".as_bytes(), ValueType::TypeValue),
            ("aba".as_bytes(), "val3".as_bytes(), ValueType::TypeValue),
            ("bab".as_bytes(), "val4".as_bytes(), ValueType::TypeValue),
            ("bba".as_bytes(), "val5".as_bytes(), ValueType::TypeValue),
        ];
        let t2 = write_table(&env, f2, 26, 2);
        let f1: &[(&[u8], &[u8], ValueType)] = &[
            ("aaa".as_bytes(), "val1".as_bytes(), ValueType::TypeValue),
            ("aab".as_bytes(), "val2".as_bytes(), ValueType::TypeValue),
            ("aac".as_bytes(), "val3".as_bytes(), ValueType::TypeValue),
            ("aba".as_bytes(), "val4".as_bytes(), ValueType::TypeValue),
        ];
        let t1 = write_table(&env, f1, 22, 1);
        // Level 1
        let f3: &[(&[u8], &[u8], ValueType)] = &[
            ("aaa".as_bytes(), "val0".as_bytes(), ValueType::TypeValue),
            ("cab".as_bytes(), "val2".as_bytes(), ValueType::TypeValue),
            ("cba".as_bytes(), "val3".as_bytes(), ValueType::TypeValue),
        ];
        let t3 = write_table(&env, f3, 19, 3);
        let f4: &[(&[u8], &[u8], ValueType)] = &[
            ("daa".as_bytes(), "val1".as_bytes(), ValueType::TypeValue),
            ("dab".as_bytes(), "val2".as_bytes(), ValueType::TypeValue),
            ("dba".as_bytes(), "val3".as_bytes(), ValueType::TypeValue),
        ];
        let t4 = write_table(&env, f4, 16, 4);
        let f5: &[(&[u8], &[u8], ValueType)] = &[
            ("eaa".as_bytes(), "val1".as_bytes(), ValueType::TypeValue),
            ("eab".as_bytes(), "val2".as_bytes(), ValueType::TypeValue),
            ("fab".as_bytes(), "val3".as_bytes(), ValueType::TypeValue),
        ];
        let t5 = write_table(&env, f5, 13, 5);
        // Level 2
        let f6: &[(&[u8], &[u8], ValueType)] = &[
            ("cab".as_bytes(), "val1".as_bytes(), ValueType::TypeValue),
            ("fab".as_bytes(), "val2".as_bytes(), ValueType::TypeValue),
            ("fba".as_bytes(), "val3".as_bytes(), ValueType::TypeValue),
        ];
        let t6 = write_table(&env, f6, 10, 6);
        let f7: &[(&[u8], &[u8], ValueType)] = &[
            ("gaa".as_bytes(), "val1".as_bytes(), ValueType::TypeValue),
            ("gab".as_bytes(), "val2".as_bytes(), ValueType::TypeValue),
            ("gba".as_bytes(), "val3".as_bytes(), ValueType::TypeValue),
            ("gca".as_bytes(), "val4".as_bytes(), ValueType::TypeDeletion),
            ("gda".as_bytes(), "val5".as_bytes(), ValueType::TypeValue),
        ];
        let t7 = write_table(&env, f7, 5, 7);
        // Level 3 (2 * 2 entries, for iterator behavior).
        let f8: &[(&[u8], &[u8], ValueType)] = &[
            ("haa".as_bytes(), "val1".as_bytes(), ValueType::TypeValue),
            ("hba".as_bytes(), "val2".as_bytes(), ValueType::TypeValue),
        ];
        let t8 = write_table(&env, f8, 3, 8);
        let f9: &[(&[u8], &[u8], ValueType)] = &[
            ("iaa".as_bytes(), "val1".as_bytes(), ValueType::TypeValue),
            ("iba".as_bytes(), "val2".as_bytes(), ValueType::TypeValue),
        ];
        let t9 = write_table(&env, f9, 1, 9);

        let cache = TableCache::new("db", opts.clone(), 100);
        let mut v = Version::new(Rc::new(RefCell::new(cache)), Rc::new(DefaultCmp));
        v.files[0] = vec![t1, t2];
        v.files[1] = vec![t3, t4, t5];
        v.files[2] = vec![t6, t7];
        v.files[3] = vec![t8, t9];
        (v, opts)
    }
}

#[cfg(test)]
mod tests {
    use crate::coredef::cmp::DefaultCmp;
    use crate::coredef::options::Options;
    use crate::coredef::types::{DbIteratorWrapper, MergingIterator};
    use crate::utils::test_iterator_properties;

    use super::testutil::*;
    use super::*;

    use time_test::time_test;

    #[test]
    fn test_version_concat_iter() {
        let v = make_version().0;

        let expected_entries = vec![0, 9, 8, 4];
        for l in 1..4 {
            let mut iter = v.new_level_iter(l);
            let iter = DbIteratorWrapper::new(&mut iter);
            assert_eq!(iter.count(), expected_entries[l]);
        }
    }

    #[test]
    fn test_version_concat_iter_properties() {
        let v = make_version().0;
        let iter = v.new_level_iter(3);
        test_iterator_properties(iter);
    }

    // #[test]
    // fn test_version_max_next_level_overlapping() {
    //     let v = make_version().0;
    //     assert_eq!(218, v.max_next_level_overlapping_bytes());
    // }

    #[test]
    fn test_version_all_iters() {
        let v = make_version().0;
        let iters = v.new_iters().unwrap();
        let mut opt = Options::for_test();
        opt.cmp = Rc::new(InternalKeyCmp(Rc::new(DefaultCmp)));

        let mut miter = MergingIterator::new(opt.cmp.clone(), iters);
        assert_eq!(DbIteratorWrapper::new(&mut miter).count(), 30);

        // Check that all elements are in order.
        let init = LookupKey::new("000".as_bytes(), MAX_SEQNUM);
        let cmp = InternalKeyCmp(Rc::new(DefaultCmp));
        DbIteratorWrapper::new(&mut miter).fold(init.internal_key().to_vec(), |b, (k, _)| {
            assert!(cmp.cmp(&b, &k) == Ordering::Less);
            k
        });
    }

    // #[test]
    // fn test_version_summary() {
    //     let v = make_version().0;
    //     let expected =
    //         "level 0: 2 files, 483 bytes ([(1, 232), (2, 251)]); level 1: 3 files, 651 \
    //                 bytes ([(3, 218), (4, 216), (5, 217)]); level 2: 2 files, 468 bytes ([(6, \
    //                 218), (7, 250)]); level 3: 2 files, 400 bytes ([(8, 200), (9, 200)]); ";
    //     assert_eq!(expected, &v.summary());
    // }

    #[test]
    fn test_version_get_simple() {
        let v = make_version().0;
        let cases: &[(&[u8], u64, Result<Option<Vec<u8>>>)] = &[
            ("aaa".as_bytes(), 1, Ok(None)),
            ("aaa".as_bytes(), 100, Ok(Some("val1".as_bytes().to_vec()))),
            ("aaa".as_bytes(), 21, Ok(Some("val0".as_bytes().to_vec()))),
            ("aab".as_bytes(), 0, Ok(None)),
            ("aab".as_bytes(), 100, Ok(Some("val2".as_bytes().to_vec()))),
            ("aac".as_bytes(), 100, Ok(None)),
            ("aac".as_bytes(), 25, Ok(Some("val3".as_bytes().to_vec()))),
            ("aba".as_bytes(), 100, Ok(Some("val3".as_bytes().to_vec()))),
            ("aba".as_bytes(), 25, Ok(Some("val4".as_bytes().to_vec()))),
            ("daa".as_bytes(), 100, Ok(Some("val1".as_bytes().to_vec()))),
            ("dab".as_bytes(), 1, Ok(None)),
            ("dac".as_bytes(), 100, Ok(None)),
            ("gba".as_bytes(), 100, Ok(Some("val3".as_bytes().to_vec()))),
            // deleted key
            ("gca".as_bytes(), 100, Ok(None)),
            ("gbb".as_bytes(), 100, Ok(None)),
        ];

        for ref c in cases {
            match v.get(LookupKey::new(c.0, c.1).internal_key()) {
                Ok(Some((val, _))) => assert_eq!(c.2.as_ref().unwrap().as_ref().unwrap(), &val),
                Ok(None) => assert!(c.2.as_ref().unwrap().as_ref().is_none()),
                Err(_) => assert!(c.2.is_err()),
            }
        }
    }

    #[test]
    fn test_version_get_overlapping_basic() {
        let v = make_version().0;

        // Overlapped by tables 1 and 2.
        let ol = v.get_overlapping(LookupKey::new(b"aay", 50).internal_key());
        // Check that sorting order is newest-first in L0.
        assert_eq!(2, ol[0][0].borrow().id);
        // Check that table from L1 matches.
        assert_eq!(3, ol[1][0].borrow().id);

        let ol = v.get_overlapping(LookupKey::new(b"cb", 50).internal_key());
        assert_eq!(3, ol[1][0].borrow().id);
        assert_eq!(6, ol[2][0].borrow().id);

        let ol = v.get_overlapping(LookupKey::new(b"x", 50).internal_key());
        for i in 0..NUM_LEVELS {
            assert!(ol[i].is_empty());
        }
    }

    #[test]
    fn test_version_overlap_in_level() {
        let v = make_version().0;

        for &(level, (k1, k2), want) in &[
            (0, ("000".as_bytes(), "003".as_bytes()), false),
            (0, ("aa0".as_bytes(), "abx".as_bytes()), true),
            (1, ("012".as_bytes(), "013".as_bytes()), false),
            (1, ("abc".as_bytes(), "def".as_bytes()), true),
            (2, ("xxx".as_bytes(), "xyz".as_bytes()), false),
            (2, ("gac".as_bytes(), "gaz".as_bytes()), true),
        ] {
            if want {
                assert!(v.overlaps_in_level(level, k1, k2));
            } else {
                assert!(!v.overlaps_in_level(level, k1, k2));
            }
        }
    }

    #[test]
    fn test_version_pick_memtable_output_level() {
        let v = make_version().0;

        for c in [
            ("000".as_bytes(), "abc".as_bytes(), 0),
            ("gab".as_bytes(), "hhh".as_bytes(), 1),
            ("000".as_bytes(), "111".as_bytes(), 2),
        ]
        .iter()
        {
            assert_eq!(c.2, v.pick_memtable_output_level(c.0, c.1));
        }
    }

    #[test]
    fn test_version_overlapping_inputs() {
        let v = make_version().0;

        time_test!("overlapping-inputs");
        {
            // Range is expanded in overlapping level-0 files.
            let from = LookupKey::new("aab".as_bytes(), MAX_SEQNUM);
            let to = LookupKey::new("aae".as_bytes(), 0);
            let r = v.overlapping_inputs(0, from.internal_key(), to.internal_key());
            assert_eq!(r.len(), 2);
            assert_eq!(r[0].borrow().id, 1);
            assert_eq!(r[1].borrow().id, 2);
        }
        {
            let from = LookupKey::new("cab".as_bytes(), MAX_SEQNUM);
            let to = LookupKey::new("cbx".as_bytes(), 0);
            // expect one file.
            let r = v.overlapping_inputs(1, from.internal_key(), to.internal_key());
            assert_eq!(r.len(), 1);
            assert_eq!(r[0].borrow().id, 3);
        }
        {
            let from = LookupKey::new("cab".as_bytes(), MAX_SEQNUM);
            let to = LookupKey::new("ebx".as_bytes(), 0);
            let r = v.overlapping_inputs(1, from.internal_key(), to.internal_key());
            // Assert that correct number of files and correct files were returned.
            assert_eq!(r.len(), 3);
            assert_eq!(r[0].borrow().id, 3);
            assert_eq!(r[1].borrow().id, 4);
            assert_eq!(r[2].borrow().id, 5);
        }
        {
            let from = LookupKey::new("hhh".as_bytes(), MAX_SEQNUM);
            let to = LookupKey::new("ijk".as_bytes(), 0);
            let r = v.overlapping_inputs(2, from.internal_key(), to.internal_key());
            assert_eq!(r.len(), 0);
            let r = v.overlapping_inputs(1, from.internal_key(), to.internal_key());
            assert_eq!(r.len(), 0);
        }
    }

    #[test]
    fn test_version_record_read_sample() {
        let mut v = make_version().0;
        let k = LookupKey::new("aab".as_bytes(), MAX_SEQNUM);
        let only_in_one = LookupKey::new("cax".as_bytes(), MAX_SEQNUM);

        assert!(!v.record_read_sample(k.internal_key()));
        assert!(!v.record_read_sample(only_in_one.internal_key()));

        for fs in v.files.iter() {
            for f in fs {
                f.borrow_mut().allowed_seeks = 0;
            }
        }
        assert!(v.record_read_sample(k.internal_key()));
    }

    #[test]
    fn test_version_key_ordering() {
        time_test!();
        let fmh = new_file(1, &[1, 0, 0], 0, &[2, 0, 0], 1);
        let cmp = InternalKeyCmp(Rc::new(DefaultCmp));

        // Keys before file.
        for k in &[&[0][..], &[1], &[1, 0], &[0, 9, 9, 9]] {
            assert!(key_is_before_file(&cmp, k, &fmh));
            assert!(!key_is_after_file(&cmp, k, &fmh));
        }
        // Keys in file.
        for k in &[
            &[1, 0, 0][..],
            &[1, 0, 1],
            &[1, 2, 3, 4],
            &[1, 9, 9],
            &[2, 0, 0],
        ] {
            assert!(!key_is_before_file(&cmp, k, &fmh));
            assert!(!key_is_after_file(&cmp, k, &fmh));
        }
        // Keys after file.
        for k in &[&[2, 0, 1][..], &[9, 9, 9], &[9, 9, 9, 9]] {
            assert!(!key_is_before_file(&cmp, k, &fmh));
            assert!(key_is_after_file(&cmp, k, &fmh));
        }
    }

    #[test]
    fn test_version_file_overlaps() {
        time_test!();

        let files_disjoint = [
            new_file(1, &[2, 0, 0], 0, &[3, 0, 0], 1),
            new_file(2, &[3, 0, 1], 0, &[4, 0, 0], 1),
            new_file(3, &[4, 0, 1], 0, &[5, 0, 0], 1),
        ];
        let files_joint = [
            new_file(1, &[2, 0, 0], 0, &[3, 0, 0], 1),
            new_file(2, &[2, 5, 0], 0, &[4, 0, 0], 1),
            new_file(3, &[3, 5, 1], 0, &[5, 0, 0], 1),
        ];
        let cmp = InternalKeyCmp(Rc::new(DefaultCmp));

        assert!(overlaps_range(&cmp, &files_joint, &[2, 5, 0], &[3, 1, 0]));
        assert!(overlaps_range(&cmp, &files_joint, &[2, 5, 0], &[7, 0, 0]));
        assert!(overlaps_range(&cmp, &files_joint, &[0, 0], &[2, 0, 0]));
        assert!(overlaps_range(&cmp, &files_joint, &[0, 0], &[7, 0, 0]));
        assert!(!overlaps_range(&cmp, &files_joint, &[0, 0], &[0, 5]));
        assert!(!overlaps_range(&cmp, &files_joint, &[6, 0], &[7, 5]));

        assert!(overlaps_range_disjoint(
            &cmp,
            &files_disjoint,
            &[2, 0, 1],
            &[2, 5, 0]
        ));
        assert!(overlaps_range_disjoint(
            &cmp,
            &files_disjoint,
            &[3, 0, 1],
            &[4, 9, 0]
        ));
        assert!(overlaps_range_disjoint(
            &cmp,
            &files_disjoint,
            &[2, 0, 1],
            &[6, 5, 0]
        ));
        assert!(overlaps_range_disjoint(
            &cmp,
            &files_disjoint,
            &[0, 0, 1],
            &[2, 5, 0]
        ));
        assert!(overlaps_range_disjoint(
            &cmp,
            &files_disjoint,
            &[0, 0, 1],
            &[6, 5, 0]
        ));
        assert!(!overlaps_range_disjoint(
            &cmp,
            &files_disjoint,
            &[0, 0, 1],
            &[0, 1]
        ));
        assert!(!overlaps_range_disjoint(
            &cmp,
            &files_disjoint,
            &[6, 0, 1],
            &[7, 0, 1]
        ));
    }
}
