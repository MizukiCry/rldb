use std::{
    cell::RefCell,
    cmp::Ordering,
    collections::HashSet,
    io::{Read, Write},
    path::{Path, PathBuf},
    rc::Rc,
};

use integer_encoding::{VarIntReader, VarIntWriter};

use crate::coredef::{
    cmp::{Cmp, InternalKeyCmp},
    env::Env,
    error::{err, Result, StatusCode},
    key::{parse_internal_key, InternalKey, UserKey},
    log::{LogReader, LogWriter},
    options::Options,
    types::{parse_file_name, DbIterator, FileID, FileMetaData, FileType, MergingIterator, SeqNum},
    NUM_LEVELS,
};
use crate::log;
use crate::storage::{
    table::TableCache,
    version::{FileMetaHandle, Version, VersionIterator},
};

pub struct Compaction {
    level: usize,
    max_file_size: usize,
    version: Option<Rc<RefCell<Version>>>,
    level_indexes: [usize; NUM_LEVELS],

    cmp: Rc<dyn Cmp>,
    icmp: InternalKeyCmp,

    manual: bool,

    // level, level+1
    inputs: [Vec<FileMetaHandle>; 2],
    grandparent_index: usize,
    // level+2..NUM_LEVELS
    grandparents: Option<Vec<FileMetaHandle>>,
    overlapped_bytes: usize,
    seen_key: bool,
    edit: VersionEdit,
}

impl Compaction {
    pub fn new(options: &Options, level: usize, version: Option<Rc<RefCell<Version>>>) -> Self {
        Self {
            level,
            max_file_size: options.max_file_size,
            version,
            level_indexes: [0; NUM_LEVELS],
            cmp: options.cmp.clone(),
            icmp: InternalKeyCmp(options.cmp.clone()),
            manual: false,
            inputs: [Vec::new(), Vec::new()],
            grandparent_index: 0,
            grandparents: None,
            overlapped_bytes: 0,
            seen_key: false,
            edit: VersionEdit::new(),
        }
    }

    pub fn level(&self) -> usize {
        self.level
    }

    pub fn num_inputs(&self, parent: usize) -> usize {
        self.inputs[parent].len()
    }

    pub fn input(&self, parent: usize, index: usize) -> FileMetaData {
        self.inputs[parent][index].borrow().clone()
    }

    /// Marks current input files as deleted.
    pub fn delete_inputs(&mut self) {
        for parent in 0..2 {
            for f in self.inputs[parent].iter() {
                self.edit
                    .deleted_files
                    .insert((self.level + parent, f.borrow().id));
            }
        }
    }

    /// Whether the key may exist in the level >= self.level + 2
    pub fn is_base_level_for(&mut self, key: UserKey) -> bool {
        for level in self.level + 2..NUM_LEVELS {
            let files = &self.version.as_ref().unwrap().borrow().files[level];
            while self.level_indexes[level] < files.len() {
                let f = files[self.level_indexes[level]].borrow();
                if self.cmp.cmp(key, parse_internal_key(&f.largest).2) != Ordering::Greater {
                    if self.cmp.cmp(key, parse_internal_key(&f.smallest).2) != Ordering::Less {
                        return false;
                    }
                    break;
                }
                self.level_indexes[level] += 1;
            }
        }
        true
    }

    pub fn is_trivial_move(&self) -> bool {
        let inputs_size = self
            .grandparents
            .as_ref()
            .map_or(0, |gp| gp.iter().map(|f| f.borrow().size).sum());
        !self.manual
            && self.num_inputs(0) == 1
            && self.num_inputs(1) == 0
            && inputs_size < 10 * self.max_file_size
    }

    pub fn should_stop_before(&mut self, key: InternalKey) -> bool {
        if self.grandparents.is_none() {
            self.seen_key = true;
            return false;
        }

        let grandparents = self.grandparents.as_ref().unwrap();
        while self.grandparent_index < grandparents.len()
            && self
                .icmp
                .cmp(key, &grandparents[self.grandparent_index].borrow().largest)
                == Ordering::Greater
        {
            if self.seen_key {
                self.overlapped_bytes += grandparents[self.grandparent_index].borrow().size
            }
            self.grandparent_index += 1;
        }
        self.seen_key = true;

        if self.overlapped_bytes > 10 * self.max_file_size {
            self.overlapped_bytes = 0;
            true
        } else {
            false
        }
    }

    pub fn edit(&mut self) -> &mut VersionEdit {
        &mut self.edit
    }

    pub fn into_edit(self) -> VersionEdit {
        self.edit
    }
}

/// Manage a set of versions.
pub struct VersionSet {
    database: PathBuf,
    options: Options,
    cmp: InternalKeyCmp,
    cache: Rc<RefCell<TableCache>>,

    pub next_file_id: FileID,
    pub manifest_id: FileID,
    pub last_sequence: SeqNum,
    pub log_id: FileID,
    pub previous_log_id: FileID,

    current: Option<Rc<RefCell<Version>>>,
    compaction_pointers: [Vec<u8>; NUM_LEVELS],
    descriptor_log: Option<LogWriter<Box<dyn Write>>>,
}

impl VersionSet {
    pub fn new(
        database: impl AsRef<Path>,
        options: Options,
        cache: Rc<RefCell<TableCache>>,
    ) -> Self {
        Self {
            database: database.as_ref().to_owned(),
            cmp: InternalKeyCmp(options.cmp.clone()),
            current: Some(Rc::new(RefCell::new(Version::new(
                cache.clone(),
                options.cmp.clone(),
            )))),
            options,
            cache,

            next_file_id: 2,
            manifest_id: 0,
            last_sequence: 0,
            log_id: 0,
            previous_log_id: 0,

            compaction_pointers: Default::default(),
            descriptor_log: None,
        }
    }

    pub fn summary(&self) -> String {
        self.current.as_ref().unwrap().borrow().summary()
    }

    pub fn active_files(&self) -> HashSet<FileID> {
        let mut files = HashSet::new();
        if let Some(version) = self.current.as_ref() {
            for level in 0..NUM_LEVELS {
                for f in version.borrow().files[level].iter() {
                    files.insert(f.borrow().id);
                }
            }
        }
        files
    }

    pub fn current(&self) -> Rc<RefCell<Version>> {
        self.current.as_ref().unwrap().clone()
    }

    pub fn set_version(&mut self, version: Version) {
        self.current = Some(Rc::new(RefCell::new(version)));
    }

    pub fn new_file_id(&mut self) -> FileID {
        self.next_file_id += 1;
        self.next_file_id - 1
    }

    pub fn reuse_file_id(&mut self, id: FileID) {
        if id == self.next_file_id - 1 {
            self.next_file_id = id;
        }
    }

    pub fn skip_file_id(&mut self, id: FileID) {
        if self.next_file_id <= id {
            self.next_file_id = id + 1;
        }
    }

    pub fn needs_compaction(&self) -> bool {
        let v = self.current.as_ref().unwrap();
        v.borrow().compaction_score.is_some_and(|s| s >= 1.0)
            || v.borrow().file_to_compact.is_some()
    }

    #[cfg(test)]
    fn approx_offset(&self, version: &Rc<RefCell<Version>>, key: InternalKey) -> usize {
        let mut offset = 0;
        for level in 0..NUM_LEVELS {
            for file in version.borrow().files[level].iter() {
                let f = file.borrow();
                if self.options.cmp.cmp(&f.largest, key) != Ordering::Greater {
                    offset += f.size;
                } else if self.options.cmp.cmp(&f.smallest, key) == Ordering::Greater {
                    if level != 0 {
                        break;
                    }
                } else if let Ok(table) = self.cache.borrow_mut().get_table(f.id) {
                    offset += table.approx_offset(key);
                }
            }
        }
        offset
    }

    pub fn pick_compaction(&mut self) -> Option<Compaction> {
        let current = self.current();
        let current = current.borrow();
        let mut compaction = Compaction::new(&self.options, 0, self.current.clone());

        if current.compaction_score.is_some_and(|s| s >= 1.0) {
            compaction.level = current.compaction_level.unwrap();

            for f in current.files[compaction.level].iter() {
                if self.compaction_pointers[compaction.level].is_empty()
                    || self.cmp.cmp(
                        &f.borrow().largest,
                        &self.compaction_pointers[compaction.level],
                    ) == Ordering::Greater
                {
                    compaction.inputs[0].push(f.clone());
                    break;
                }
            }

            if compaction.inputs[0].is_empty() {
                compaction.inputs[0].push(current.files[compaction.level][0].clone());
            }
        } else if let Some(f) = current.file_to_compact.as_ref() {
            compaction.level = current.file_to_compact_level;
            compaction.inputs[0].push(f.clone());
        } else {
            return None;
        }

        compaction.version = self.current.clone();

        if compaction.level == 0 {
            let (begin, end) = get_range(&self.cmp, compaction.inputs[0].iter());
            compaction.inputs[0] = current.overlapping_inputs(0, &begin, &end);
            assert!(!compaction.inputs[0].is_empty());
        }

        self.setup_other_inputs(&mut compaction);
        Some(compaction)
    }

    pub fn compact_range(
        &mut self,
        level: usize,
        begin: InternalKey,
        end: InternalKey,
    ) -> Option<Compaction> {
        let mut inputs = self
            .current
            .as_ref()
            .unwrap()
            .borrow()
            .overlapping_inputs(level, begin, end);
        if inputs.is_empty() {
            return None;
        }

        if level > 0 {
            let mut size = 0;
            for (i, input) in inputs.iter().enumerate() {
                size += input.borrow().size;
                if size > self.options.max_file_size {
                    inputs.truncate(i + 1);
                    break;
                }
            }
        }

        let mut compaction = Compaction::new(&self.options, level, self.current.clone());
        compaction.inputs[0] = inputs;
        compaction.manual = true;
        self.setup_other_inputs(&mut compaction);
        Some(compaction)
    }

    fn setup_other_inputs(&mut self, compaction: &mut Compaction) {
        let current = self.current.as_ref().unwrap();
        let current = current.borrow();
        let level = compaction.level;

        let (mut begin, mut end) = get_range(&self.cmp, compaction.inputs[0].iter());
        compaction.inputs[1] = current.overlapping_inputs(level + 1, &begin, &end);
        let (mut all_begin, mut all_end) = get_range(
            &self.cmp,
            compaction.inputs[0]
                .iter()
                .chain(compaction.inputs[1].iter()),
        );

        if !compaction.inputs[1].is_empty() {
            let expanded0 = current.overlapping_inputs(level, &all_begin, &all_end);
            let inputs1_size = compaction.inputs[1]
                .iter()
                .map(|f| f.borrow().size)
                .sum::<usize>();
            let expanded0_size = expanded0.iter().map(|f| f.borrow().size).sum::<usize>();
            if expanded0.len() > compaction.num_inputs(0)
                && inputs1_size + expanded0_size < 25 * self.options.max_file_size
            {
                let (new_begin, new_end) = get_range(&self.cmp, expanded0.iter());
                let expanded1 = current.overlapping_inputs(level + 1, &new_begin, &new_end);
                if expanded1.len() == compaction.num_inputs(1) {
                    log!(
                        self.options.log,
                        "Expanding inputs@{} {}+{} ({}+{} bytes) to {}+{} ({}+{} bytes)",
                        level,
                        compaction.inputs[0].len(),
                        compaction.inputs[1].len(),
                        compaction.inputs[0]
                            .iter()
                            .map(|f| f.borrow().size)
                            .sum::<usize>(),
                        compaction.inputs[1]
                            .iter()
                            .map(|f| f.borrow().size)
                            .sum::<usize>(),
                        expanded0.len(),
                        expanded1.len(),
                        expanded0.iter().map(|f| f.borrow().size).sum::<usize>(),
                        expanded1.iter().map(|f| f.borrow().size).sum::<usize>()
                    );

                    begin = new_begin;
                    end = new_end;
                    compaction.inputs[0] = expanded0;
                    compaction.inputs[1] = expanded1;
                    (all_begin, all_end) = get_range(
                        &self.cmp,
                        compaction.inputs[0]
                            .iter()
                            .chain(compaction.inputs[1].iter()),
                    );
                }
            }
        }

        if level + 2 < NUM_LEVELS {
            compaction.grandparents =
                Some(current.overlapping_inputs(level + 2, &all_begin, &all_end));
        }

        log!(
            self.options.log,
            "Compacting @{} {:?} .. {:?}",
            level,
            begin,
            end
        );

        compaction
            .edit()
            .compaction_pointers
            .push((level, end.clone()));
        self.compaction_pointers[level] = end;
    }

    fn write_snapshot(&mut self) -> Result<()> {
        let mut ve = VersionEdit::new();
        ve.comparator = Some(self.options.cmp.name().to_string());

        for (level, pointer) in self.compaction_pointers.iter().enumerate() {
            if !pointer.is_empty() {
                ve.compaction_pointers.push((level, pointer.clone()));
            }
        }

        let current = self.current.as_ref().unwrap().borrow();
        for (level, files) in current.files.iter().enumerate() {
            for f in files.iter() {
                ve.new_files.push((level, f.borrow().clone()));
            }
        }
        self.descriptor_log
            .as_mut()
            .unwrap()
            .add_record(&ve.encode())
    }

    /// Merges the edit and writes it to the manifest file.
    pub fn log_and_apply(&mut self, mut ve: VersionEdit) -> Result<()> {
        assert!(self.current.is_some());

        if ve.log_id.is_none() {
            ve.log_id = Some(self.log_id);
        } else {
            assert!(ve.log_id.unwrap() >= self.log_id && ve.log_id.unwrap() < self.next_file_id);
        }

        if ve.prev_log_id.is_none() {
            ve.prev_log_id = Some(self.previous_log_id);
        }
        ve.next_file_id = Some(self.next_file_id);
        ve.last_sequence = Some(self.last_sequence);

        let mut version = Version::new(self.cache.clone(), self.options.cmp.clone());
        {
            let mut builder = Builder::new();
            builder.apply(&ve, &mut self.compaction_pointers);
            builder.save_to(&self.cmp, self.current.as_ref().unwrap(), &mut version);
        }
        self.finalize(&mut version);

        if self.descriptor_log.is_none() {
            ve.next_file_id = Some(self.next_file_id);
            self.descriptor_log = Some(LogWriter::new(self.options.env.open_writable_file(
                manifest_file_name(&self.database, self.manifest_id).as_path(),
            )?));
            self.write_snapshot()?;
        }

        if let Some(log) = self.descriptor_log.as_mut() {
            log.add_record(&ve.encode())?;
            log.flush()?;
        }
        set_current_file(self.options.env.as_ref(), &self.database, self.manifest_id)?;

        self.set_version(version);
        self.log_id = ve.log_id.unwrap();
        Ok(())
    }

    fn finalize(&self, version: &mut Version) {
        let (level, score) = (0..NUM_LEVELS - 1)
            .map(|level| {
                let score = if level == 0 {
                    version.files[0].len() as f64 / 4.0
                } else {
                    version.files[level]
                        .iter()
                        .map(|f| f.borrow().size)
                        .sum::<usize>() as f64
                        / 10_f64.powi(level as i32)
                        / 1048576.0
                };
                (level, score)
            })
            .max_by(|a, b| a.1.total_cmp(&b.1))
            .unwrap();
        version.compaction_score = Some(score);
        version.compaction_level = Some(level);
    }

    /// Recovers the state of a DB instance from the files on disk.
    /// If returns true, a new manifest needs to be written eventually (using log_and_apply()).
    pub fn recover(&mut self) -> Result<bool> {
        let mut current = read_current_file(self.options.env.as_ref(), &self.database)?;
        current.pop();
        let current = Path::new(&current);

        let log_file_name = self.database.join(current);
        let mut builder = Builder::new();
        {
            let mut log_file = self.options.env.open_sequential_file(&log_file_name)?;
            let mut log_reader = LogReader::new(&mut log_file, true);
            let mut log_id = None;
            let mut prev_log_id = None;
            let mut next_file_id = None;
            let mut last_sequence = None;
            let mut buf = Vec::new();

            while let Ok(ok) = log_reader.read(&mut buf) {
                if !ok {
                    break;
                }
                let ve = VersionEdit::decode(&buf)?;
                builder.apply(&ve, &mut self.compaction_pointers);
                if ve.log_id.is_some() {
                    log_id = ve.log_id;
                }
                if ve.prev_log_id.is_some() {
                    prev_log_id = ve.prev_log_id;
                }
                if ve.next_file_id.is_some() {
                    next_file_id = ve.next_file_id;
                }
                if ve.last_sequence.is_some() {
                    last_sequence = ve.last_sequence;
                }
            }

            if let Some(id) = log_id {
                self.log_id = id;
                self.skip_file_id(id);
            } else {
                return err(StatusCode::Corruption, "No log ID found in the descriptor");
            }
            if let Some(id) = prev_log_id {
                self.previous_log_id = id;
                self.skip_file_id(id);
            } else {
                self.previous_log_id = 0;
            }
            if let Some(id) = next_file_id {
                self.next_file_id = id + 1;
            } else {
                return err(
                    StatusCode::Corruption,
                    "No next file ID found in the descriptor",
                );
            }
            if let Some(seq) = last_sequence {
                self.last_sequence = seq;
            } else {
                return err(
                    StatusCode::Corruption,
                    "No last sequence found in the descriptor",
                );
            }
        }

        let mut version = Version::new(self.cache.clone(), self.options.cmp.clone());
        builder.save_to(&self.cmp, &self.current(), &mut version);
        self.finalize(&mut version);
        self.set_version(version);
        self.manifest_id = self.next_file_id - 1;

        log!(
            self.options.log,
            "Recovered manifest with next_file={} manifest_num={} log_num={} prev_log_num={} last_seq={}",
            self.next_file_id,
            self.manifest_id,
            self.log_id,
            self.previous_log_id,
            self.last_sequence
        );

        Ok(!self.can_reuse_manifest(&log_file_name, current))
    }

    fn can_reuse_manifest(&mut self, log_file_name: &Path, current: &Path) -> bool {
        if !self.options.reuse_manifest {
            return false;
        }

        if let Ok((id, t)) = parse_file_name(current.to_str().unwrap()) {
            if t != FileType::Descriptor {
                return false;
            }

            if let Ok(size) = self.options.env.size_of(log_file_name) {
                if size >= self.options.max_file_size {
                    return false;
                }
                let file = self.options.env.open_appendable_file(log_file_name);
                if let Ok(f) = file {
                    log!(self.options.log, "Reusing manifest {:?}", log_file_name);
                    self.descriptor_log = Some(LogWriter::new_with_offset(f, size));
                    self.manifest_id = id;
                    return true;
                } else {
                    log!(
                        self.options.log,
                        "Reuse manifest failed: {:?}",
                        file.err().unwrap()
                    );
                }
            }
        }
        false
    }

    pub fn make_input_iterator(&self, c: &Compaction) -> Box<dyn DbIterator> {
        let capacity = if c.level == 0 { c.num_inputs(0) + 1 } else { 2 };
        let mut iters: Vec<Box<dyn DbIterator>> = Vec::with_capacity(capacity);
        for i in 0..2 {
            if c.num_inputs(i) == 0 {
                continue;
            }
            if c.level + i == 0 {
                for f in c.inputs[i].iter() {
                    let table = self.cache.borrow_mut().get_table(f.borrow().id);
                    if let Ok(table) = table {
                        iters.push(Box::new(table.iter()));
                    } else {
                        log!(
                            self.options.log,
                            "error opening table {}: {}",
                            f.borrow().id,
                            table.err().unwrap()
                        );
                    }
                }
            } else {
                iters.push(Box::new(VersionIterator::new(
                    c.inputs[i].clone(),
                    self.cache.clone(),
                    self.options.cmp.clone(),
                )));
            }
        }
        assert!(iters.len() <= capacity);
        Box::new(MergingIterator::new(Rc::new(self.cmp.clone()), iters))
    }
}

/// Returns the smallest and largest keys in the given files.
fn get_range<'a>(
    cmp: &impl Cmp,
    files: impl Iterator<Item = &'a FileMetaHandle>,
) -> (Vec<u8>, Vec<u8>) {
    let mut begin: Option<Vec<u8>> = None;
    let mut end: Option<Vec<u8>> = None;
    for f in files {
        let f = f.borrow();
        if begin.is_none() || cmp.cmp(&f.smallest, begin.as_ref().unwrap()) == Ordering::Less {
            begin = Some(f.smallest.clone());
        }
        if end.is_none() || cmp.cmp(&f.largest, end.as_ref().unwrap()) == Ordering::Greater {
            end = Some(f.largest.clone());
        }
    }
    (begin.unwrap(), end.unwrap())
}

struct Builder {
    deleted: [Vec<FileID>; NUM_LEVELS],
    added: [Vec<FileMetaHandle>; NUM_LEVELS],
}

impl Builder {
    pub fn new() -> Self {
        Self {
            deleted: Default::default(),
            added: Default::default(),
        }
    }

    fn apply(&mut self, ve: &VersionEdit, cp: &mut [Vec<u8>; NUM_LEVELS]) {
        for pointer in ve.compaction_pointers.iter() {
            cp[pointer.0] = pointer.1.clone();
        }
        for (level, id) in ve.deleted_files.iter() {
            self.deleted[*level].push(*id);
        }
        for &(level, ref f) in ve.new_files.iter() {
            let mut f = f.clone();
            f.allowed_seeks = (f.size / 16384).max(100);
            self.deleted[level] = self.deleted[level]
                .iter()
                .filter_map(|&id| if id != f.id { Some(id) } else { None })
                .collect();
            self.added[level].push(Rc::new(RefCell::new(f)));
        }
    }

    fn save_to(
        &mut self,
        cmp: &InternalKeyCmp,
        base: &Rc<RefCell<Version>>,
        version: &mut Version,
    ) {
        for level in 0..NUM_LEVELS {
            self.added[level].sort_by(|a, b| cmp.cmp(&a.borrow().smallest, &b.borrow().smallest));
            base.borrow_mut().files[level]
                .sort_by(|a, b| cmp.cmp(&a.borrow().smallest, &b.borrow().smallest));

            let added_files = self.added[level].clone();
            let base_files = base.borrow().files[level].clone();
            version.files[level].reserve(added_files.len() + base_files.len());
            let merged_files =
                merge_iters(added_files.into_iter(), base_files.into_iter(), |a, b| {
                    cmp.cmp(&a.borrow().smallest, &b.borrow().smallest)
                });

            for f in merged_files {
                if self.deleted[level].contains(&f.borrow().id) {
                    continue;
                }
                let files = &mut version.files[level];
                if level != 0 && !files.is_empty() {
                    assert!(
                        cmp.cmp(
                            &files.last().unwrap().borrow().largest,
                            &f.borrow().smallest
                        ) == Ordering::Less
                    );
                }
                files.push(f);
            }

            if level != 0 {
                for i in 1..version.files[level].len() {
                    assert!(
                        cmp.cmp(
                            &version.files[level][i - 1].borrow().largest,
                            &version.files[level][i].borrow().smallest
                        ) == Ordering::Less
                    );
                }
            }
        }
    }
}

fn manifest_name(file_id: FileID) -> PathBuf {
    Path::new(&format!("MANIFEST-{:06}", file_id)).to_owned()
}

pub fn manifest_file_name(database: impl AsRef<Path>, file_id: FileID) -> PathBuf {
    database.as_ref().join(manifest_name(file_id))
}

fn temp_file_name(database: impl AsRef<Path>, file_id: FileID) -> PathBuf {
    database.as_ref().join(format!("{:06}.dbtmp", file_id))
}

fn current_file_name(database: impl AsRef<Path>) -> PathBuf {
    database.as_ref().join("CURRENT")
}

fn merge_iters<T, It: Iterator<Item = T>>(
    mut a: It,
    mut b: It,
    cmp: impl Fn(&T, &T) -> Ordering,
) -> Vec<T> {
    let mut res = Vec::new();

    let mut a_val = a.next();
    let mut b_val = b.next();
    while a_val.is_some() && b_val.is_some() {
        if cmp(a_val.as_ref().unwrap(), b_val.as_ref().unwrap()) == Ordering::Less {
            res.push(a_val.unwrap());
            a_val = a.next();
        } else {
            res.push(b_val.unwrap());
            b_val = b.next();
        }
    }

    while let Some(v) = a_val {
        res.push(v);
        a_val = a.next();
    }

    while let Some(v) = b_val {
        res.push(v);
        b_val = b.next();
    }

    res
}

pub fn read_current_file(env: &dyn Env, database: impl AsRef<Path>) -> Result<String> {
    let mut current = String::new();
    env.open_sequential_file(Path::new(&current_file_name(database)))?
        .read_to_string(&mut current)?;
    if !current.ends_with('\n') {
        return err(
            StatusCode::Corruption,
            "CURRENT file does not end with newline",
        );
    }
    Ok(current)
}

pub fn set_current_file(
    env: &dyn Env,
    database: impl AsRef<Path>,
    manifest_file_id: FileID,
) -> Result<()> {
    let temp_file = temp_file_name(database.as_ref(), manifest_file_id);
    {
        let mut f = env.open_writable_file(&temp_file)?;
        f.write_all(manifest_name(manifest_file_id).to_str().unwrap().as_bytes())?;
        f.write_all(b"\n")?;
    }
    if let Err(e) = env.rename(&temp_file, &current_file_name(database)) {
        let _ = env.delete(&temp_file);
        return Err(e);
    }
    Ok(())
}

enum EditTag {
    Comparator = 1,
    LogID = 2,
    NextFileID = 3,
    LastSequence = 4,
    CompactPointer = 5,
    DeletedFile = 6,
    NewFile = 7,
    PreviousLogID = 9, // sic!
}

fn u32_to_tag(tag: u32) -> Option<EditTag> {
    match tag {
        1 => Some(EditTag::Comparator),
        2 => Some(EditTag::LogID),
        3 => Some(EditTag::NextFileID),
        4 => Some(EditTag::LastSequence),
        5 => Some(EditTag::CompactPointer),
        6 => Some(EditTag::DeletedFile),
        7 => Some(EditTag::NewFile),
        9 => Some(EditTag::PreviousLogID),
        _ => None,
    }
}

/// Manages changes to the set of managed SSTables and log files.
// #[derive(Debug)]
pub struct VersionEdit {
    pub comparator: Option<String>,
    pub log_id: Option<FileID>,
    pub prev_log_id: Option<FileID>,
    pub next_file_id: Option<FileID>,
    pub last_sequence: Option<SeqNum>,

    // (level, internal_key)
    pub compaction_pointers: Vec<(usize, Vec<u8>)>,
    pub deleted_files: HashSet<(usize, FileID)>,
    pub new_files: Vec<(usize, FileMetaData)>,
}

impl Default for VersionEdit {
    fn default() -> Self {
        Self::new()
    }
}

impl VersionEdit {
    pub fn new() -> Self {
        Self {
            comparator: None,
            log_id: None,
            prev_log_id: None,
            next_file_id: None,
            last_sequence: None,
            compaction_pointers: Vec::with_capacity(8),
            deleted_files: HashSet::with_capacity(8),
            new_files: Vec::with_capacity(8),
        }
    }

    pub fn clear(&mut self) {
        *self = Self::new();
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(256);

        if let Some(cmp) = self.comparator.as_ref() {
            buf.write_varint(EditTag::Comparator as u32).unwrap();
            buf.write_varint(cmp.len()).unwrap();
            buf.write_all(cmp.as_bytes()).unwrap();
        }

        if let Some(log_id) = self.log_id {
            buf.write_varint(EditTag::LogID as u32).unwrap();
            buf.write_varint(log_id).unwrap();
        }

        if let Some(prev_log_id) = self.prev_log_id {
            buf.write_varint(EditTag::PreviousLogID as u32).unwrap();
            buf.write_varint(prev_log_id).unwrap();
        }

        if let Some(next_file_id) = self.next_file_id {
            buf.write_varint(EditTag::NextFileID as u32).unwrap();
            buf.write_varint(next_file_id).unwrap();
        }

        if let Some(last_sequence) = self.last_sequence {
            buf.write_varint(EditTag::LastSequence as u32).unwrap();
            buf.write_varint(last_sequence).unwrap();
        }

        for (level, key) in self.compaction_pointers.iter() {
            buf.write_varint(EditTag::CompactPointer as u32).unwrap();
            buf.write_varint(*level).unwrap();
            buf.write_varint(key.len()).unwrap();
            buf.write_all(key).unwrap();
        }

        for (level, file_id) in self.deleted_files.iter() {
            buf.write_varint(EditTag::DeletedFile as u32).unwrap();
            buf.write_varint(*level).unwrap();
            buf.write_varint(*file_id).unwrap();
        }

        for (level, file) in self.new_files.iter() {
            buf.write_varint(EditTag::NewFile as u32).unwrap();
            buf.write_varint(*level).unwrap();
            buf.write_varint(file.id).unwrap();
            buf.write_varint(file.size).unwrap();
            buf.write_varint(file.smallest.len()).unwrap();
            buf.write_all(&file.smallest).unwrap();
            buf.write_varint(file.largest.len()).unwrap();
            buf.write_all(&file.largest).unwrap();
        }

        buf
    }

    pub fn decode(mut src: &[u8]) -> Result<Self> {
        let mut res = Self::new();

        fn read_length_prefixed(src: &mut &[u8]) -> Result<Vec<u8>> {
            if let Ok(len) = src.read_varint() {
                let mut buf = vec![0; len];
                if let Ok(read_len) = src.read(&mut buf) {
                    if len == read_len {
                        return Ok(buf);
                    }
                }
            }
            err(StatusCode::IOError, "Failed to read length-prefixed data")
        }

        while let Ok(tag) = src.read_varint::<u32>() {
            let edit_tag = u32_to_tag(tag);
            if edit_tag.is_none() {
                return err(StatusCode::Corruption, &format!("Unknown tag: {}", tag));
            }
            match edit_tag.unwrap() {
                EditTag::Comparator => {
                    if let Ok(v) = String::from_utf8(read_length_prefixed(&mut src)?) {
                        res.comparator = Some(v);
                    } else {
                        return err(StatusCode::Corruption, "Failed to read comparator");
                    }
                }
                EditTag::LogID => {
                    if let Ok(v) = src.read_varint() {
                        res.log_id = Some(v);
                    } else {
                        return err(StatusCode::IOError, "Failed to read log ID");
                    }
                }
                EditTag::PreviousLogID => {
                    if let Ok(v) = src.read_varint() {
                        res.prev_log_id = Some(v);
                    } else {
                        return err(StatusCode::IOError, "Failed to read previous log ID");
                    }
                }
                EditTag::NextFileID => {
                    if let Ok(v) = src.read_varint() {
                        res.next_file_id = Some(v);
                    } else {
                        return err(StatusCode::IOError, "Failed to read next file ID");
                    }
                }
                EditTag::LastSequence => {
                    if let Ok(v) = src.read_varint() {
                        res.last_sequence = Some(v);
                    } else {
                        return err(StatusCode::IOError, "Failed to read last sequence");
                    }
                }
                EditTag::CompactPointer => {
                    if let Ok(v) = src.read_varint() {
                        res.compaction_pointers
                            .push((v, read_length_prefixed(&mut src)?))
                    } else {
                        return err(StatusCode::IOError, "Failed to read compact pointer");
                    }
                }
                EditTag::DeletedFile => {
                    if let Ok(level) = src.read_varint() {
                        if let Ok(file_id) = src.read_varint() {
                            res.deleted_files.insert((level, file_id));
                        } else {
                            return err(StatusCode::IOError, "Failed to read deleted file ID");
                        }
                    } else {
                        return err(StatusCode::IOError, "Failed to read deleted file level");
                    }
                }
                EditTag::NewFile => {
                    if let Ok(level) = src.read_varint() {
                        if let Ok(id) = src.read_varint() {
                            if let Ok(size) = src.read_varint() {
                                res.new_files.push((
                                    level,
                                    FileMetaData {
                                        allowed_seeks: 0,
                                        id,
                                        size,
                                        smallest: read_length_prefixed(&mut src)?,
                                        largest: read_length_prefixed(&mut src)?,
                                    },
                                ));
                            } else {
                                return err(StatusCode::IOError, "Failed to read new file size");
                            }
                        } else {
                            return err(StatusCode::IOError, "Failed to read new file ID");
                        }
                    } else {
                        return err(StatusCode::IOError, "Failed to read new file level");
                    }
                }
            }
        }

        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod test_version_set {
        use crate::{
            coredef::{cmp::DefaultCmp, key::LookupKey, types::DbIteratorWrapper},
            storage::version::testutil::make_version,
        };

        use super::*;
        use time_test::time_test;

        fn example_files() -> Vec<FileMetaHandle> {
            let mut f1 = FileMetaData::default();
            f1.id = 1;
            f1.size = 10;
            f1.smallest = "f".as_bytes().to_vec();
            f1.largest = "g".as_bytes().to_vec();
            let mut f2 = FileMetaData::default();
            f2.id = 2;
            f2.size = 20;
            f2.smallest = "e".as_bytes().to_vec();
            f2.largest = "f".as_bytes().to_vec();
            let mut f3 = FileMetaData::default();
            f3.id = 3;
            f3.size = 30;
            f3.smallest = "a".as_bytes().to_vec();
            f3.largest = "b".as_bytes().to_vec();
            let mut f4 = FileMetaData::default();
            f4.id = 4;
            f4.size = 40;
            f4.smallest = "q".as_bytes().to_vec();
            f4.largest = "z".as_bytes().to_vec();
            vec![f1, f2, f3, f4]
                .into_iter()
                .map(|f| Rc::new(RefCell::new(f)))
                .collect()
        }

        #[test]
        fn test_version_set_merge_iters() {
            let v1 = vec![2, 4, 6, 8, 10];
            let v2 = vec![1, 3, 5, 7];
            assert_eq!(
                vec![1, 2, 3, 4, 5, 6, 7, 8, 10],
                merge_iters(v1.into_iter(), v2.into_iter(), |a, b| a.cmp(&b))
            );
        }

        #[test]
        fn test_version_set_total_size() {
            assert_eq!(
                100,
                example_files()
                    .iter()
                    .map(|f| f.borrow().size)
                    .sum::<usize>()
            );
        }

        #[test]
        fn test_version_set_get_range() {
            let cmp = DefaultCmp;
            let fs = example_files();
            assert_eq!(
                ("a".as_bytes().to_vec(), "z".as_bytes().to_vec()),
                get_range(&cmp, fs.iter())
            );
        }

        #[test]
        fn test_version_set_builder() {
            let (v, opt) = make_version();
            let v = Rc::new(RefCell::new(v));

            let mut fmd = FileMetaData::default();
            fmd.id = 21;
            fmd.size = 123;
            fmd.smallest = LookupKey::new("klm".as_bytes(), 777)
                .internal_key()
                .to_vec();
            fmd.largest = LookupKey::new("kop".as_bytes(), 700)
                .internal_key()
                .to_vec();

            let mut ve = VersionEdit::new();
            ve.new_files.push((1, fmd));
            // This deletion should be undone by apply().
            ve.deleted_files.insert((1, 21));
            ve.deleted_files.insert((0, 2));
            ve.compaction_pointers.push((
                2,
                LookupKey::new("xxx".as_bytes(), 123)
                    .internal_key()
                    .to_vec(),
            ));

            let mut b = Builder::new();
            let mut ptrs: [Vec<u8>; NUM_LEVELS] = Default::default();
            b.apply(&ve, &mut ptrs);

            assert_eq!(
                &[120 as u8, 120, 120, 1, 123, 0, 0, 0, 0, 0, 0],
                ptrs[2].as_slice()
            );
            assert_eq!(2, b.deleted[0][0]);
            assert_eq!(1, b.added[1].len());

            let mut v2 = Version::new(
                Rc::new(RefCell::new(TableCache::new("db", opt.clone(), 100))),
                opt.cmp.clone(),
            );
            b.save_to(&InternalKeyCmp(opt.cmp.clone()), &v, &mut v2);
            // Second file in L0 was removed.
            assert_eq!(1, v2.files[0].len());
            // File was added to L1.
            assert_eq!(4, v2.files[1].len());
            assert_eq!(21, v2.files[1][3].borrow().id);
        }

        #[test]
        fn test_version_set_log_and_apply() {
            let (_, opt) = make_version();
            let mut vs = VersionSet::new(
                "db",
                opt.clone(),
                Rc::new(RefCell::new(TableCache::new("db", opt.clone(), 100))),
            );

            assert_eq!(2, vs.new_file_id());
            // Simulate NewDB
            {
                let mut ve = VersionEdit::new();
                ve.comparator = Some("rldb.DefaultCmp".to_string());
                ve.log_id = Some(10);
                ve.next_file_id = Some(20);
                ve.last_sequence = Some(30);

                // Write first manifest to be recovered from.
                let manifest = manifest_file_name("db", 19);
                let mffile = opt.env.open_writable_file(Path::new(&manifest)).unwrap();
                let mut lw = LogWriter::new(mffile);
                lw.add_record(&ve.encode()).unwrap();
                lw.flush().unwrap();
                set_current_file(opt.env.as_ref(), "db", 19).unwrap();
            }

            // Recover from new state.
            {
                vs.recover().unwrap();
                assert_eq!(10, vs.log_id);
                assert_eq!(21, vs.next_file_id);
                assert_eq!(30, vs.last_sequence);
                assert_eq!(0, vs.current.as_ref().unwrap().borrow().files[0].len());
                assert_eq!(0, vs.current.as_ref().unwrap().borrow().files[1].len());
                assert!(vs.write_snapshot().is_ok()); // todo
            }

            // Simulate compaction by adding a file.
            {
                let mut ve = VersionEdit::new();
                ve.log_id = Some(11);
                let mut fmd = FileMetaData::default();
                fmd.id = 21;
                fmd.size = 123;
                fmd.smallest = LookupKey::new("abc".as_bytes(), 777)
                    .internal_key()
                    .to_vec();
                fmd.largest = LookupKey::new("def".as_bytes(), 700)
                    .internal_key()
                    .to_vec();
                ve.new_files.push((1, fmd));
                vs.log_and_apply(ve).unwrap();

                assert!(opt.env.exists(&Path::new("db").join("CURRENT")).unwrap());
                assert!(opt
                    .env
                    .exists(&Path::new("db").join("MANIFEST-000019"))
                    .unwrap());
                // next_file_num and last_seq are untouched by log_and_apply
                assert_eq!(21, vs.new_file_id());
                assert_eq!(22, vs.next_file_id);
                assert_eq!(30, vs.last_sequence);
                // the following fields are touched by log_and_apply.
                assert_eq!(11, vs.log_id);

                // The previous "compaction" should have added one file to the first level in the
                // current version.
                assert_eq!(0, vs.current.as_ref().unwrap().borrow().files[0].len());
                assert_eq!(1, vs.current.as_ref().unwrap().borrow().files[1].len());
                // assert_eq!(63, vs.write_snapshot().unwrap()); todo
            }
        }

        #[test]
        fn test_version_set_utils() {
            let (v, opt) = make_version();
            let mut vs = VersionSet::new(
                "db",
                opt.clone(),
                Rc::new(RefCell::new(TableCache::new("db", opt, 100))),
            );
            vs.set_version(v);
            // active_files()
            assert_eq!(9, vs.active_files().len());
            assert!(vs.active_files().contains(&3));

            let v = vs.current();
            let v = v.borrow();
            // num_level_bytes()
            // assert_eq!(483, v.num_level_bytes(0));
            // assert_eq!(651, v.num_level_bytes(1));
            // assert_eq!(468, v.num_level_bytes(2));
            // num_level_files()
            assert_eq!(2, v.num_level_files(0));
            assert_eq!(3, v.num_level_files(1));
            assert_eq!(2, v.num_level_files(2));
            // new_file_id()
            assert_eq!(2, vs.new_file_id());
            assert_eq!(3, vs.new_file_id());
        }

        #[test]
        fn test_version_set_pick_compaction() {
            let (mut v, opt) = make_version();
            let mut vs = VersionSet::new(
                "db",
                opt.clone(),
                Rc::new(RefCell::new(TableCache::new("db", opt, 100))),
            );

            v.compaction_score = Some(2.0);
            v.compaction_level = Some(0);
            vs.set_version(v);

            // Size compaction
            {
                let c = vs.pick_compaction().unwrap();
                assert_eq!(2, c.inputs[0].len());
                assert_eq!(1, c.inputs[1].len());
                assert_eq!(0, c.level);
                assert!(c.version.is_some());
            }
            // Seek compaction
            {
                let current = vs.current();
                current.borrow_mut().compaction_score = None;
                current.borrow_mut().compaction_level = None;
                current.borrow_mut().file_to_compact_level = 1;

                let fmd = current.borrow().files[1][0].clone();
                current.borrow_mut().file_to_compact = Some(fmd);

                let c = vs.pick_compaction().unwrap();
                assert_eq!(3, c.inputs[0].len()); // inputs on l+0 are expanded.
                assert_eq!(1, c.inputs[1].len());
                assert_eq!(1, c.level);
                assert!(c.version.is_some());
            }
        }

        /// iterator_properties tests that it contains len elements and that they are ordered in
        /// ascending order by cmp.
        fn iterator_properties<It: DbIterator>(mut it: It, len: usize, cmp: Rc<Box<dyn Cmp>>) {
            let mut wr = DbIteratorWrapper::new(&mut it);
            let first = wr.next().unwrap();
            let mut count = 1;
            wr.fold(first, |(a, _), (b, c)| {
                assert_eq!(Ordering::Less, cmp.cmp(&a, &b));
                count += 1;
                (b, c)
            });
            assert_eq!(len, count);
        }

        #[test]
        fn test_version_set_compaction() {
            let (v, opt) = make_version();
            let mut vs = VersionSet::new(
                "db",
                opt.clone(),
                Rc::new(RefCell::new(TableCache::new("db", opt, 100))),
            );
            time_test!();
            vs.set_version(v);

            {
                // approx_offset()
                let v = vs.current();
                assert_eq!(
                    0,
                    vs.approx_offset(&v, LookupKey::new("aaa".as_bytes(), 9000).internal_key())
                );
                // assert_eq!(
                //     232,
                //     vs.approx_offset(&v, LookupKey::new("bab".as_bytes(), 9000).internal_key())
                // );
                // assert_eq!(
                //     1134,
                //     vs.approx_offset(&v, LookupKey::new("fab".as_bytes(), 9000).internal_key())
                // );
            }
            // The following tests reuse the same version set and verify that various compactions work
            // like they should.
            {
                time_test!("compaction tests");
                // compact level 0 with a partial range.
                let from = LookupKey::new("000".as_bytes(), 1000);
                let to = LookupKey::new("ab".as_bytes(), 1010);
                let c = vs
                    .compact_range(0, from.internal_key(), to.internal_key())
                    .unwrap();
                assert_eq!(2, c.inputs[0].len());
                assert_eq!(1, c.inputs[1].len());
                assert_eq!(1, c.grandparents.unwrap().len());

                // compact level 0, but entire range of keys in version.
                let from = LookupKey::new("000".as_bytes(), 1000);
                let to = LookupKey::new("zzz".as_bytes(), 1010);
                let c = vs
                    .compact_range(0, from.internal_key(), to.internal_key())
                    .unwrap();
                assert_eq!(2, c.inputs[0].len());
                assert_eq!(1, c.inputs[1].len());
                assert_eq!(1, c.grandparents.as_ref().unwrap().len());
                iterator_properties(
                    vs.make_input_iterator(&c),
                    12,
                    Rc::new(Box::new(vs.cmp.clone())),
                );

                // Expand input range on higher level.
                let from = LookupKey::new("dab".as_bytes(), 1000);
                let to = LookupKey::new("eab".as_bytes(), 1010);
                let c = vs
                    .compact_range(1, from.internal_key(), to.internal_key())
                    .unwrap();
                assert_eq!(3, c.inputs[0].len());
                assert_eq!(1, c.inputs[1].len());
                assert_eq!(0, c.grandparents.as_ref().unwrap().len());
                iterator_properties(
                    vs.make_input_iterator(&c),
                    12,
                    Rc::new(Box::new(vs.cmp.clone())),
                );

                // is_trivial_move
                let from = LookupKey::new("fab".as_bytes(), 1000);
                let to = LookupKey::new("fba".as_bytes(), 1010);
                let mut c = vs
                    .compact_range(2, from.internal_key(), to.internal_key())
                    .unwrap();
                // pretend it's not manual
                c.manual = false;
                assert!(c.is_trivial_move());

                // should_stop_before
                let from = LookupKey::new("000".as_bytes(), 1000);
                let to = LookupKey::new("zzz".as_bytes(), 1010);
                let mid = LookupKey::new("abc".as_bytes(), 1010);
                let mut c = vs
                    .compact_range(0, from.internal_key(), to.internal_key())
                    .unwrap();
                assert!(!c.should_stop_before(from.internal_key()));
                assert!(!c.should_stop_before(mid.internal_key()));
                assert!(!c.should_stop_before(to.internal_key()));

                // is_base_level_for
                let from = LookupKey::new("000".as_bytes(), 1000);
                let to = LookupKey::new("zzz".as_bytes(), 1010);
                let mut c = vs
                    .compact_range(0, from.internal_key(), to.internal_key())
                    .unwrap();
                assert!(c.is_base_level_for("aaa".as_bytes()));
                assert!(!c.is_base_level_for("hac".as_bytes()));

                // input/add_input_deletions
                let from = LookupKey::new("000".as_bytes(), 1000);
                let to = LookupKey::new("zzz".as_bytes(), 1010);
                let mut c = vs
                    .compact_range(0, from.internal_key(), to.internal_key())
                    .unwrap();
                for inp in &[(0, 0, 1), (0, 1, 2), (1, 0, 3)] {
                    let f = &c.inputs[inp.0][inp.1];
                    assert_eq!(inp.2, f.borrow().id);
                }
                c.delete_inputs();
                assert_eq!(23, c.edit().encode().len())
            }
        }
    }

    mod test_version_edit {
        use crate::coredef::cmp::DefaultCmp;

        use super::*;

        #[test]
        fn test_version_edit_encode_decode() {
            let mut ve = VersionEdit::new();

            ve.comparator = Some(DefaultCmp.name().to_string());
            ve.log_id = Some(123);
            ve.next_file_id = Some(456);
            ve.compaction_pointers.push((0, vec![0, 1, 2]));
            ve.compaction_pointers.push((1, vec![3, 4, 5]));
            ve.compaction_pointers.push((2, vec![6, 7, 8]));
            ve.new_files.push((
                0,
                FileMetaData {
                    allowed_seeks: 12345,
                    id: 901,
                    size: 234,
                    smallest: vec![5, 6, 7],
                    largest: vec![8, 9, 0],
                },
            ));
            ve.deleted_files.insert((1, 132));

            let encoded = ve.encode();

            let decoded = VersionEdit::decode(encoded.as_ref()).unwrap();

            assert_eq!(decoded.comparator, Some(DefaultCmp.name().to_string()));
            assert_eq!(decoded.log_id, Some(123));
            assert_eq!(decoded.next_file_id, Some(456));
            assert_eq!(decoded.compaction_pointers.len(), 3);
            assert_eq!(decoded.compaction_pointers[0], (0, vec![0, 1, 2]));
            assert_eq!(decoded.compaction_pointers[1], (1, vec![3, 4, 5]));
            assert_eq!(decoded.compaction_pointers[2], (2, vec![6, 7, 8]));
            assert_eq!(decoded.new_files.len(), 1);
            assert_eq!(
                decoded.new_files[0],
                (
                    0,
                    FileMetaData {
                        allowed_seeks: 0,
                        id: 901,
                        size: 234,
                        smallest: vec![5, 6, 7],
                        largest: vec![8, 9, 0],
                    }
                )
            );
            assert_eq!(decoded.deleted_files.len(), 1);
            assert!(decoded.deleted_files.contains(&(1, 132)));
        }
    }
}
