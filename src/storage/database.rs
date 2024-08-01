use std::{
    cell::RefCell,
    cmp::Ordering,
    io::{BufWriter, Write},
    ops::AddAssign,
    path::{Path, PathBuf},
    rc::Rc,
};

use crate::coredef::{
    cmp::{Cmp, InternalKeyCmp},
    env::{Env, FileLock},
    error::{err, Result, StatusCode},
    key::{parse_internal_key, LookupKey, ValueType},
    log::{LogReader, LogWriter, Logger},
    options::Options,
    types::{
        parse_file_name, DbIterator, FileID, FileMetaData, FileType, MergingIterator, SeqNum,
        MAX_SEQNUM,
    },
    NUM_LEVELS,
};
use crate::log;
use crate::storage::{
    database_iter::DatabaseIter,
    memtable::Memtable,
    snapshot::{Snapshot, SnapshotList},
    table::{TableBuilder, TableCache},
    version::Version,
    version_set::{
        manifest_file_name, read_current_file, set_current_file, Compaction, VersionEdit,
        VersionSet,
    },
    write_batch::WriteBatch,
};
use crate::utils::filter::{FilterPolicy, InternalKeyFilterPolicy};

/// Compactions Statistics
#[derive(Default)]
struct CompStats {
    micros: u64,
    bytes_read: usize,
    bytes_written: usize,
}

impl AddAssign for CompStats {
    fn add_assign(&mut self, rhs: Self) {
        self.micros += rhs.micros;
        self.bytes_read += rhs.bytes_read;
        self.bytes_written += rhs.bytes_written;
    }
}

/// Compaction State
struct CompState {
    compaction: Compaction,
    smallest_seqnum: SeqNum,
    outputs: Vec<FileMetaData>,
    builder: Option<TableBuilder<Box<dyn Write>>>,
    total_bytes: usize,
}

impl CompState {
    fn new(compaction: Compaction, smallest_seqnum: SeqNum) -> Self {
        Self {
            compaction,
            smallest_seqnum,
            outputs: Vec::new(),
            builder: None,
            total_bytes: 0,
        }
    }

    fn current_output(&mut self) -> &mut FileMetaData {
        self.outputs.last_mut().unwrap()
    }

    fn cleanup(&mut self, env: &dyn Env, name: impl AsRef<Path>) {
        for f in self.outputs.drain(..) {
            let _ = env.delete(&TableCache::table_file_name(name.as_ref(), f.id));
        }
    }
}

/// Returns /dev/null when fails.
fn open_info_log(env: &dyn Env, p: impl AsRef<Path>) -> Logger {
    let p = p.as_ref();
    let log_file_name = p.join("LOG");
    let old_file_name = p.join("LOG.old");
    let _ = env.mkdir(Path::new(p));
    if env.exists(&log_file_name).is_ok_and(|e| e) {
        let _ = env.rename(&log_file_name, &old_file_name);
    }
    Logger(
        env.open_writable_file(&log_file_name)
            .unwrap_or(Box::new(std::io::sink())),
    )
}

#[allow(dead_code)]
pub struct Database {
    name: PathBuf,
    path: PathBuf,
    lock: Option<FileLock>,

    icmp: Rc<dyn Cmp>,
    policy: InternalKeyFilterPolicy<Rc<dyn FilterPolicy>>,
    options: Options,

    mem: Memtable,
    imm: Option<Memtable>,

    log: Option<LogWriter<BufWriter<Box<dyn Write>>>>,
    log_id: Option<FileID>,
    cache: Rc<RefCell<TableCache>>,
    version_set: Rc<RefCell<VersionSet>>,
    snapshots: SnapshotList,

    cstats: [CompStats; NUM_LEVELS],
}

impl Database {
    // INITIALIZATION / RECOVER

    fn new(name: impl AsRef<Path>, mut options: Options) -> Self {
        let name = name.as_ref();
        if options.log.is_none() {
            options.log = Some(Rc::new(RefCell::new(open_info_log(
                options.env.as_ref(),
                name,
            ))));
        }
        let cache = Rc::new(RefCell::new(TableCache::new(
            name,
            options.clone(),
            options.max_open_files - 10,
        )));

        Self {
            name: name.to_owned(),
            path: name.canonicalize().unwrap_or(name.to_owned()),
            lock: None,

            icmp: Rc::new(InternalKeyCmp(options.cmp.clone())),
            policy: InternalKeyFilterPolicy::new(options.filter_policy.clone()),
            options: options.clone(),

            mem: Memtable::new(options.cmp.clone()),
            imm: None,

            log: None,
            log_id: None,
            cache: cache.clone(),
            version_set: Rc::new(RefCell::new(VersionSet::new(name, options, cache))),
            snapshots: SnapshotList::new(),

            cstats: Default::default(),
        }
    }

    fn current(&self) -> Rc<RefCell<Version>> {
        self.version_set.borrow().current()
    }

    /// Opens / creates a database. `name` is the name of the directory containing the database.
    pub fn open(name: impl AsRef<Path>, options: Options) -> Result<Self> {
        let name = name.as_ref();
        let mut db = Self::new(name, options);
        let mut ve = VersionEdit::new();
        let save_manifest = db.recover(&mut ve)?;

        if db.log.is_none() {
            let log_id = db.version_set.borrow_mut().new_file_id();
            let log_file = db
                .options
                .env
                .open_writable_file(&log_file_name(name, log_id))?;
            ve.log_id = Some(log_id);
            db.log = Some(LogWriter::new(BufWriter::new(log_file)));
            db.log_id = Some(log_id);
        }

        if save_manifest {
            ve.log_id = Some(db.log_id.unwrap_or_default());
            db.version_set.borrow_mut().log_and_apply(ve)?;
        }

        db.delete_obsolete_files()?;
        db.try_compaction()?;
        Ok(db)
    }

    fn initialize(&mut self) -> Result<()> {
        let mut ve = VersionEdit::new();
        ve.comparator = Some(self.options.cmp.name().to_string());
        ve.log_id = Some(0);
        ve.next_file_id = Some(2);
        ve.last_sequence = Some(0);

        {
            let manifest = manifest_file_name(&self.path, 1);
            let manifest_file = self.options.env.open_writable_file(&manifest)?;
            let mut log = LogWriter::new(manifest_file);
            log.add_record(&ve.encode())?;
            log.flush()?;
        }

        set_current_file(self.options.env.as_ref(), &self.path, 1)
    }

    // log_and_apply should be called after recovery
    fn recover(&mut self, ve: &mut VersionEdit) -> Result<bool> {
        if self.options.error_if_exists
            && self.options.env.exists(self.path.as_ref()).unwrap_or(false)
        {
            return err(StatusCode::AlreadyExists, "database already exists");
        }

        let _ = self.options.env.mkdir(Path::new(&self.path));
        self.acquire_lock()?;

        if let Err(e) = read_current_file(self.options.env.as_ref(), &self.path) {
            if e.code == StatusCode::NotFound && self.options.create_if_missing {
                self.initialize()?;
            } else {
                return err(
                    StatusCode::InvalidArgument,
                    "database does not exist and create_if_missing is false",
                );
            }
        }

        let mut save_manifest = self.version_set.borrow_mut().recover()?;
        let mut max_seqnum = 0;
        let filenames = self.options.env.children(&self.path)?;
        let mut expected = self.version_set.borrow().active_files();
        let mut log_files = vec![];

        for file in &filenames {
            match parse_file_name(file.as_path().to_str().unwrap()) {
                Ok((id, t)) => {
                    expected.remove(&id);
                    if t == FileType::Log
                        && (id >= self.version_set.borrow().log_id
                            || id == self.version_set.borrow().previous_log_id)
                    {
                        log_files.push(id);
                    }
                }
                Err(e) => return Err(e),
            }
        }
        if !expected.is_empty() {
            log!(
                self.options.log,
                "Missing at least these files: {:?}",
                expected
            );
            return err(StatusCode::Corruption, "missing live files (see log)");
        }

        log_files.sort();
        for i in 0..log_files.len() {
            let (save, seqnum) =
                self.recover_log_file(log_files[i], i == log_files.len() - 1, ve)?;
            save_manifest |= save;
            max_seqnum = max_seqnum.max(seqnum);
            self.version_set.borrow_mut().skip_file_id(log_files[i]);
        }

        if self.version_set.borrow().last_sequence < max_seqnum {
            self.version_set.borrow_mut().last_sequence = max_seqnum;
        }

        Ok(save_manifest)
    }

    /// recover_log_file reads a single log file into a memtable, writing new L0 tables if
    /// necessary. If is_last is true, it checks whether the log file can be reused, and sets up
    /// the database's logging handles appropriately if that's the case.
    fn recover_log_file(
        &mut self,
        log_id: FileID,
        is_last: bool,
        ve: &mut VersionEdit,
    ) -> Result<(bool, SeqNum)> {
        let filename = log_file_name(&self.path, log_id);
        let log_file = self.options.env.open_sequential_file(filename.as_path())?;
        let cmp: Rc<dyn Cmp> = self.options.cmp.clone();

        let mut logreader = LogReader::new(log_file, true);
        log!(self.options.log, "Recovering log file {:?}", filename);
        let mut scratch = Vec::new();
        let mut mem = Memtable::new(cmp.clone());
        let mut batch = WriteBatch::new();

        let mut compactions = 0;
        let mut max_seqnum = 0;
        let mut save_manifest = false;

        while let Ok(flag) = logreader.read(&mut scratch) {
            if !flag {
                break;
            }
            // if len < 12 {
            //     log!(
            //         self.options.log,
            //         "corruption in log file {:06}: record shorter than 12B",
            //         log_num
            //     );
            //     continue;
            // }

            batch.set_entries(&scratch);
            batch.apply(batch.seq_num(), &mut mem);

            let last_seqnum = batch.seq_num() + batch.count() as u64 - 1;
            if last_seqnum > max_seqnum {
                max_seqnum = last_seqnum
            }
            if mem.approx_size() > self.options.write_buffer_size {
                compactions += 1;
                self.write_l0_table(&mem, ve, None)?;
                save_manifest = true;
                mem = Memtable::new(cmp.clone());
            }
            batch.clear();
        }

        if self.options.reuse_logs && is_last && compactions == 0 {
            assert!(self.log.is_none());
            log!(self.options.log, "reusing log file {:?}", filename);
            let oldsize = self.options.env.size_of(Path::new(&filename))?;
            let oldfile = self
                .options
                .env
                .open_appendable_file(Path::new(&filename))?;
            self.log = Some(LogWriter::new_with_offset(BufWriter::new(oldfile), oldsize));
            self.log_id = Some(log_id);
            self.mem = mem;
        } else if mem.len() > 0 {
            save_manifest = true;
            self.write_l0_table(&mem, ve, None)?;
        }

        Ok((save_manifest, max_seqnum))
    }

    /// delete_obsolete_files removes files that are no longer needed from the file system.
    fn delete_obsolete_files(&mut self) -> Result<()> {
        let files = self.version_set.borrow().active_files();
        let filenames = self.options.env.children(&self.path)?;
        for name in filenames {
            if let Ok((id, t)) = parse_file_name(name.as_path().to_str().unwrap()) {
                match t {
                    FileType::Log => {
                        if id >= self.version_set.borrow().log_id {
                            continue;
                        }
                    }
                    FileType::Descriptor => {
                        if id >= self.version_set.borrow().manifest_id {
                            continue;
                        }
                    }
                    FileType::Table => {
                        if files.contains(&id) {
                            continue;
                        }
                    }
                    FileType::Temp => {
                        if files.contains(&id) {
                            continue;
                        }
                    }
                    _ => continue,
                }

                if t == FileType::Table {
                    let _ = self.cache.borrow_mut().evict(id);
                }
                log!(self.options.log, "Deleting file type={:?} id={}", t, id);
                if let Err(e) = self.options.env.delete(&self.path.join(&name)) {
                    log!(self.options.log, "Deleting file id={} failed: {}", id, e);
                }
            }
        }
        Ok(())
    }

    fn acquire_lock(&mut self) -> Result<()> {
        match self.options.env.lock(&self.path.join("LOCK")) {
            Ok(lock) => {
                self.lock = Some(lock);
                Ok(())
            }
            Err(e) => Err(e),
        }
    }

    fn release_lock(&mut self) -> Result<()> {
        if let Some(lock) = self.lock.take() {
            self.options.env.unlock(lock)
        } else {
            Ok(())
        }
    }

    pub fn close(&mut self) -> Result<()> {
        self.flush()?;
        self.release_lock()
    }

    // WRITE

    pub fn insert(&mut self, key: &[u8], value: &[u8]) -> Result<()> {
        let mut batch = WriteBatch::new();
        batch.add(key, value);
        self.write(batch, false)
    }

    pub fn delete(&mut self, key: &[u8]) -> Result<()> {
        let mut batch = WriteBatch::new();
        batch.delete(key);
        self.write(batch, false)
    }

    pub fn write(&mut self, batch: WriteBatch, flush: bool) -> Result<()> {
        assert!(self.log.is_some());

        self.make_room_for_write(false)?;

        let entries = batch.count() as u64;
        let log = self.log.as_mut().unwrap();
        let next = self.version_set.borrow().last_sequence + 1;

        batch.apply(next, &mut self.mem);
        log.add_record(&batch.encode(next))?;
        if flush {
            log.flush()?;
        }
        self.version_set.borrow_mut().last_sequence += entries;
        Ok(())
    }

    pub fn flush(&mut self) -> Result<()> {
        if let Some(log) = self.log.as_mut() {
            log.flush()?;
        }
        Ok(())
    }

    // READ

    fn get_internal(&mut self, seqnum: SeqNum, key: &[u8]) -> Result<Option<Vec<u8>>> {
        let key = LookupKey::new(key, seqnum);

        match self.mem.get(&key) {
            (Some(v), _) => return Ok(Some(v)),
            (None, true) => return Ok(None),
            (None, false) => {}
        }

        if let Some(imm) = self.imm.as_ref() {
            match imm.get(&key) {
                (Some(v), _) => return Ok(Some(v)),
                (None, true) => return Ok(None),
                (None, false) => {}
            }
        }

        let mut compact = false;
        let mut value = None;

        {
            let current = self.current();
            let mut current = current.borrow_mut();
            if let Ok(Some((v, stats))) = current.get(key.internal_key()) {
                compact |= current.update_stats(stats);
                value = Some(v)
            }
        }

        if compact {
            if let Err(e) = self.try_compaction() {
                log!(self.options.log, "error compaction in get: {}", e);
            }
        }
        Ok(value)
    }

    /// get the value at specified snapshot
    pub fn get_at(&mut self, snapshot: &Snapshot, key: &[u8]) -> Result<Option<Vec<u8>>> {
        self.get_internal(snapshot.seqnum(), key)
    }

    /// get the value at the latest snapshot
    pub fn get(&mut self, key: &[u8]) -> Option<Vec<u8>> {
        let seqnum = self.version_set.borrow().last_sequence;
        self.get_internal(seqnum, key).ok()?
    }

    // SNAPSHOT

    pub fn get_snapshot(&mut self) -> Snapshot {
        self.snapshots
            .new_snapshot(self.version_set.borrow().last_sequence)
    }

    // ITERATOR

    /// Creates a new iterator at the specified snapshot.
    pub fn new_iter_at(&mut self, snapshot: Snapshot) -> Result<DatabaseIter> {
        Ok(DatabaseIter::new(
            self.options.cmp.clone(),
            self.version_set.clone(),
            self.merge_iterator()?,
            snapshot,
        ))
    }

    pub fn new_iter(&mut self) -> Result<DatabaseIter> {
        let snapshot = self.get_snapshot();
        self.new_iter_at(snapshot)
    }

    fn merge_iterator(&mut self) -> Result<MergingIterator> {
        let mut iters: Vec<Box<dyn DbIterator>> = Vec::new();

        if self.mem.len() > 0 {
            iters.push(Box::new(self.mem.iter()));
        }
        if let Some(imm) = self.imm.as_ref() {
            if imm.len() > 0 {
                iters.push(Box::new(imm.iter()));
            }
        }

        iters.extend(self.current().borrow().new_iters()?);
        Ok(MergingIterator::new(self.icmp.clone(), iters))
    }

    // COMPACTION

    fn try_compaction(&mut self) -> Result<()> {
        if self.imm.is_some() {
            self.compact_memtable()?;
        }
        if self.version_set.borrow().needs_compaction() {
            let c = self.version_set.borrow_mut().pick_compaction();
            if let Some(c) = c {
                return self.start_compaction(c);
            }
        }
        Ok(())
    }

    fn start_compaction(&mut self, mut c: Compaction) -> Result<()> {
        if c.is_trivial_move() {
            assert_eq!(1, c.num_inputs(0));
            let f = c.input(0, 0);
            let id = f.id;
            let level = c.level();

            c.edit().deleted_files.insert((level, id));
            c.edit().new_files.push((level + 1, f));

            return self.version_set.borrow_mut().log_and_apply(c.into_edit());
            // let r = self.version_set.borrow_mut().log_and_apply(c.into_edit());
            // if let Err(e) = r {
            //     log!(self.options.log, "trivial move failed: {}", e);
            //     Err(e)
            // } else {
            // log!(
            //     self.options.log,
            //     "Moved id={} bytes={} from L{} to L{}",
            //     id,
            //     size,
            //     level,
            //     level + 1
            // );
            // log!(
            //     self.options.log,
            //     "Summary: {}",
            //     self.version_set.borrow().current_summary()
            // );
            //     Ok(())
            // }
        }

        let smallest = if self.snapshots.empty() {
            self.version_set.borrow().last_sequence
        } else {
            self.snapshots.oldest().1
        };

        let mut state = CompState::new(c, smallest);

        if let Err(e) = self.compact(&mut state) {
            state.cleanup(self.options.env.as_ref(), &self.path);
            log!(self.options.log, "Compaction work failed: {}", e);
        }
        self.apply_compaction_results(state)?;
        // log!(
        //     self.options.log,
        //     "Compaction finished: {}",
        //     self.version_set.borrow().current_summary()
        // );

        self.delete_obsolete_files()
    }

    fn compact_memtable(&mut self) -> Result<()> {
        let mut ve = VersionEdit::new();
        let base = self.current();
        let imm = self.imm.take().unwrap();

        if let Err(e) = self.write_l0_table(&imm, &mut ve, Some(&base.borrow())) {
            self.imm = Some(imm);
            return Err(e);
        }

        ve.log_id = Some(self.log_id.unwrap_or_default());
        self.version_set.borrow_mut().log_and_apply(ve)?;
        // if let Err(e) = self.delete_obsolete_files() {
        //     log!(self.options.log, "Error deleting obsolete files: {}", e);
        // }
        // Ok(())
        self.delete_obsolete_files()
    }

    fn write_l0_table(
        &mut self,
        mem: &Memtable,
        ve: &mut VersionEdit,
        base: Option<&Version>,
    ) -> Result<()> {
        let start_micros = self.options.env.micros();
        let id = self.version_set.borrow_mut().new_file_id();
        log!(self.options.log, "Start write of L0 table {:06}", id);

        let file = build_table(&self.path, &self.options, mem.iter(), id)?;
        log!(
            self.options.log,
            "L0 table {:06} has {} bytes",
            id,
            file.size
        );

        if file.size == 0 {
            self.version_set.borrow_mut().reuse_file_id(id);
            return Ok(());
        }

        if let Err(e) = self.cache.borrow_mut().get_table(id) {
            log!(
                self.options.log,
                "L0 table {:06} not returned by cache: {}",
                id,
                e
            );
            let _ = self
                .options
                .env
                .delete(&TableCache::table_file_name(&self.path, id));
            return Err(e);
        }

        let stats = CompStats {
            micros: self.options.env.micros() - start_micros,
            bytes_read: 0,
            bytes_written: file.size,
        };
        let level = base.map_or(0, |v| {
            v.pick_memtable_output_level(
                parse_internal_key(&file.smallest).2,
                parse_internal_key(&file.largest).2,
            )
        });

        self.cstats[level] += stats;
        ve.new_files.push((level, file));

        Ok(())
    }

    /// Checks memtable and triggers a compaction if necessary.
    fn make_room_for_write(&mut self, force: bool) -> Result<()> {
        if !force && self.mem.approx_size() < self.options.write_buffer_size || self.mem.len() == 0
        {
            return Ok(());
        }

        // Create new memtable.
        let log_id = self.version_set.borrow_mut().new_file_id();
        let log_file = self
            .options
            .env
            .open_writable_file(Path::new(&log_file_name(&self.path, log_id)));
        if log_file.is_err() {
            self.version_set.borrow_mut().reuse_file_id(log_id);
            return Err(log_file.err().unwrap());
        }

        self.log = Some(LogWriter::new(BufWriter::new(log_file.unwrap())));
        self.log_id = Some(log_id);

        let mut imm = Memtable::new(self.options.cmp.clone());
        std::mem::swap(&mut imm, &mut self.mem);
        self.imm = Some(imm);
        self.try_compaction()
    }

    fn compact(&mut self, cs: &mut CompState) -> Result<()> {
        // {
        //     let current = self.version_set.borrow().current();
        //     assert!(current.borrow().num_level_files(cs.compaction.level()) > 0);
        //     assert!(cs.builder.is_none());
        // }
        let start_micros = self.options.env.micros();
        log!(
            self.options.log,
            "Compacting {} files at L{} and {} files at L{}",
            cs.compaction.num_inputs(0),
            cs.compaction.level(),
            cs.compaction.num_inputs(1),
            cs.compaction.level() + 1
        );

        let mut iter = self
            .version_set
            .borrow()
            .make_input_iterator(&cs.compaction);
        iter.seek_to_first();

        let mut key = Vec::new();
        let mut value = Vec::new();
        let mut last_seq_for_key = MAX_SEQNUM;

        let mut have_ukey = false;
        let mut current_ukey = Vec::new();

        while iter.valid() {
            assert!(iter.current(&mut key, &mut value));
            if cs.compaction.should_stop_before(&key) && cs.builder.is_some() {
                self.finish_compaction_output(cs)?;
            }
            let (key_type, seqnum, ukey) = parse_internal_key(&key);
            if seqnum == 0 {
                log!(self.options.log, "Encountered seq=0 in key: {:?}", &key);
                last_seq_for_key = MAX_SEQNUM;
                have_ukey = false;
                current_ukey.clear();
                iter.advance();
                continue;
            }

            if !have_ukey || self.options.cmp.cmp(ukey, &current_ukey) != Ordering::Equal {
                current_ukey.clear();
                current_ukey.extend_from_slice(ukey);
                have_ukey = true;
                last_seq_for_key = MAX_SEQNUM;
            }

            // We can omit the key under the following conditions:
            if last_seq_for_key <= cs.smallest_seqnum {
                last_seq_for_key = seqnum;
                iter.advance();
                continue;
            }

            if key_type == ValueType::TypeDeletion
                && seqnum <= cs.smallest_seqnum
                && cs.compaction.is_base_level_for(ukey)
            {
                last_seq_for_key = seqnum;
                iter.advance();
                continue;
            }

            last_seq_for_key = seqnum;

            if cs.builder.is_none() {
                let file_id = self.version_set.borrow_mut().new_file_id();
                let file = FileMetaData {
                    id: file_id,
                    ..Default::default()
                };

                let f =
                    Box::new(BufWriter::new(self.options.env.open_writable_file(
                        &TableCache::table_file_name(&self.path, file_id),
                    )?));
                cs.builder = Some(TableBuilder::new(self.options.clone(), f));
                cs.outputs.push(file);
            }
            if cs.builder.as_ref().unwrap().num_entries() == 0 {
                cs.current_output().smallest = key.clone();
            }

            cs.current_output().largest = key.clone();
            cs.builder.as_mut().unwrap().add(&key, &value)?;
            if cs.builder.as_ref().unwrap().estimate_size() > self.options.max_file_size {
                self.finish_compaction_output(cs)?;
            }

            iter.advance();
        }

        if cs.builder.is_some() {
            self.finish_compaction_output(cs)?;
        }

        let mut stats = CompStats {
            micros: self.options.env.micros() - start_micros,
            bytes_read: 0,
            bytes_written: 0,
        };

        for parent in 0..2 {
            for input in 0..cs.compaction.num_inputs(parent) {
                stats.bytes_read += cs.compaction.input(parent, input).size;
            }
        }
        for output in &cs.outputs {
            stats.bytes_written += output.size;
        }

        self.cstats[cs.compaction.level()] += stats;
        Ok(())
    }

    fn finish_compaction_output(&mut self, cs: &mut CompState) -> Result<()> {
        let output_id = cs.current_output().id;
        assert!(output_id > 0);

        let builder = cs.builder.take().unwrap();
        let entries = builder.num_entries();
        let bytes = builder.build()?;
        cs.total_bytes += bytes;
        cs.current_output().size = bytes;

        if entries > 0 {
            if let Err(e) = self.cache.borrow_mut().get_table(output_id) {
                log!(self.options.log, "New table can't be read: {}", e);
                return Err(e);
            }
            log!(
                self.options.log,
                "New table id={}: keys={} size={}",
                output_id,
                entries,
                bytes
            );
        }
        Ok(())
    }

    fn apply_compaction_results(&mut self, mut cs: CompState) -> Result<()> {
        log!(
            self.options.log,
            "Compacted {} L{} files + {} L{} files => {}B",
            cs.compaction.num_inputs(0),
            cs.compaction.level(),
            cs.compaction.num_inputs(1),
            cs.compaction.level() + 1,
            cs.total_bytes
        );

        cs.compaction.delete_inputs();
        let level = cs.compaction.level();
        for output in &cs.outputs {
            cs.compaction
                .edit()
                .new_files
                .push((level + 1, output.clone()));
        }

        self.version_set
            .borrow_mut()
            .log_and_apply(cs.compaction.into_edit())
    }

    /// Compacts on the specified key range.
    pub fn compact_range(&mut self, from: &[u8], to: &[u8]) -> Result<()> {
        let mut max_level = 1;
        {
            let v = self.version_set.borrow().current();
            let v = v.borrow();
            for level in 2..NUM_LEVELS - 1 {
                if v.overlaps_in_level(level, from, to) {
                    max_level = level;
                }
            }
        }

        self.make_room_for_write(true)?;
        let mut begin = LookupKey::new(from, MAX_SEQNUM).internal_key().to_vec();
        let end = LookupKey::new_with_type(to, 0, ValueType::TypeDeletion);

        for level in 0..max_level + 1 {
            loop {
                let c =
                    self.version_set
                        .borrow_mut()
                        .compact_range(level, &begin, end.internal_key());
                if let Some(c) = c {
                    begin = c.input(0, c.num_inputs(0) - 1).largest.clone();
                    self.start_compaction(c)?;
                } else {
                    break;
                }
            }
        }
        Ok(())
    }
}

unsafe impl Send for Database {}

impl Drop for Database {
    fn drop(&mut self) {
        let _ = self.flush();
        let _ = self.release_lock();
    }
}

pub fn build_table(
    name: impl AsRef<Path>,
    options: &Options,
    mut iter: impl DbIterator,
    id: FileID,
) -> Result<FileMetaData> {
    iter.reset();
    let filename = TableCache::table_file_name(name.as_ref(), id);

    let mut key_buf = Vec::new();
    let mut value_buf = Vec::new();
    let mut firstkey = None;

    let r = (|| -> Result<()> {
        let f = BufWriter::new(options.env.open_writable_file(&filename)?);
        let mut builder = TableBuilder::new(options.clone(), f);
        while iter.advance() {
            assert!(iter.current(&mut key_buf, &mut value_buf));
            if firstkey.is_none() {
                firstkey = Some(key_buf.clone());
            }
            builder.add(&key_buf, &value_buf)?;
        }
        builder.build()?;
        Ok(())
    })();

    if let Err(e) = r {
        let _ = options.env.delete(&filename);
        return Err(e);
    }

    let mut file = FileMetaData::default();
    match firstkey {
        None => {
            let _ = options.env.delete(&filename);
        }
        Some(key) => {
            file.id = id;
            file.size = options.env.size_of(&filename)?;
            file.smallest = key;
            file.largest = key_buf;
        }
    }
    Ok(file)
}

fn log_file_name(path: &Path, id: FileID) -> PathBuf {
    path.join(format!("{:06}.log", id))
}

#[cfg(test)]
pub mod testutil {
    use crate::storage::version::testutil::make_version;

    use super::*;

    /// build_db creates a database filled with the tables created by make_version().
    pub fn build_db() -> (Database, Options) {
        let name = "db";
        let (v, mut options) = make_version();
        options.reuse_logs = false;
        options.reuse_manifest = false;
        let mut ve = VersionEdit::new();
        ve.comparator = Some(options.cmp.name().to_string());
        ve.log_id = Some(0);
        // 9 files + 1 manifest we write below.
        ve.next_file_id = Some(11);
        // 30 entries in these tables.
        ve.last_sequence = Some(30);

        for l in 0..NUM_LEVELS {
            for f in &v.files[l] {
                ve.new_files.push((l, f.borrow().clone()));
            }
        }

        let manifest = manifest_file_name(name, 10);
        let manifest_file = options
            .env
            .open_writable_file(Path::new(&manifest))
            .unwrap();
        let mut lw = LogWriter::new(manifest_file);
        lw.add_record(&ve.encode()).unwrap();
        lw.flush().unwrap();
        set_current_file(options.env.as_ref(), name, 10).unwrap();

        (Database::open(name, options.clone()).unwrap(), options)
    }

    /// set_file_to_compact ensures that the specified table file will be compacted next.
    pub fn set_file_to_compact(db: &mut Database, num: FileID) {
        let v = db.current();
        let mut v = v.borrow_mut();

        let mut ftc = None;
        for l in 0..NUM_LEVELS {
            for f in &v.files[l] {
                if f.borrow().id == num {
                    ftc = Some((f.clone(), l));
                }
            }
        }
        if let Some((f, l)) = ftc {
            v.file_to_compact = Some(f);
            v.file_to_compact_level = l;
        } else {
            panic!("file number not found");
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::coredef::env::mem_env::MemEnv;
    use crate::coredef::error::Status;
    use crate::coredef::types::DbIteratorWrapper;
    use crate::storage::version::testutil::make_version;

    use super::testutil::{build_db, set_file_to_compact};
    use super::*;

    #[test]
    fn test_db_impl_open_info_log() {
        let e = MemEnv::new();
        {
            let l = Some(Rc::new(RefCell::new(open_info_log(&e, "abc"))));
            assert!(e.exists(&Path::new("abc").join("LOG")).unwrap());
            log!(l, "hello {}", "world");
            assert_eq!(12, e.size_of(&Path::new("abc").join("LOG")).unwrap());
        }
        {
            let l = Some(Rc::new(RefCell::new(open_info_log(&e, "abc"))));
            assert!(e.exists(&Path::new("abc").join("LOG.old")).unwrap());
            assert!(e.exists(&Path::new("abc").join("LOG")).unwrap());
            assert_eq!(12, e.size_of(&Path::new("abc").join("LOG.old")).unwrap());
            assert_eq!(0, e.size_of(&Path::new("abc").join("LOG")).unwrap());
            log!(l, "something else");
            log!(l, "and another {}", 1);

            let mut s = String::new();
            let mut r = e
                .open_sequential_file(&Path::new("abc").join("LOG"))
                .unwrap();
            r.read_to_string(&mut s).unwrap();
            assert_eq!("something else\nand another 1\n", &s);
        }
    }

    fn build_memtable() -> Memtable {
        let mut mt = Memtable::new(Options::for_test().cmp);
        let mut i = 1;
        for k in ["abc", "def", "ghi", "jkl", "mno", "aabc", "test123"].iter() {
            mt.add(
                k.as_bytes(),
                "looooongval".as_bytes(),
                ValueType::TypeValue,
                i,
            );
            i += 1;
        }
        mt
    }

    #[test]
    fn test_db_impl_init() {
        // A sanity check for recovery and basic persistence.
        let options = Options::for_test();
        let env = options.env.clone();

        // Several test cases with different options follow. The printlns can eventually be
        // removed.

        {
            let mut options = options.clone();
            options.reuse_manifest = false;
            let _ = Database::open("otherdb", options.clone()).unwrap();

            eprintln!(
                "children after: {:?}",
                env.children(Path::new("otherdb")).unwrap()
            );
            assert!(env.exists(&Path::new("otherdb").join("CURRENT")).unwrap());
            // Database is initialized and initial manifest reused.
            assert!(!env
                .exists(&Path::new("otherdb").join("MANIFEST-000001"))
                .unwrap());
            assert!(env
                .exists(&Path::new("otherdb").join("MANIFEST-000002"))
                .unwrap());
            assert!(env
                .exists(&Path::new("otherdb").join("000003.log"))
                .unwrap());
        }

        {
            let mut options = options.clone();
            options.reuse_manifest = true;
            let mut db = Database::open("db", options.clone()).unwrap();

            eprintln!(
                "children after: {:?}",
                env.children(&Path::new("db").join("")).unwrap()
            );
            assert!(env.exists(&Path::new("db").join("CURRENT")).unwrap());
            // Database is initialized and initial manifest reused.
            assert!(env
                .exists(&Path::new("db").join("MANIFEST-000001"))
                .unwrap());
            assert!(env.exists(&Path::new("db").join("LOCK")).unwrap());
            assert!(env.exists(&Path::new("db").join("000003.log")).unwrap());

            db.insert("abc".as_bytes(), "def".as_bytes()).unwrap();
            db.insert("abd".as_bytes(), "def".as_bytes()).unwrap();
        }

        {
            eprintln!(
                "children before: {:?}",
                env.children(&Path::new("db").join("")).unwrap()
            );
            let mut options = options.clone();
            options.reuse_manifest = false;
            options.reuse_logs = false;
            let mut db = Database::open("db", options.clone()).unwrap();

            eprintln!(
                "children after: {:?}",
                env.children(&Path::new("db").join("")).unwrap()
            );
            // Obsolete manifest is deleted.
            assert!(!env
                .exists(&Path::new("db").join("MANIFEST-000001"))
                .unwrap());
            // New manifest is created.
            assert!(env
                .exists(&Path::new("db").join("MANIFEST-000002"))
                .unwrap());
            // Obsolete log file is deleted.
            assert!(!env.exists(&Path::new("db").join("000003.log")).unwrap());
            // New L0 table has been added.
            assert!(env.exists(&Path::new("db").join("000003.ldb")).unwrap());
            assert!(env.exists(&Path::new("db").join("000004.log")).unwrap());
            // Check that entry exists and is correct. Phew, long call chain!
            let current = db.current();
            log!(options.log, "files: {:?}", current.borrow().files);
            assert_eq!(
                "def".as_bytes(),
                current
                    .borrow_mut()
                    .get(LookupKey::new("abc".as_bytes(), 1).internal_key())
                    .unwrap()
                    .unwrap()
                    .0
                    .as_slice()
            );
            db.insert("abe".as_bytes(), "def".as_bytes()).unwrap();
        }

        {
            eprintln!(
                "children before: {:?}",
                env.children(Path::new("db")).unwrap()
            );
            // reuse_manifest above causes the old manifest to be deleted as obsolete, but no new
            // manifest is written. CURRENT becomes stale.
            let mut options = options.clone();
            options.reuse_logs = true;
            let db = Database::open("db", options).unwrap();

            eprintln!(
                "children after: {:?}",
                env.children(Path::new("db")).unwrap()
            );
            assert!(!env
                .exists(&Path::new("db").join("MANIFEST-000001"))
                .unwrap());
            assert!(env
                .exists(&Path::new("db").join("MANIFEST-000002"))
                .unwrap());
            assert!(!env
                .exists(&Path::new("db").join("MANIFEST-000005"))
                .unwrap());
            assert!(env.exists(&Path::new("db").join("000004.log")).unwrap());
            // 000004 should be reused, no new log file should be created.
            assert!(!env.exists(&Path::new("db").join("000006.log")).unwrap());
            // Log is reused, so memtable should contain last written entry from above.
            assert_eq!(1, db.mem.len());
            assert_eq!(
                "def".as_bytes(),
                db.mem
                    .get(&LookupKey::new("abe".as_bytes(), 3))
                    .0
                    .unwrap()
                    .as_slice()
            );
        }
    }

    #[test]
    fn test_db_impl_compact_range() {
        let (mut db, options) = build_db();
        let env = &options.env;

        eprintln!(
            "children before: {:?}",
            env.children(&Path::new("db").join("")).unwrap()
        );
        db.compact_range(b"aaa", b"dba").unwrap();
        eprintln!(
            "children after: {:?}",
            env.children(&Path::new("db").join("")).unwrap()
        );

        // assert_eq!(
        //     250,
        //     options
        //         .env
        //         .size_of(&Path::new("db").join("000007.ldb"))
        //         .unwrap()
        // );
        // assert_eq!(
        //     200,
        //     options
        //         .env
        //         .size_of(&Path::new("db").join("000008.ldb"))
        //         .unwrap()
        // );
        // assert_eq!(
        //     200,
        //     options
        //         .env
        //         .size_of(&Path::new("db").join("000009.ldb"))
        //         .unwrap()
        // );
        // assert_eq!(
        //     435,
        //     options
        //         .env
        //         .size_of(&Path::new("db").join("000015.ldb"))
        //         .unwrap()
        // );

        assert!(!options
            .env
            .exists(&Path::new("db").join("000001.ldb"))
            .unwrap());
        assert!(!options
            .env
            .exists(&Path::new("db").join("000002.ldb"))
            .unwrap());
        assert!(!options
            .env
            .exists(&Path::new("db").join("000004.ldb"))
            .unwrap());
        assert!(!options
            .env
            .exists(&Path::new("db").join("000005.ldb"))
            .unwrap());
        assert!(!options
            .env
            .exists(&Path::new("db").join("000006.ldb"))
            .unwrap());
        assert!(!options
            .env
            .exists(&Path::new("db").join("000013.ldb"))
            .unwrap());
        assert!(!options
            .env
            .exists(&Path::new("db").join("000014.ldb"))
            .unwrap());

        assert_eq!(b"val1".to_vec(), db.get(b"aaa").unwrap());
        assert_eq!(b"val2".to_vec(), db.get(b"cab").unwrap());
        assert_eq!(b"val3".to_vec(), db.get(b"aba").unwrap());
        assert_eq!(b"val3".to_vec(), db.get(b"fab").unwrap());
    }

    #[test]
    fn test_db_impl_compact_range_memtable() {
        let (mut db, options) = build_db();
        let env = &options.env;

        db.insert(b"xxx", b"123").unwrap();

        eprintln!(
            "children before: {:?}",
            env.children(Path::new("db")).unwrap()
        );
        db.compact_range(b"aaa", b"dba").unwrap();
        eprintln!(
            "children after: {:?}",
            env.children(Path::new("db")).unwrap()
        );

        // assert_eq!(
        //     250,
        //     options
        //         .env
        //         .size_of(&Path::new("db").join("000007.ldb"))
        //         .unwrap()
        // );
        // assert_eq!(
        //     200,
        //     options
        //         .env
        //         .size_of(&Path::new("db").join("000008.ldb"))
        //         .unwrap()
        // );
        // assert_eq!(
        //     200,
        //     options
        //         .env
        //         .size_of(&Path::new("db").join("000009.ldb"))
        //         .unwrap()
        // );
        // assert_eq!(
        //     182,
        //     options
        //         .env
        //         .size_of(&Path::new("db").join("000014.ldb"))
        //         .unwrap()
        // );
        // assert_eq!(
        //     435,
        //     options
        //         .env
        //         .size_of(&Path::new("db").join("000017.ldb"))
        //         .unwrap()
        // );

        assert!(!options
            .env
            .exists(&Path::new("db").join("000001.ldb"))
            .unwrap());
        assert!(!options
            .env
            .exists(&Path::new("db").join("000002.ldb"))
            .unwrap());
        assert!(!options
            .env
            .exists(&Path::new("db").join("000003.ldb"))
            .unwrap());
        assert!(!options
            .env
            .exists(&Path::new("db").join("000004.ldb"))
            .unwrap());
        assert!(!options
            .env
            .exists(&Path::new("db").join("000005.ldb"))
            .unwrap());
        assert!(!options
            .env
            .exists(&Path::new("db").join("000006.ldb"))
            .unwrap());
        assert!(!options
            .env
            .exists(&Path::new("db").join("000015.ldb"))
            .unwrap());
        assert!(!options
            .env
            .exists(&Path::new("db").join("000016.ldb"))
            .unwrap());

        assert_eq!(b"val1".to_vec(), db.get(b"aaa").unwrap());
        assert_eq!(b"val2".to_vec(), db.get(b"cab").unwrap());
        assert_eq!(b"val3".to_vec(), db.get(b"aba").unwrap());
        assert_eq!(b"val3".to_vec(), db.get(b"fab").unwrap());
        assert_eq!(b"123".to_vec(), db.get(b"xxx").unwrap());
    }

    #[allow(unused_variables)]
    #[test]
    fn test_db_impl_locking() {
        let options = Options::for_test();
        let db = Database::open("db", options.clone()).unwrap();
        let want_err = Status::new(
            StatusCode::LockError,
            // "database lock is held by another instance",
            "lock: file already locked: db/LOCK",
        );
        assert_eq!(
            want_err,
            Database::open("db", options.clone()).err().unwrap()
        );
    }

    #[test]
    fn test_db_impl_build_table() {
        let mut options = Options::for_test();
        options.block_size = 128;
        let mt = build_memtable();

        let f = build_table("db", &options, mt.iter(), 123).unwrap();
        let path = &Path::new("db").join("000123.ldb");

        assert_eq!(
            LookupKey::new("aabc".as_bytes(), 6).internal_key(),
            f.smallest.as_slice()
        );
        assert_eq!(
            LookupKey::new("test123".as_bytes(), 7).internal_key(),
            f.largest.as_slice()
        );
        // assert_eq!(379, f.size);
        assert_eq!(123, f.id);
        assert!(options.env.exists(path).unwrap());

        {
            // Read table back in.
            let mut tc = TableCache::new("db", options.clone(), 100);
            let tbl = tc.get_table(123).unwrap();
            assert_eq!(mt.len(), DbIteratorWrapper::new(&mut tbl.iter()).count());
        }

        {
            // Corrupt table; make sure it doesn't load fully.
            let mut buf = vec![];
            options
                .env
                .open_sequential_file(path)
                .unwrap()
                .read_to_end(&mut buf)
                .unwrap();
            buf[150] += 1;
            options
                .env
                .open_writable_file(path)
                .unwrap()
                .write_all(&buf)
                .unwrap();

            let mut tc = TableCache::new("db", options.clone(), 100);
            let tbl = tc.get_table(123).unwrap();
            // The last two entries are skipped due to the corruption above.
            assert_eq!(
                5,
                DbIteratorWrapper::new(&mut tbl.iter())
                    .map(|v| eprintln!("{:?}", v))
                    .count()
            );
        }
    }

    #[allow(unused_variables)]
    #[test]
    fn test_db_impl_build_db_sanity() {
        let db = build_db().0;
        let env = &db.options.env;
        let name = &db.name;

        assert!(env.exists(Path::new(&log_file_name(name, 12))).unwrap());
    }

    #[test]
    fn test_db_impl_get_from_table_with_snapshot() {
        let mut db = build_db().0;

        assert_eq!(30, db.version_set.borrow().last_sequence);

        // seq = 31
        db.insert("xyy".as_bytes(), "123".as_bytes()).unwrap();
        let old_ss = db.get_snapshot();
        // seq = 32
        db.insert("xyz".as_bytes(), "123".as_bytes()).unwrap();
        db.flush().unwrap();
        assert!(db.get_at(&old_ss, "xyy".as_bytes()).unwrap().is_some());
        assert!(db.get_at(&old_ss, "xyz".as_bytes()).unwrap().is_none());

        // memtable get
        assert_eq!(
            "123".as_bytes(),
            db.get("xyz".as_bytes()).unwrap().as_slice()
        );
        assert!(db.get_internal(31, "xyy".as_bytes()).unwrap().is_some());
        assert!(db.get_internal(32, "xyy".as_bytes()).unwrap().is_some());

        assert!(db.get_internal(31, "xyz".as_bytes()).unwrap().is_none());
        assert!(db.get_internal(32, "xyz".as_bytes()).unwrap().is_some());

        // table get
        assert_eq!(
            "val2".as_bytes(),
            db.get("eab".as_bytes()).unwrap().as_slice()
        );
        assert!(db.get_internal(3, "eab".as_bytes()).unwrap().is_none());
        assert!(db.get_internal(32, "eab".as_bytes()).unwrap().is_some());

        {
            let ss = db.get_snapshot();
            assert_eq!(
                "val2".as_bytes(),
                db.get_at(&ss, "eab".as_bytes())
                    .unwrap()
                    .unwrap()
                    .as_slice()
            );
        }

        // from table.
        assert_eq!(
            "val2".as_bytes(),
            db.get("cab".as_bytes()).unwrap().as_slice()
        );
    }

    #[test]
    fn test_db_impl_delete() {
        let mut db = build_db().0;

        db.insert(b"xyy", b"123").unwrap();
        db.insert(b"xyz", b"123").unwrap();

        assert!(db.get(b"xyy").is_some());
        assert!(db.get(b"gaa").is_some());

        // Delete one memtable entry and one table entry.
        db.delete(b"xyy").unwrap();
        db.delete(b"gaa").unwrap();

        assert!(db.get(b"xyy").is_none());
        assert!(db.get(b"gaa").is_none());
        assert!(db.get(b"xyz").is_some());
    }

    #[test]
    fn test_db_impl_compact_single_file() {
        let mut db = build_db().0;
        set_file_to_compact(&mut db, 4);
        db.try_compaction().unwrap();

        let env = &db.options.env;
        let name = &db.name;
        assert!(!env.exists(&TableCache::table_file_name(name, 3)).unwrap());
        assert!(!env.exists(&TableCache::table_file_name(name, 4)).unwrap());
        assert!(!env.exists(&TableCache::table_file_name(name, 5)).unwrap());
        assert!(env.exists(&TableCache::table_file_name(name, 13)).unwrap());
    }

    #[test]
    fn test_db_impl_compaction_trivial_move() {
        let mut db = Database::open("db", Options::for_test()).unwrap();

        db.insert("abc".as_bytes(), "xyz".as_bytes()).unwrap();
        db.insert("ab3".as_bytes(), "xyz".as_bytes()).unwrap();
        db.insert("ab0".as_bytes(), "xyz".as_bytes()).unwrap();
        db.insert("abz".as_bytes(), "xyz".as_bytes()).unwrap();
        assert_eq!(4, db.mem.len());
        let mut imm = Memtable::new(db.options.cmp.clone());
        std::mem::swap(&mut imm, &mut db.mem);
        db.imm = Some(imm);
        db.compact_memtable().unwrap();

        eprintln!(
            "children after: {:?}",
            db.options.env.children(Path::new("db")).unwrap()
        );
        assert!(db
            .options
            .env
            .exists(&Path::new("db").join("000004.ldb"))
            .unwrap());

        {
            let v = db.current();
            let mut v = v.borrow_mut();
            v.file_to_compact = Some(v.files[2][0].clone());
            v.file_to_compact_level = 2;
        }

        db.try_compaction().unwrap();

        {
            let v = db.current();
            let v = v.borrow_mut();
            assert_eq!(1, v.files[3].len());
        }
    }

    #[test]
    fn test_db_impl_memtable_compaction() {
        let mut options = Options::for_test();
        options.write_buffer_size = 25;
        let mut db = Database::new("db", options);

        // Fill up memtable.
        db.mem = build_memtable();

        // Trigger memtable compaction.
        db.make_room_for_write(true).unwrap();
        assert_eq!(0, db.mem.len());
        assert!(db
            .options
            .env
            .exists(&Path::new("db").join("000002.log"))
            .unwrap());
        assert!(db
            .options
            .env
            .exists(&Path::new("db").join("000003.ldb"))
            .unwrap());
        // assert_eq!(
        //     351,
        //     db.options
        //         .env
        //         .size_of(&Path::new("db").join("000003.ldb"))
        //         .unwrap()
        // );
        assert_eq!(
            7,
            DbIteratorWrapper::new(&mut db.cache.borrow_mut().get_table(3).unwrap().iter()).count()
        );
    }

    #[test]
    fn test_db_impl_compaction() {
        let mut db = build_db().0;
        let v = db.current();
        v.borrow_mut().compaction_score = Some(2.0);
        v.borrow_mut().compaction_level = Some(1);

        db.try_compaction().unwrap();

        assert!(!db
            .options
            .env
            .exists(&Path::new("db").join("000003.ldb"))
            .unwrap());
        assert!(db
            .options
            .env
            .exists(&Path::new("db").join("000013.ldb"))
            .unwrap());
        // assert_eq!(
        //     345,
        //     db.options
        //         .env
        //         .size_of(&Path::new("db").join("000013.ldb"))
        //         .unwrap()
        // );

        // New current version.
        let v = db.current();
        assert_eq!(0, v.borrow().files[1].len());
        assert_eq!(2, v.borrow().files[2].len());
    }

    #[test]
    fn test_db_impl_compaction_trivial() {
        let (mut v, options) = make_version();

        let to_compact = v.files[2][0].clone();
        v.file_to_compact = Some(to_compact);
        v.file_to_compact_level = 2;

        let mut db = Database::new("db", options.clone());
        db.version_set.borrow_mut().set_version(v);
        db.version_set.borrow_mut().next_file_id = 10;

        db.try_compaction().unwrap();

        assert!(options
            .env
            .exists(&Path::new("db").join("000006.ldb"))
            .unwrap());
        assert!(!options
            .env
            .exists(&Path::new("db").join("000010.ldb"))
            .unwrap());
        // assert_eq!(
        //     218,
        //     options
        //         .env
        //         .size_of(&Path::new("db").join("000006.ldb"))
        //         .unwrap()
        // );

        let v = db.current();
        assert_eq!(1, v.borrow().files[2].len());
        assert_eq!(3, v.borrow().files[3].len());
    }

    #[test]
    fn test_db_impl_compaction_state_cleanup() {
        let env: Box<dyn Env> = Box::new(MemEnv::new());
        let name = "db";

        let stuff = "abcdefghijkl".as_bytes();
        env.open_writable_file(&Path::new("db").join("000001.ldb"))
            .unwrap()
            .write_all(stuff)
            .unwrap();
        let mut fmd = FileMetaData::default();
        fmd.id = 1;

        let mut cs = CompState::new(Compaction::new(&Options::for_test(), 2, None), 12);
        cs.outputs = vec![fmd];
        cs.cleanup(env.as_ref(), name);

        assert!(!env.exists(&Path::new("db").join("000001.ldb")).unwrap());
    }

    #[test]
    fn test_db_impl_open_close_reopen() {
        let options;
        {
            let mut db = build_db().0;
            options = db.options.clone();
            db.insert(b"xx1", b"111").unwrap();
            db.insert(b"xx2", b"112").unwrap();
            db.insert(b"xx3", b"113").unwrap();
            db.insert(b"xx4", b"114").unwrap();
            db.insert(b"xx5", b"115").unwrap();
            db.delete(b"xx2").unwrap();
        }

        {
            let mut db = Database::open("db", options.clone()).unwrap();
            db.delete(b"xx5").unwrap();
        }

        {
            let mut db = Database::open("db", options.clone()).unwrap();

            assert_eq!(None, db.get(b"xx5"));

            let ss = db.get_snapshot();
            db.insert(b"xx4", b"222").unwrap();
            let ss2 = db.get_snapshot();

            assert_eq!(Some(b"113".to_vec()), db.get_at(&ss, b"xx3").unwrap());
            assert_eq!(None, db.get_at(&ss, b"xx2").unwrap());
            assert_eq!(None, db.get_at(&ss, b"xx5").unwrap());

            assert_eq!(Some(b"114".to_vec()), db.get_at(&ss, b"xx4").unwrap());
            assert_eq!(Some(b"222".to_vec()), db.get_at(&ss2, b"xx4").unwrap());
        }

        {
            let mut db = Database::open("db", options).unwrap();

            let ss = db.get_snapshot();
            assert_eq!(Some(b"113".to_vec()), db.get_at(&ss, b"xx3").unwrap());
            assert_eq!(Some(b"222".to_vec()), db.get_at(&ss, b"xx4").unwrap());
            assert_eq!(None, db.get_at(&ss, b"xx2").unwrap());
        }
    }

    #[test]
    fn test_drop_memtable() {
        let mut db = Database::open("db", Options::for_test()).unwrap();
        let mut cnt = 0;
        let mut buf: Vec<u8> = Vec::with_capacity(8);
        let entries_per_batch = 1;
        let max_num = 100000;
        while cnt < max_num {
            let mut write_batch = WriteBatch::new();
            for i in 0..entries_per_batch {
                buf.clear();
                buf.extend_from_slice(format!("{}-{}", cnt, i).as_bytes());
                write_batch.add(buf.as_slice(), buf.as_slice());
            }
            db.write(write_batch, false).unwrap();
            cnt += entries_per_batch;
        }
    }
}
