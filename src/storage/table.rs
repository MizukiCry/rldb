//! SSTable implementation
use crate::coredef::{
    cmp::InternalKeyCmp,
    compressor::{Compressor, NoneCompressor},
    env::RandomAccess,
    error::{err, Result, StatusCode},
    key::InternalKey,
    options::Options,
    types::{DbIterator, FileID},
};
use crate::storage::{
    block::{Block, BlockBuilder, BlockHandle, BlockIter},
    filter_block::{FilterBlockBuilder, FilterBlockReader},
};
use crate::utils::{
    cache::{Cache, CacheID, CacheKey},
    filter::{FilterPolicy, InternalKeyFilterPolicy},
    mask_crc, unmask_crc, CRC,
};
use integer_encoding::{FixedInt, FixedIntWriter};
use std::{
    cmp::Ordering,
    io::Write,
    path::{Path, PathBuf},
    rc::Rc,
};

/// A footer is used to indicate meta index block and index block.
///
/// Footer format:
/// [meta_index_handle, index_handle, Padding, magic_number (used to verify)]
/// size (excluding magic_number): 40 bytes
/// size (including magic_number): 48 bytes
#[derive(Clone)]
pub struct Footer {
    pub meta_index_handle: BlockHandle,
    pub index_handle: BlockHandle,
}

impl Footer {
    pub const FOOTER_SIZE: usize = 40;
    pub const FOOTER_FULL_SIZE: usize = 48;
    pub const MAGIC_NUMBER: u64 = 0xdb4775248b80fb57;
    pub const MAGIC_NUMBER_BYTES: [u8; 8] = [0x57, 0xfb, 0x80, 0x8b, 0x24, 0x75, 0x47, 0xdb];

    pub fn new(meta_index_handle: BlockHandle, index_handle: BlockHandle) -> Self {
        Self {
            meta_index_handle,
            index_handle,
        }
    }

    pub fn decode(src: &[u8]) -> Option<Self> {
        assert_eq!(src.len(), Self::FOOTER_FULL_SIZE, "Invalid footer size");
        assert_eq!(
            &src[Self::FOOTER_SIZE..],
            &Self::MAGIC_NUMBER_BYTES,
            "Invalid magic number"
        );

        let (meta_index_handle, len) = BlockHandle::decode(src)?;
        let index_handle = BlockHandle::decode(&src[len..])?.0;

        Some(Self::new(meta_index_handle, index_handle))
    }

    pub fn encode(&self, dst: &mut [u8]) {
        assert!(dst.len() >= Self::FOOTER_FULL_SIZE, "Buffer too small");

        let meta_index_len = self.meta_index_handle.encode(dst);
        let index_len = self.index_handle.encode(&mut dst[meta_index_len..]);

        dst[meta_index_len + index_len..Self::FOOTER_SIZE].fill(0);
        dst[Self::FOOTER_SIZE..Self::FOOTER_FULL_SIZE].copy_from_slice(&Self::MAGIC_NUMBER_BYTES);
    }
}

/// A sstable consists of multiple blocks (default 4KiB).
///
/// SSTable format:
/// [data_block_1, data_block_2, ..., data_block_n]
/// [filter_block, meta_index_block, index_block, footer]
/// An index_block is used to indicate each data_block
/// A meta_index_block is used to indicate filter_block
///
/// Block format:
/// [data, compression_type (1 byte), crc_checksum (4 bytes)]
#[derive(Clone)]
pub struct Table {
    file: Rc<dyn RandomAccess>,
    cache_id: CacheID,
    options: Options,

    #[allow(dead_code)]
    footer: Footer,

    index_block: Block,
    filters: Option<FilterBlockReader>,
}

impl Table {
    pub const COMPRESSOR_SIZE: usize = 1;
    pub const CHECKSUM_SIZE: usize = 4;

    /// Creates a table reader on InternalKey
    pub fn new(mut options: Options, file: Rc<dyn RandomAccess>, size: usize) -> Result<Self> {
        options.cmp = Rc::new(InternalKeyCmp(options.cmp.clone()));
        options.filter_policy = Rc::new(InternalKeyFilterPolicy::new(options.filter_policy));
        Self::new_raw(options, file, size)
    }

    fn read_footer(file: &dyn RandomAccess, size: usize) -> Result<Footer> {
        let mut buf = [0; Footer::FOOTER_FULL_SIZE];
        file.read(size - Footer::FOOTER_FULL_SIZE, &mut buf)?;
        match Footer::decode(&buf) {
            Some(f) => Ok(f),
            None => err(StatusCode::Corruption, "Invalid footer"),
        }
    }

    fn read_bytes(file: &dyn RandomAccess, handle: &BlockHandle) -> Result<Vec<u8>> {
        let mut buffer = vec![0; handle.size()];
        file.read(handle.offset(), &mut buffer)?;
        Ok(buffer)
    }

    /// Read a sstable block from file.
    /// A handle refers to the data part of a block.
    fn read_table_block(
        options: Options,
        file: &dyn RandomAccess,
        handle: &BlockHandle,
    ) -> Result<Block> {
        let buffer = Self::read_bytes(file, handle)?;
        let compressor_id = Self::read_bytes(
            file,
            &BlockHandle::new(handle.offset() + handle.size(), Table::COMPRESSOR_SIZE),
        )?[0];
        let crc = unmask_crc(
            u32::decode_fixed(&Self::read_bytes(
                file,
                &BlockHandle::new(
                    handle.offset() + handle.size() + Table::COMPRESSOR_SIZE,
                    Table::CHECKSUM_SIZE,
                ),
            )?)
            .unwrap(),
        );

        let mut digest = CRC.digest();
        digest.update(&buffer);
        digest.update(&[compressor_id]);

        if digest.finalize() != crc {
            return err(
                StatusCode::Corruption,
                &format!("Block checksum mismatch at {}", handle.offset()),
            );
        }

        let contents = options.compressor_list.get(compressor_id)?.decode(buffer)?;
        Ok(Block::new(contents, options))
    }

    fn read_filter_block(
        meta_index_block: &Block,
        file: &dyn RandomAccess,
        options: &Options,
    ) -> Result<Option<FilterBlockReader>> {
        let mut iter = meta_index_block.iter();
        iter.seek(format!("filter.{}", options.filter_policy.name()).as_bytes());

        if let Some((_, value)) = iter.current_kv() {
            if let Some((handle, _)) = BlockHandle::decode(&value) {
                if handle.size() != 0 {
                    if handle.size() < 5 {
                        return err(StatusCode::InvalidArgument, "Filter block size too small");
                    }
                    return Ok(Some(FilterBlockReader::new_with_vec(
                        options.filter_policy.clone(),
                        Self::read_bytes(file, &handle)?,
                    )));
                }
            } else {
                return err(StatusCode::Corruption, "Invalid filter block handle");
            }
        }
        Ok(None)
    }

    /// Creates a table reader on UserKey
    fn new_raw(options: Options, file: Rc<dyn RandomAccess>, size: usize) -> Result<Self> {
        let footer = Self::read_footer(file.as_ref(), size)?;
        let index_block =
            Self::read_table_block(options.clone(), file.as_ref(), &footer.index_handle)?;
        let meta_index_block =
            Self::read_table_block(options.clone(), file.as_ref(), &footer.meta_index_handle)?;

        let filters = Self::read_filter_block(&meta_index_block, file.as_ref(), &options)?;
        let cache_id = options.block_cache.borrow_mut().new_cache_id();

        Ok(Self {
            file,
            cache_id,
            options,
            footer,
            index_block,
            filters,
        })
    }

    fn try_get_block(&self, handle: &BlockHandle) -> Result<Block> {
        let mut cache_key = [0u8; 16];
        (&mut cache_key[..8]).write_fixedint(self.cache_id).unwrap();
        (&mut cache_key[8..])
            .write_fixedint(handle.offset() as u64)
            .unwrap();

        if let Some(block) = self.options.block_cache.borrow_mut().get(&cache_key) {
            return Ok(block.clone());
        }

        let block = Self::read_table_block(self.options.clone(), self.file.as_ref(), handle)?;
        self.options
            .block_cache
            .borrow_mut()
            .insert(&cache_key, block.clone());
        Ok(block)
    }

    /// Returns the userkey-value pair for the given key.
    /// Callers are supposed to check the result.
    pub fn get(&self, key: InternalKey) -> Result<Option<(Vec<u8>, Vec<u8>)>> {
        let mut iter = self.index_block.iter();
        iter.seek(key);

        let handle;
        if let Some((last_key, h)) = iter.current_kv() {
            if self.options.cmp.cmp(key, &last_key) == Ordering::Less {
                handle = BlockHandle::decode(&h).unwrap().0;
            } else {
                return Ok(None);
            }
        } else {
            return Ok(None);
        }

        if let Some(f) = &self.filters {
            if !f.may_exist(handle.offset(), key) {
                return Ok(None);
            }
        }

        let block = self.try_get_block(&handle)?;
        let mut iter = block.iter();
        iter.seek(key);

        if let Some((k, v)) = iter.current_kv() {
            if self.options.cmp.cmp(&k, key) != Ordering::Less {
                return Ok(Some((k, v)));
            }
        }
        Ok(None)
    }

    pub fn iter(&self) -> TableIterator {
        TableIterator {
            table: self.clone(),
            current_block_iter: None,
            current_block_offset: 0,
            index_block_iter: self.index_block.iter(),
        }
    }

    #[cfg(test)]
    pub fn approx_offset(&self, key: &[u8]) -> usize {
        let mut iter = self.index_block.iter();
        iter.seek(key);

        if let Some((_, value)) = iter.current_kv() {
            return BlockHandle::decode(&value).unwrap().0.offset();
        }

        self.footer.meta_index_handle.offset()
    }
}

pub struct TableIterator {
    table: Table,
    current_block_iter: Option<BlockIter>,
    current_block_offset: usize,
    index_block_iter: BlockIter,
}

impl TableIterator {
    fn skip_to_next_block(&mut self) -> Result<bool> {
        if let Some((_, value)) = self.index_block_iter.next() {
            self.load_block(&value)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn load_block(&mut self, handle: &[u8]) -> Result<()> {
        let handle = BlockHandle::decode(handle);
        if handle.is_none() {
            return err(StatusCode::Corruption, "Invalid block handle");
        }

        let handle = handle.unwrap().0;
        let block = self.table.try_get_block(&handle)?;
        self.current_block_iter = Some(block.iter());
        self.current_block_offset = handle.offset();
        Ok(())
    }
}

impl DbIterator for TableIterator {
    fn advance(&mut self) -> bool {
        if self.current_block_iter.is_none() {
            if let Ok(false) = self.skip_to_next_block() {
                self.reset();
                return false;
            }
            return self.advance();
        }

        if self
            .current_block_iter
            .as_mut()
            .is_some_and(|i| i.advance())
        {
            return true;
        }

        self.current_block_iter = None;
        self.advance()
    }

    fn seek(&mut self, key: &[u8]) {
        self.index_block_iter.seek(key);
        if let Some((block_last_key, handle)) = self.index_block_iter.current_kv() {
            if self.table.options.cmp.cmp(key, &block_last_key) != Ordering::Greater
                && self.load_block(&handle).is_ok()
            {
                self.current_block_iter.as_mut().unwrap().seek(key);
                return;
            }
        }
        self.reset();
    }

    fn prev(&mut self) -> bool {
        if self.current_block_iter.as_mut().is_some_and(|i| i.prev()) {
            return true;
        }

        if self.index_block_iter.prev() {
            if let Some((_, handle)) = self.index_block_iter.current_kv() {
                if self.load_block(&handle).is_ok() {
                    self.current_block_iter.as_mut().unwrap().seek_to_last();
                    return self.current_block_iter.as_ref().unwrap().valid();
                } else {
                    self.reset();
                }
            }
        }
        false
    }

    fn reset(&mut self) {
        self.index_block_iter.reset();
        self.current_block_iter = None;
    }

    fn valid(&self) -> bool {
        self.current_block_iter.as_ref().is_some_and(|i| i.valid())
    }

    fn current(&self, key: &mut Vec<u8>, value: &mut Vec<u8>) -> bool {
        if let Some(i) = &self.current_block_iter {
            i.current(key, value)
        } else {
            false
        }
    }
}

pub struct TableBuilder<W: Write> {
    options: Options,
    dst: W,
    offset: usize,
    num_entries: usize,
    prev_block_last_key: Vec<u8>,

    data_block: Option<BlockBuilder>,
    index_block: Option<BlockBuilder>,
    filter_block: Option<FilterBlockBuilder>,
}

impl<W: Write> TableBuilder<W> {
    /// Wraps cmp in a InternalKeyCmp, policy in a Internal
    pub fn new(mut options: Options, dst: W) -> Self {
        options.cmp = Rc::new(InternalKeyCmp(options.cmp.clone()));
        options.filter_policy = Rc::new(InternalKeyFilterPolicy::new(options.filter_policy));
        Self::new_raw(options, dst)
    }

    pub fn new_raw(options: Options, dst: W) -> Self {
        Self {
            dst,
            offset: 0,
            num_entries: 0,
            prev_block_last_key: Vec::new(),
            data_block: Some(BlockBuilder::new(options.clone())),
            index_block: Some(BlockBuilder::new(options.clone())),
            filter_block: Some(FilterBlockBuilder::new(options.filter_policy.clone())),
            options,
        }
    }

    pub fn num_entries(&self) -> usize {
        self.num_entries
    }

    pub fn estimate_size(&self) -> usize {
        self.data_block.as_ref().map_or(0, |b| b.estimate_size())
            + self.index_block.as_ref().map_or(0, |b| b.estimate_size())
            + self.filter_block.as_ref().map_or(0, |b| b.estimate_size())
            + self.offset
            + Footer::FOOTER_FULL_SIZE
    }

    /// Add a key to the table.
    /// The key are supposed to added in ascending order.
    pub fn add(&mut self, key: InternalKey, value: &[u8]) -> Result<()> {
        // assert!(self.data_block.is_some());

        if !self.prev_block_last_key.is_empty() {
            assert!(self.options.cmp.cmp(&self.prev_block_last_key, key) == Ordering::Less);
        }

        if self.data_block.as_ref().unwrap().estimate_size() > self.options.block_size {
            self.write_data_block(key)?;
        }

        if let Some(filter_block) = &mut self.filter_block {
            filter_block.add(key);
        }

        self.num_entries += 1;
        self.data_block.as_mut().unwrap().add(key, value);
        Ok(())
    }

    /// Writes current data block and create next data block with next_key.
    fn write_data_block(&mut self, next_key: InternalKey) -> Result<()> {
        // assert!(self.data_block.is_some());

        let data_block = self.data_block.take().unwrap();
        self.data_block = Some(BlockBuilder::new(self.options.clone()));

        let separator = self
            .options
            .cmp
            .find_shortest_separator(data_block.last_key(), next_key);
        self.prev_block_last_key = data_block.last_key().to_vec();
        let data_block = data_block.build();

        let compressor_id = self.options.compressor;
        let compressor_list = self.options.compressor_list.clone();
        let compressor = compressor_list.get(compressor_id)?;
        let handle = self.write_block(data_block, compressor_id, compressor)?;

        let mut handle_encoded = [0u8; 16];
        let handle_length = handle.encode(&mut handle_encoded);

        self.index_block
            .as_mut()
            .unwrap()
            .add(&separator, &handle_encoded[0..handle_length]);

        if let Some(filter_block) = &mut self.filter_block {
            filter_block.start_block(self.offset);
        }

        Ok(())
    }

    /// Writes a block to file
    fn write_block(
        &mut self,
        block: Vec<u8>,
        compressor_id: u8,
        compressor: &dyn Compressor,
    ) -> Result<BlockHandle> {
        let data = compressor.encode(block)?;

        self.dst.write_all(&data)?;
        self.dst.write_all(&[compressor_id])?;

        let mut digest = CRC.digest();
        digest.update(&data);
        digest.update(&[compressor_id]);

        self.dst.write_fixedint(mask_crc(digest.finalize()))?;

        let handle = BlockHandle::new(self.offset, data.len());
        self.offset += data.len() + Table::COMPRESSOR_SIZE + Table::CHECKSUM_SIZE;
        Ok(handle)
    }

    pub fn build(mut self) -> Result<usize> {
        // assert!(self.data_block.is_some());

        let compressor_list = self.options.compressor_list.clone();
        let compressor_id = self.options.compressor;
        let compressor = compressor_list.get(compressor_id)?;

        if self.data_block.as_ref().unwrap().num_entries() != 0 {
            self.write_data_block(
                &self
                    .options
                    .cmp
                    .find_shortest_successor(self.data_block.as_ref().unwrap().last_key()),
            )?;
        }

        let mut meta_index_block = BlockBuilder::new(self.options.clone());

        if let Some(filter_block) = self.filter_block.take() {
            let filter_key = format!("filter.{}", filter_block.policy_name());
            let filter_data = filter_block.build();

            let handle = self.write_block(filter_data, NoneCompressor.id(), &NoneCompressor)?;
            let mut handle_encoded = [0u8; 16];
            let handle_length = handle.encode(&mut handle_encoded);

            meta_index_block.add(filter_key.as_bytes(), &handle_encoded[..handle_length]);
        }

        let meta_index_handle =
            self.write_block(meta_index_block.build(), compressor_id, compressor)?;

        let index_data = self.index_block.take().unwrap().build();
        let index_handle = self.write_block(index_data, compressor_id, compressor)?;

        let footer = Footer::new(meta_index_handle, index_handle);
        let mut footer_data = [0; Footer::FOOTER_FULL_SIZE];
        footer.encode(&mut footer_data);

        self.offset += self.dst.write(&footer_data[..])?;
        self.dst.flush()?;
        Ok(self.offset)
    }
}

/// A cache for sstable on disk.
pub struct TableCache {
    database: PathBuf,
    cache: Cache<Table>,
    options: Options,
}

impl TableCache {
    pub fn new(database: impl AsRef<Path>, options: Options, capacity: usize) -> Self {
        Self {
            database: database.as_ref().to_owned(),
            cache: Cache::new(capacity),
            options,
        }
    }

    pub fn get(&mut self, file_id: FileID, key: InternalKey) -> Result<Option<(Vec<u8>, Vec<u8>)>> {
        self.get_table(file_id)?.get(key)
    }

    fn file_id_to_key(file_id: FileID) -> CacheKey {
        let mut key = [0u8; 16];
        (&mut key[..]).write_fixedint(file_id).unwrap();
        key
    }

    pub fn table_file_name(name: impl AsRef<Path>, file_id: FileID) -> PathBuf {
        name.as_ref().join(format!("{:06}.ldb", file_id))
    }

    pub fn get_table(&mut self, file_id: FileID) -> Result<Table> {
        let key = Self::file_id_to_key(file_id);
        if let Some(table) = self.cache.get(&key) {
            return Ok(table.clone());
        }

        let name = Self::table_file_name(&self.database, file_id);
        let path = name.as_path();
        let file_size = self.options.env.size_of(path)?;

        if file_size == 0 {
            return err(StatusCode::InvalidData, "Empty file");
        }

        let file = self.options.env.open_random_access_file(path)?;
        let table = Table::new(self.options.clone(), file.into(), file_size)?;
        self.cache
            .insert(&Self::file_id_to_key(file_id), table.clone());
        Ok(table)
    }

    pub fn evict(&mut self, file_id: FileID) -> Result<()> {
        if self.cache.remove(&Self::file_id_to_key(file_id)).is_some() {
            Ok(())
        } else {
            err(StatusCode::NotFound, "Table not found")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests_builder {
        use crate::coredef::compressor::SnappyCompressor;

        use super::*;

        #[test]
        fn test_footer() {
            let f = Footer::new(BlockHandle::new(44, 4), BlockHandle::new(55, 5));
            let mut buf = [0; 48];
            f.encode(&mut buf[..]);

            let f2 = Footer::decode(&buf).unwrap();
            assert_eq!(f2.meta_index_handle.offset(), 44);
            assert_eq!(f2.meta_index_handle.size(), 4);
            assert_eq!(f2.index_handle.offset(), 55);
            assert_eq!(f2.index_handle.size(), 5);
        }

        #[test]
        fn test_table_builder() {
            let mut d = Vec::with_capacity(512);
            let mut opt = Options::for_test();
            opt.block_restart_interval = 3;
            opt.compressor = SnappyCompressor.id();
            let mut b = TableBuilder::new_raw(opt, &mut d);

            let data = vec![
                ("abc", "def"),
                ("abe", "dee"),
                ("bcd", "asa"),
                ("dcc", "a00"),
            ];
            let data2 = vec![
                ("abd", "def"),
                ("abf", "dee"),
                ("ccd", "asa"),
                ("dcd", "a00"),
            ];

            for i in 0..data.len() {
                b.add(&data[i].0.as_bytes(), &data[i].1.as_bytes()).unwrap();
                b.add(&data2[i].0.as_bytes(), &data2[i].1.as_bytes())
                    .unwrap();
            }

            let estimate = b.estimate_size();

            assert_eq!(143, estimate);
            assert!(b.filter_block.is_some());

            // let actual = b.build().unwrap();
            // assert_eq!(223, actual);
        }

        #[test]
        #[should_panic]
        fn test_bad_input() {
            let mut d = Vec::with_capacity(512);
            let mut opt = Options::for_test();
            opt.block_restart_interval = 3;
            let mut b = TableBuilder::new_raw(opt, &mut d);

            // Test two equal consecutive keys
            let data = vec![
                ("abc", "def"),
                ("abc", "dee"),
                ("bcd", "asa"),
                ("bsr", "a00"),
            ];

            for &(k, v) in data.iter() {
                b.add(k.as_bytes(), v.as_bytes()).unwrap();
            }
            b.build().unwrap();
        }
    }

    mod tests_cache {
        use crate::coredef::{env::mem_env::MemEnv, types::DbIteratorWrapper};

        use super::*;

        #[test]
        fn test_table_file_name() {
            assert_eq!(
                Path::new("abc/000122.ldb"),
                TableCache::table_file_name("abc", 122)
            );
            assert_eq!(
                Path::new("abc/1234567.ldb"),
                TableCache::table_file_name("abc", 1234567)
            );
        }

        fn make_key(a: u8, b: u8, c: u8) -> CacheKey {
            [a, b, c, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        }

        #[test]
        fn test_filenum_to_key() {
            assert_eq!(make_key(16, 0, 0), TableCache::file_id_to_key(0x10));
            assert_eq!(make_key(16, 1, 0), TableCache::file_id_to_key(0x0110));
            assert_eq!(make_key(1, 2, 3), TableCache::file_id_to_key(0x030201));
        }

        fn write_table_to(o: Options, p: &Path) {
            let w = o.env.open_writable_file(p).unwrap();
            let mut b = TableBuilder::new_raw(o, w);

            let data = vec![
                ("abc", "def"),
                ("abd", "dee"),
                ("bcd", "asa"),
                ("bsr", "a00"),
            ];

            for &(k, v) in data.iter() {
                b.add(k.as_bytes(), v.as_bytes()).unwrap();
            }
            b.build().unwrap();
        }

        #[test]
        fn test_table_cache() {
            // Tests that a table can be written to a MemFS file, read back by the table cache and
            // parsed/iterated by the table reader.
            let mut opt = Options::for_test();
            opt.env = Rc::new(MemEnv::new());
            let dbname = Path::new("testdb1");
            let tablename = TableCache::table_file_name(dbname, 123);
            let tblpath = Path::new(&tablename);

            write_table_to(opt.clone(), tblpath);
            assert!(opt.env.exists(tblpath).unwrap());
            assert!(opt.env.size_of(tblpath).unwrap() > 20);

            let mut cache = TableCache::new(dbname, opt.clone(), 10);
            assert!(cache.cache.get(&TableCache::file_id_to_key(123)).is_none());
            assert_eq!(
                DbIteratorWrapper::new(&mut cache.get_table(123).unwrap().iter()).count(),
                4
            );
            // Test cached table.
            assert_eq!(
                DbIteratorWrapper::new(&mut cache.get_table(123).unwrap().iter()).count(),
                4
            );

            assert!(cache.cache.get(&TableCache::file_id_to_key(123)).is_some());
            assert!(cache.evict(123).is_ok());
            assert!(cache.evict(123).is_err());
            assert!(cache.cache.get(&TableCache::file_id_to_key(123)).is_none());
        }
    }

    mod tests_reader {
        use crate::{
            coredef::{compressor::SnappyCompressor, key::LookupKey, types::DbIteratorWrapper},
            utils::{filter::BloomFilterPolicy, test_iterator_properties},
        };

        use super::*;

        fn build_data() -> Vec<(&'static str, &'static str)> {
            vec![
                // block 1
                ("abc", "def"),
                ("abd", "dee"),
                ("bcd", "asa"),
                // block 2
                ("bsr", "a00"),
                ("xyz", "xxx"),
                ("xzz", "yyy"),
                // block 3
                ("zzz", "111"),
            ]
        }

        // Build a table containing raw keys (no format). It returns (vector, length) for convenience
        // reason, a call f(v, v.len()) doesn't work for borrowing reasons.
        fn build_table(data: Vec<(&'static str, &'static str)>) -> (Vec<u8>, usize) {
            let mut d = Vec::with_capacity(512);
            let mut opt = Options::for_test();
            opt.block_restart_interval = 2;
            opt.block_size = 32;
            opt.compressor = SnappyCompressor.id();

            {
                // Uses the standard comparator in opt.
                let mut b = TableBuilder::new_raw(opt, &mut d);

                for &(k, v) in data.iter() {
                    b.add(k.as_bytes(), v.as_bytes()).unwrap();
                }

                b.build().unwrap();
            }

            let size = d.len();
            (d, size)
        }

        // Build a table containing keys in InternalKey format.
        fn build_internal_table() -> (Vec<u8>, usize) {
            let mut d = Vec::with_capacity(512);
            let mut opt = Options::for_test();
            opt.block_restart_interval = 1;
            opt.block_size = 32;
            opt.filter_policy = Rc::new(BloomFilterPolicy::new(4));

            let mut i = 1 as u64;
            let data: Vec<(Vec<u8>, &'static str)> = build_data()
                .into_iter()
                .map(|(k, v)| {
                    i += 1;
                    (LookupKey::new(k.as_bytes(), i).internal_key().to_vec(), v)
                })
                .collect();

            {
                // Uses InternalKeyCmp
                let mut b = TableBuilder::new(opt, &mut d);

                for &(ref k, ref v) in data.iter() {
                    b.add(k.as_slice(), v.as_bytes()).unwrap();
                }

                b.build().unwrap();
            }

            let size = d.len();

            (d, size)
        }

        fn wrap_buffer(src: Vec<u8>) -> Rc<dyn RandomAccess> {
            Rc::new(src)
        }

        #[test]
        fn test_table_approximate_offset() {
            let (src, size) = build_table(build_data());
            let mut opt = Options::for_test();
            opt.block_size = 32;
            let table = Table::new_raw(opt, wrap_buffer(src), size).unwrap();
            let mut iter = table.iter();

            let expected_offsets = vec![0, 0, 0, 44, 44, 44, 89];
            let mut i = 0;
            for (k, _) in DbIteratorWrapper::new(&mut iter) {
                assert_eq!(expected_offsets[i], table.approx_offset(&k));
                i += 1;
            }

            // Key-past-last returns offset of metaindex block.
            assert_eq!(137, table.approx_offset("{aa".as_bytes()));
        }

        #[test]
        fn test_table_block_cache_use() {
            let (src, size) = build_table(build_data());
            let mut opt = Options::for_test();
            opt.block_size = 32;

            let table = Table::new_raw(opt.clone(), wrap_buffer(src), size).unwrap();
            let mut iter = table.iter();

            // index/metaindex blocks are not cached. That'd be a waste of memory.
            assert_eq!(opt.block_cache.borrow().size(), 0);

            iter.next();
            assert_eq!(opt.block_cache.borrow().size(), 1);
            // This may fail if block parameters or data change. In that case, adapt it.
            iter.next();
            iter.next();
            iter.next();
            iter.next();
            assert_eq!(opt.block_cache.borrow().size(), 2);
        }

        #[test]
        fn test_table_iterator_fwd_bwd() {
            let (src, size) = build_table(build_data());
            let data = build_data();

            let table = Table::new_raw(Options::for_test(), wrap_buffer(src), size).unwrap();
            let mut iter = table.iter();
            let mut i = 0;

            while let Some((k, v)) = iter.next() {
                assert_eq!(
                    (data[i].0.as_bytes(), data[i].1.as_bytes()),
                    (k.as_ref(), v.as_ref())
                );
                i += 1;
            }

            assert_eq!(i, data.len());
            assert!(!iter.valid());

            // Go forward again, to last entry.
            while let Some((key, _)) = iter.next() {
                if key.as_slice() == b"zzz" {
                    break;
                }
            }

            assert!(iter.valid());
            // backwards count
            let mut j = 0;

            while iter.prev() {
                if let Some((k, v)) = iter.current_kv() {
                    j += 1;
                    assert_eq!(
                        (
                            data[data.len() - 1 - j].0.as_bytes(),
                            data[data.len() - 1 - j].1.as_bytes()
                        ),
                        (k.as_ref(), v.as_ref())
                    );
                } else {
                    break;
                }
            }

            // expecting 7 - 1, because the last entry that the iterator stopped on is the last entry
            // in the table; that is, it needs to go back over 6 entries.
            assert_eq!(j, 6);
        }

        #[test]
        fn test_table_iterator_filter() {
            let (src, size) = build_table(build_data());

            let table = Table::new_raw(Options::for_test(), wrap_buffer(src), size).unwrap();
            assert!(table.filters.is_some());
            let filter_reader = table.filters.clone().unwrap();
            let mut iter = table.iter();

            loop {
                if let Some((k, _)) = iter.next() {
                    assert!(filter_reader.may_exist(iter.current_block_offset, &k));
                    assert!(!filter_reader.may_exist(iter.current_block_offset, b"somerandomkey"));
                } else {
                    break;
                }
            }
        }

        #[test]
        fn test_table_iterator_state_behavior() {
            let (src, size) = build_table(build_data());

            let table = Table::new_raw(Options::for_test(), wrap_buffer(src), size).unwrap();
            let mut iter = table.iter();

            // behavior test

            // See comment on valid()
            assert!(!iter.valid());
            assert!(iter.current_kv().is_none());
            assert!(!iter.prev());

            assert!(iter.advance());
            let first = iter.current_kv();
            assert!(iter.valid());
            assert!(iter.current_kv().is_some());

            assert!(iter.advance());
            assert!(iter.prev());
            assert!(iter.valid());

            iter.reset();
            assert!(!iter.valid());
            assert!(iter.current_kv().is_none());
            assert_eq!(first, iter.next());
        }

        #[test]
        fn test_table_iterator_behavior_standard() {
            let mut data = build_data();
            data.truncate(4);
            let (src, size) = build_table(data);
            let table = Table::new_raw(Options::for_test(), wrap_buffer(src), size).unwrap();
            test_iterator_properties(table.iter());
        }

        #[test]
        fn test_table_iterator_values() {
            let (src, size) = build_table(build_data());
            let data = build_data();

            let table = Table::new_raw(Options::for_test(), wrap_buffer(src), size).unwrap();
            let mut iter = table.iter();
            let mut i = 0;

            iter.next();
            iter.next();

            // Go back to previous entry, check, go forward two entries, repeat
            // Verifies that prev/next works well.
            loop {
                iter.prev();

                if let Some((k, v)) = iter.current_kv() {
                    assert_eq!(
                        (data[i].0.as_bytes(), data[i].1.as_bytes()),
                        (k.as_ref(), v.as_ref())
                    );
                } else {
                    break;
                }

                i += 1;
                if iter.next().is_none() || iter.next().is_none() {
                    break;
                }
            }

            // Skipping the last value because the second next() above will break the loop
            assert_eq!(i, 6);
        }

        #[test]
        fn test_table_iterator_seek() {
            let (src, size) = build_table(build_data());

            let table = Table::new_raw(Options::for_test(), wrap_buffer(src), size).unwrap();
            let mut iter = table.iter();

            iter.seek(b"bcd");
            assert!(iter.valid());
            assert_eq!(iter.current_kv(), Some((b"bcd".to_vec(), b"asa".to_vec())));
            iter.seek(b"abc");
            assert!(iter.valid());
            assert_eq!(iter.current_kv(), Some((b"abc".to_vec(), b"def".to_vec())));

            // Seek-past-last invalidates.
            iter.seek("{{{".as_bytes());
            assert!(!iter.valid());
            iter.seek(b"bbb");
            assert!(iter.valid());
        }

        #[test]
        fn test_table_get() {
            let (src, size) = build_table(build_data());

            let table = Table::new_raw(Options::for_test(), wrap_buffer(src), size).unwrap();
            let table2 = table.clone();

            let mut _iter = table.iter();
            // Test that all of the table's entries are reachable via get()
            for (k, v) in DbIteratorWrapper::new(&mut _iter) {
                let r = table2.get(&k);
                assert_eq!(Ok(Some((k, v))), r);
            }

            assert_eq!(table.options.block_cache.borrow().size(), 3);

            // test that filters work and don't return anything at all.
            assert!(table.get(b"aaa").unwrap().is_none());
            assert!(table.get(b"aaaa").unwrap().is_none());
            assert!(table.get(b"aa").unwrap().is_none());
            assert!(table.get(b"abcd").unwrap().is_none());
            assert!(table.get(b"abb").unwrap().is_none());
            assert!(table.get(b"zzy").unwrap().is_none());
            assert!(table.get(b"zz1").unwrap().is_none());
            assert!(table.get("zz{".as_bytes()).unwrap().is_none());
        }

        // This test verifies that the table and filters work with internal keys. This means:
        // The table contains keys in InternalKey format and it uses a filter wrapped by
        // InternalFilterPolicy.
        // All the other tests use raw keys that don't have any internal structure; this is fine in
        // general, but here we want to see that the other infrastructure works too.
        #[test]
        fn test_table_internal_keys() {
            let (src, size) = build_internal_table();

            let table = Table::new(Options::for_test(), wrap_buffer(src), size).unwrap();
            let filter_reader = table.filters.clone().unwrap();

            // Check that we're actually using internal keys
            let mut _iter = table.iter();
            for (ref k, ref v) in DbIteratorWrapper::new(&mut _iter) {
                assert_eq!(k.len(), 3 + 8);
                assert_eq!((k.to_vec(), v.to_vec()), table.get(k).unwrap().unwrap());
            }

            assert!(table
                .get(LookupKey::new(b"abc", 1000).internal_key())
                .unwrap()
                .is_some());

            let mut iter = table.iter();

            loop {
                if let Some((k, _)) = iter.next() {
                    let lk = LookupKey::new(&k, 123);
                    let userkey = lk.user_key();

                    assert!(filter_reader.may_exist(iter.current_block_offset, userkey));
                    assert!(!filter_reader.may_exist(iter.current_block_offset, b"somerandomkey"));
                } else {
                    break;
                }
            }
        }

        #[test]
        fn test_table_reader_checksum() {
            let (mut src, size) = build_table(build_data());

            src[10] += 1;

            let table = Table::new_raw(Options::for_test(), wrap_buffer(src), size).unwrap();

            assert!(table.filters.is_some());
            assert_eq!(table.filters.as_ref().unwrap().num_filters(), 1);

            {
                let mut _iter = table.iter();
                let iter = DbIteratorWrapper::new(&mut _iter);
                // first block is skipped
                assert_eq!(iter.count(), 4);
            }

            {
                let mut _iter = table.iter();
                let iter = DbIteratorWrapper::new(&mut _iter);

                for (k, _) in iter {
                    if k == build_data()[5].0.as_bytes() {
                        return;
                    }
                }

                panic!("Should have hit 5th record in table!");
            }
        }
    }
}
