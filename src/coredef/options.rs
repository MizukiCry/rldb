use std::cell::RefCell;
use std::rc::Rc;

use super::cmp::{Cmp, DefaultCmp};
use super::compressor::{Compressor, NoneCompressor, SnappyCompressor};
use super::env::{disk_env::PosixDiskEnv, mem_env::MemEnv, Env};
use super::error::{Result, Status, StatusCode};
use super::log::{stderr, Logger};
use crate::storage::block::Block;
use crate::utils::cache::Cache;
use crate::utils::filter::{BloomFilterPolicy, FilterPolicy};

/// Customizable compressor list
pub struct CompressorList([Option<Box<dyn Compressor>>; 256]);

impl Default for CompressorList {
    fn default() -> Self {
        let mut list = Self::new();
        list.set(NoneCompressor);
        list.set(SnappyCompressor);
        list
    }
}

impl CompressorList {
    pub fn new() -> Self {
        const NO_COMPRESSOR: Option<Box<dyn Compressor>> = None;
        Self([NO_COMPRESSOR; 256])
    }

    pub fn set(&mut self, compressor: impl Compressor + 'static) {
        self.set_with_id(compressor.id(), compressor);
    }

    pub fn set_with_id(&mut self, id: u8, compressor: impl Compressor + 'static) {
        self.0[id as usize] = Some(Box::new(compressor));
    }

    pub fn exists(&self, id: u8) -> bool {
        self.0[id as usize].is_some()
    }

    pub fn get(&self, id: u8) -> Result<&(dyn Compressor + 'static)> {
        // self.0[id as usize].as_ref().ok_or_else(|| {
        //     Status::new(
        //         StatusCode::NotSupported,
        //         &format!("Compressor with id {} not found", id),
        //     )
        // })
        self.0[id as usize]
            .as_ref()
            .map(|c| c.as_ref())
            .ok_or_else(|| {
                Status::new(
                    StatusCode::NotSupported,
                    &format!("Compressor with id {} not found", id),
                )
            })
    }
}

const MAX_BLOCK_SIZE: usize = 4 * 1024; // 4KB
const BLOCK_CACHE_CAPACITY: usize = 8 * 1024 * 1024; // 8MB
const WRITE_BUFFER_SIZE: usize = 4 * 1024 * 1024; // 4MB
const DEFAULT_BITS_PER_KEY: u32 = 10;

#[cfg(feature = "fs")]
type DefaultEnv = PosixDiskEnv;
#[cfg(not(feature = "fs"))]
type DefaultEnv = MemEnv;

#[derive(Clone)]
pub struct Options {
    pub cmp: Rc<dyn Cmp>,
    pub env: Rc<dyn Env>,
    pub log: Option<Rc<RefCell<Logger>>>,

    pub create_if_missing: bool,
    pub error_if_exists: bool,
    pub paranoid_checks: bool,

    pub write_buffer_size: usize,
    pub max_open_files: usize,
    pub max_file_size: usize,
    pub block_cache: Rc<RefCell<Cache<Block>>>,
    pub block_size: usize,
    pub block_restart_interval: usize,

    pub compressor: u8,
    pub compressor_list: Rc<CompressorList>,

    pub reuse_logs: bool,
    pub reuse_manifest: bool,

    pub filter_policy: Rc<dyn FilterPolicy>,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            cmp: Rc::new(DefaultCmp),
            env: Rc::new(DefaultEnv::new()),
            log: None,
            create_if_missing: true,
            error_if_exists: false,
            paranoid_checks: false,
            write_buffer_size: WRITE_BUFFER_SIZE,
            max_open_files: 1024,
            max_file_size: 2 * 1024 * 1024, // 2MB
            block_cache: Rc::new(RefCell::new(Cache::new(
                BLOCK_CACHE_CAPACITY / MAX_BLOCK_SIZE,
            ))),
            block_size: MAX_BLOCK_SIZE,
            block_restart_interval: 16,
            reuse_logs: true,
            reuse_manifest: true,
            compressor: 0,
            compressor_list: Rc::new(CompressorList::default()),
            filter_policy: Rc::new(BloomFilterPolicy::new(DEFAULT_BITS_PER_KEY)),
        }

        // todo!()
    }
}

impl Options {
    pub fn in_memory() -> Self {
        Self {
            env: Rc::new(MemEnv::new()),
            ..Self::default()
        }
    }

    pub fn for_test() -> Self {
        Self {
            log: Some(Rc::new(RefCell::new(stderr()))),
            ..Self::in_memory()
        }
    }
}
