use std::rc::Rc;

use super::cmp::{Cmp, DefaultCmp};
use super::compressor::Compressor;
use super::env::{disk_env::PosixDiskEnv, mem_env::MemEnv, Env};
use super::error::Result;
use crate::storage::block::Block;

const MAX_BLOCK_SIZE: usize = 4 * 1024; // 4KB

#[cfg(feature = "fs")]
type DefaultEnv = PosixDiskEnv;
#[cfg(not(feature = "fs"))]
type DefaultEnv = MemEnv;

#[derive(Clone)]
pub struct Options {
    pub cmp: Rc<dyn Cmp>,
    pub env: Rc<dyn Env>,

    pub block_size: usize,

    // Number of keys per restart point
    pub block_restart_interval: usize,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            cmp: Rc::new(DefaultCmp),
            env: Rc::new(DefaultEnv::new()),
            block_size: MAX_BLOCK_SIZE,
            block_restart_interval: 16,
        }

        // todo!()
    }
}
