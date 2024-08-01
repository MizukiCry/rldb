//! rldb: a reimplementation of LevelDB refering to leveldb-rs
//!
//! ```
//! use rldb::{Database, DbIterator, DatabaseIter, Options};
//!
//! let options = Options::in_memory();
//! let mut db = Database::open("mydatabase", options).unwrap();
//!
//! db.insert(b"Hello", b"World").unwrap();
//! assert_eq!(b"World", db.get(b"Hello").unwrap().as_slice());
//!
//! let mut iter = db.new_iter().unwrap();
//! // Note: For efficiency reasons, it's recommended to use advance() and current() instead of
//! // next() when iterating over many elements.
//! assert_eq!((b"Hello".to_vec(), b"World".to_vec()), iter.next().unwrap());
//!
//! db.delete(b"Hello").unwrap();
//! db.flush().unwrap();
//! ```
//!

mod coredef;
mod storage;
mod utils;

pub use coredef::{
    cmp::{Cmp, DefaultCmp},
    compressor::{self, Compressor},
    env::mem_env::MemEnv,
    error::{Result, Status, StatusCode},
    options::{CompressorList, Options},
    types::DbIterator,
};

pub use storage::{database::Database, database_iter::DatabaseIter, write_batch::WriteBatch};

pub use utils::{
    filter::{BloomFilterPolicy, FilterPolicy},
    skip_list::SkipList,
};

#[cfg(feature = "fs")]
pub use coredef::env::disk_env::PosixDiskEnv;

#[cfg(feature = "fs")]
extern crate errno;

#[cfg(feature = "fs")]
extern crate fs2;

extern crate crc;
extern crate integer_encoding;
extern crate rand;
extern crate snap;

#[cfg(feature = "async")]
mod asyncdb;
#[cfg(feature = "async")]
pub use asyncdb::AsyncDB;
