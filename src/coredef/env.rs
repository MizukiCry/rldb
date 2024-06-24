//! An abstraction for key-value storage

pub mod disk_env;
pub mod mem_env;

use super::error::Result;
use std::fs::File;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::time::{self, Duration};

#[cfg(unix)]
use std::os::unix::fs::FileExt;
#[cfg(windows)]
use std::os::windows::fs::FileExt;

pub trait RandomAccess {
    fn read(&self, offset: usize, dst: &mut [u8]) -> Result<usize>;
}

#[cfg(unix)]
impl RandomAccess for File {
    fn read(&self, offset: usize, dst: &mut [u8]) -> Result<usize> {
        Ok((self as &dyn FileExt).read_at(dst, offset as u64)?)
    }
}

#[cfg(windows)]
impl RandomAccess for File {
    fn read(&self, offset: usize, dst: &mut [u8]) -> Result<usize> {
        Ok((self as &dyn FileExt).seek_read(dst, offset as u64)?)
    }
}

pub struct FileLock {
    pub id: String,
}

pub trait Env {
    fn open_sequential_file(&self, p: &Path) -> Result<Box<dyn Read>>;
    fn open_random_access_file(&self, p: &Path) -> Result<Box<dyn RandomAccess>>;
    fn open_writable_file(&self, p: &Path) -> Result<Box<dyn Write>>;
    fn open_appendable_file(&self, p: &Path) -> Result<Box<dyn Write>>;

    fn exists(&self, p: &Path) -> Result<bool>;
    fn size_of(&self, p: &Path) -> Result<usize>;
    fn children(&self, p: &Path) -> Result<Vec<PathBuf>>;

    fn delete(&self, p: &Path) -> Result<()>;
    fn mkdir(&self, p: &Path) -> Result<()>;
    fn rmdir(&self, p: &Path) -> Result<()>;
    fn rename(&self, old: &Path, new: &Path) -> Result<()>;

    fn lock(&self, p: &Path) -> Result<FileLock>;
    fn unlock(&self, lock: FileLock) -> Result<()>;

    fn micros(&self) -> u64 {
        time::SystemTime::now()
            .duration_since(time::UNIX_EPOCH)
            .unwrap()
            .as_micros() as u64
    }

    fn sleep_for(&self, micros: u64) {
        std::thread::sleep(Duration::from_micros(micros))
    }
}
