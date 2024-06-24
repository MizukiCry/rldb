//! On-disk implementation of Env.

use super::{Env, FileLock, RandomAccess};
use crate::coredef::error::{err, Result, Status, StatusCode};
use fs2::FileExt;
use std::collections::HashMap;
use std::fs::{self, File, OpenOptions};
use std::io::{self, ErrorKind, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

pub struct PosixDiskEnv {
    locks: Arc<Mutex<HashMap<String, File>>>,
}

impl PosixDiskEnv {
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self {
            locks: Arc::new(Mutex::new(HashMap::new())),
        }
    }
}

fn format_err(method: &'static str, e: io::Error, p: &Path) -> Status {
    let mut status = Status::from(e);
    status.err = format!("{}: {}: {}", method, status.err, p.display());
    status
}

impl Env for PosixDiskEnv {
    fn open_sequential_file(&self, p: &Path) -> Result<Box<dyn Read>> {
        Ok(Box::new(
            OpenOptions::new()
                .read(true)
                .open(p)
                .map_err(|e| format_err("open (seq)", e, p))?,
        ))
    }

    fn open_random_access_file(&self, p: &Path) -> Result<Box<dyn RandomAccess>> {
        Ok(Box::new(
            OpenOptions::new()
                .read(true)
                .open(p)
                .map_err(|e| format_err("open(random)", e, p))?,
        ))
    }

    fn open_writable_file(&self, p: &Path) -> Result<Box<dyn Write>> {
        Ok(Box::new(
            OpenOptions::new()
                .create(true)
                .write(true)
                .append(false)
                .open(p)
                .map_err(|e| format_err("open (write)", e, p))?,
        ))
    }

    fn open_appendable_file(&self, p: &Path) -> Result<Box<dyn Write>> {
        Ok(Box::new(
            OpenOptions::new()
                .create(true)
                .write(true)
                .append(true)
                .open(p)
                .map_err(|e| format_err("open (append)", e, p))?,
        ))
    }

    fn exists(&self, p: &Path) -> Result<bool> {
        Ok(p.exists())
    }

    fn size_of(&self, p: &Path) -> Result<usize> {
        Ok(fs::metadata(p)
            .map_err(|e| format_err("size_of", e, p))?
            .len() as usize)
    }

    fn children(&self, p: &Path) -> Result<Vec<PathBuf>> {
        let dir = fs::read_dir(p).map_err(|e| format_err("children", e, p))?;
        Ok(dir
            .filter_map(|item| {
                item.ok()
                    .map(|entry| Path::new(&entry.file_name()).to_path_buf())
            })
            .collect())
    }

    fn delete(&self, p: &Path) -> Result<()> {
        Ok(fs::remove_file(p).map_err(|e| format_err("delete", e, p))?)
    }

    fn mkdir(&self, p: &Path) -> Result<()> {
        Ok(fs::create_dir_all(p).map_err(|e| format_err("mkdir", e, p))?)
    }

    fn rmdir(&self, p: &Path) -> Result<()> {
        Ok(fs::remove_dir_all(p).map_err(|e| format_err("rmdir", e, p))?)
    }

    fn rename(&self, old: &Path, new: &Path) -> Result<()> {
        Ok(fs::rename(old, new).map_err(|e| format_err("rename", e, old))?)
    }

    fn lock(&self, p: &Path) -> Result<FileLock> {
        let p_string = p.to_str().unwrap().to_string();
        let mut locks = self.locks.lock().unwrap();

        if locks.contains_key(&p_string) {
            return err(StatusCode::AlreadyExists, "file already locked");
        }

        let f = OpenOptions::new()
            .write(true)
            .create(true)
            .open(p)
            .map_err(|e| format_err("lock", e, p))?;

        if let Err(e) = f.try_lock_exclusive() {
            if e.kind() == ErrorKind::WouldBlock {
                return err(
                    StatusCode::LockError,
                    "file already locked by another process",
                );
            }
            return err(
                StatusCode::Errno(errno::errno()),
                &format!("unknown error on file {:?} (file {})", f, p.display()),
            );
        }

        locks.insert(p_string.clone(), f);
        Ok(FileLock { id: p_string })
    }

    fn unlock(&self, lock: FileLock) -> Result<()> {
        let mut locks = self.locks.lock().unwrap();
        if !locks.contains_key(&lock.id) {
            return err(
                StatusCode::LockError,
                &format!("file not locked: {}", lock.id),
            );
        }
        if let Err(e) = locks.remove(&lock.id).unwrap().unlock() {
            return err(
                StatusCode::LockError,
                &format!("failed to unlock file {}: {}", lock.id, e),
            );
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests_leveldb_rs {
        use super::*;

        #[test]
        fn test_files() {
            let n = "testfile.xyz".to_string();
            let name = n.as_ref();
            let env = PosixDiskEnv::new();

            // exists, size_of, delete
            assert!(env.open_appendable_file(name).is_ok());
            assert!(env.exists(name).unwrap_or(false));
            assert_eq!(env.size_of(name).unwrap_or(1), 0);
            assert!(env.delete(name).is_ok());

            assert!(env.open_writable_file(name).is_ok());
            assert!(env.exists(name).unwrap_or(false));
            assert_eq!(env.size_of(name).unwrap_or(1), 0);
            assert!(env.delete(name).is_ok());

            {
                // write
                let mut f = env.open_writable_file(name).unwrap();
                let _ = f.write("123xyz".as_bytes());
                assert_eq!(6, env.size_of(name).unwrap_or(0));

                // rename
                let newname = Path::new("testfile2.xyz");
                assert!(env.rename(name, newname).is_ok());
                assert_eq!(6, env.size_of(newname).unwrap());
                assert!(!env.exists(name).unwrap());
                // rename back so that the remaining tests can use the file.
                assert!(env.rename(newname, name).is_ok());
            }

            assert!(env.open_sequential_file(name).is_ok());
            assert!(env.open_random_access_file(name).is_ok());

            assert!(env.delete(name).is_ok());
        }

        #[test]
        fn test_locking() {
            let env = PosixDiskEnv::new();
            let n = "testfile.123".to_string();
            let name = n.as_ref();

            {
                let mut f = env.open_writable_file(name).unwrap();
                let _ = f.write("123xyz".as_bytes());
                assert_eq!(env.size_of(name).unwrap_or(0), 6);
            }

            {
                let r = env.lock(name);
                assert!(r.is_ok());
                env.unlock(r.unwrap()).unwrap();
            }

            {
                let r = env.lock(name);
                assert!(r.is_ok());
                let s = env.lock(name);
                assert!(s.is_err());
                env.unlock(r.unwrap()).unwrap();
            }

            assert!(env.delete(name).is_ok());
        }

        #[test]
        fn test_dirs() {
            let d = "subdir/";
            let dirname = d.as_ref();
            let env = PosixDiskEnv::new();

            assert!(env.mkdir(dirname).is_ok());
            assert!(env
                .open_writable_file(
                    String::from_iter(vec![d.to_string(), "f1.txt".to_string()].into_iter())
                        .as_ref()
                )
                .is_ok());
            assert_eq!(env.children(dirname).unwrap().len(), 1);
            assert!(env.rmdir(dirname).is_ok());
        }
    }

    mod tests_gpt_4o {
        use super::*;

        #[test]
        fn test_open_sequential_file() {
            let env = PosixDiskEnv::new();
            let path = Path::new("test_sequential_file.txt");

            // Create and write to the file
            let mut file = env.open_writable_file(path).unwrap();
            file.write_all(b"Hello, world!").unwrap();
            drop(file);

            // Open sequentially and read
            let mut seq_file = env.open_sequential_file(path).unwrap();
            let mut buffer = String::new();
            seq_file.read_to_string(&mut buffer).unwrap();
            assert_eq!(buffer, "Hello, world!");

            // Clean up
            env.delete(path).unwrap();
        }

        // #[test]
        // fn test_open_random_access_file() {
        //     let env = PosixDiskEnv::new();
        //     let path = Path::new("test_random_access_file.txt");

        //     // Create and write to the file
        //     let mut file = env.open_writable_file(path).unwrap();
        //     file.write_all(b"Hello, world!").unwrap();
        //     drop(file);

        //     // Open with random access and read
        //     let mut rand_file = env.open_random_access_file(path).unwrap();
        //     let mut buffer = [0; 5];
        //     rand_file.read_at(&mut buffer, 7).unwrap();
        //     assert_eq!(&buffer, b"world");

        //     // Clean up
        //     env.delete(path).unwrap();
        // }

        #[test]
        fn test_open_writable_file() {
            let env = PosixDiskEnv::new();
            let path = Path::new("test_writable_file.txt");

            // Open writable and write
            let mut file = env.open_writable_file(path).unwrap();
            file.write_all(b"Hello, world!").unwrap();

            // Verify size
            assert_eq!(env.size_of(path).unwrap(), 13);

            // Clean up
            env.delete(path).unwrap();
        }

        #[test]
        fn test_open_appendable_file() {
            let env = PosixDiskEnv::new();
            let path = Path::new("test_appendable_file.txt");

            // Open writable and write
            let mut file = env.open_writable_file(path).unwrap();
            file.write_all(b"Hello,").unwrap();
            drop(file);

            // Open appendable and write
            let mut file = env.open_appendable_file(path).unwrap();
            file.write_all(b" world!").unwrap();
            drop(file);

            // Verify content
            let mut seq_file = env.open_sequential_file(path).unwrap();
            let mut buffer = String::new();
            seq_file.read_to_string(&mut buffer).unwrap();
            assert_eq!(buffer, "Hello, world!");

            // Clean up
            env.delete(path).unwrap();
        }

        #[test]
        fn test_exists() {
            let env = PosixDiskEnv::new();
            let path = Path::new("test_exists_file.txt");

            // Initially should not exist
            assert!(!env.exists(path).unwrap());

            // Create the file
            let _ = env.open_writable_file(path).unwrap();

            // Should exist now
            assert!(env.exists(path).unwrap());

            // Clean up
            env.delete(path).unwrap();
        }

        #[test]
        fn test_size_of() {
            let env = PosixDiskEnv::new();
            let path = Path::new("test_size_of_file.txt");

            // Create and write to the file
            let mut file = env.open_writable_file(path).unwrap();
            file.write_all(b"Hello, world!").unwrap();

            // Verify size
            assert_eq!(env.size_of(path).unwrap(), 13);

            // Clean up
            env.delete(path).unwrap();
        }

        #[test]
        fn test_children() {
            let env = PosixDiskEnv::new();
            let dir = Path::new("test_dir");

            // Create directory and files
            env.mkdir(dir).unwrap();
            env.open_writable_file(&dir.join("file1.txt")).unwrap();
            env.open_writable_file(&dir.join("file2.txt")).unwrap();

            // Verify children
            let children = env.children(dir).unwrap();
            assert_eq!(children.len(), 2);

            // Clean up
            env.delete(&dir.join("file1.txt")).unwrap();
            env.delete(&dir.join("file2.txt")).unwrap();
            env.rmdir(dir).unwrap();
        }

        #[test]
        fn test_delete() {
            let env = PosixDiskEnv::new();
            let path = Path::new("test_delete_file.txt");

            // Create the file
            let _ = env.open_writable_file(path).unwrap();

            // Delete the file
            env.delete(path).unwrap();

            // Verify deletion
            assert!(!env.exists(path).unwrap());
        }

        #[test]
        fn test_mkdir_rmdir() {
            let env = PosixDiskEnv::new();
            let dir = Path::new("test_mkdir_rmdir_dir");

            // Create the directory
            env.mkdir(dir).unwrap();

            // Verify existence
            assert!(env.exists(dir).unwrap());

            // Remove the directory
            env.rmdir(dir).unwrap();

            // Verify removal
            assert!(!env.exists(dir).unwrap());
        }

        #[test]
        fn test_rename() {
            let env = PosixDiskEnv::new();
            let old_path = Path::new("test_rename_old.txt");
            let new_path = Path::new("test_rename_new.txt");

            // Create the file
            let _ = env.open_writable_file(old_path).unwrap();

            // Rename the file
            env.rename(old_path, new_path).unwrap();

            // Verify renaming
            assert!(!env.exists(old_path).unwrap());
            assert!(env.exists(new_path).unwrap());

            // Clean up
            env.delete(new_path).unwrap();
        }

        #[test]
        fn test_lock_unlock() {
            let env = PosixDiskEnv::new();
            let path = Path::new("test_lock_unlock_file.txt");

            // Create the file
            let _ = env.open_writable_file(path).unwrap();

            // Lock the file
            let lock = env.lock(path).unwrap();

            // Verify locking
            assert!(env.lock(path).is_err());

            // Unlock the file
            env.unlock(lock).unwrap();

            // Verify unlocking
            let lock = env.lock(path).unwrap();
            env.unlock(lock).unwrap();

            // Clean up
            env.delete(path).unwrap();
        }
    }
}
