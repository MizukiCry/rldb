//! In-memory implementation of Env.

use super::{Env, FileLock, RandomAccess};
use crate::coredef::error::{err, Result, StatusCode};
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

/// A file type based on `Vec<u8>`.
type VecFile = Vec<u8>;

impl RandomAccess for VecFile {
    fn read(&self, offset: usize, dst: &mut [u8]) -> Result<usize> {
        if offset >= self.len() {
            return Ok(0);
        }
        let len = dst.len().min(self.len() - offset);
        (&mut dst[..len]).copy_from_slice(&self[offset..offset + len]);
        Ok(len)
    }
}

/// A thread-safe wrapper around `VecFile`.
#[derive(Clone)]
pub struct MemFile(Arc<Mutex<VecFile>>);

impl MemFile {
    fn new() -> Self {
        Self(Arc::new(Mutex::new(Vec::new())))
    }
}

impl RandomAccess for MemFile {
    fn read(&self, offset: usize, dst: &mut [u8]) -> Result<usize> {
        self.0.lock().unwrap().read(offset, dst)
    }
}

/// A reference to a MemFile and the offset
struct MemFileReader(MemFile, usize);

impl MemFileReader {
    fn new(file: MemFile, offset: usize) -> Self {
        Self(file, offset)
    }
}

impl Read for MemFileReader {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let src = self.0 .0.lock().unwrap();
        if self.1 >= src.len() {
            return Ok(0);
        }

        let len = buf.len().min(src.len() - self.1);
        (&mut buf[..len]).copy_from_slice(&src[self.1..self.1 + len]);
        self.1 += len;
        Ok(len)
    }
}

/// A reference to a MemFile and the offset
struct MemFileWriter(MemFile, usize);

impl MemFileWriter {
    fn new(file: MemFile, append: bool) -> Self {
        let offset = if append {
            file.0.lock().unwrap().len()
        } else {
            0
        };
        Self(file, offset)
    }
}

impl Write for MemFileWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let mut dst = self.0 .0.lock().unwrap();
        let copy_len = std::cmp::min(dst.len() - self.1, buf.len());

        (&mut dst[self.1..self.1 + copy_len]).copy_from_slice(&buf[..copy_len]);
        dst.extend_from_slice(&buf[copy_len..]);

        self.1 += buf.len();
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

struct MemEnvEntry {
    file: MemFile,
    locked: bool,
}

/// An in-memory environment.
pub struct MemEnv(Arc<Mutex<HashMap<String, MemEnvEntry>>>);

impl Default for MemEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl MemEnv {
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self(Arc::new(Mutex::new(HashMap::new())))
    }

    fn open(&self, p: &Path, create: bool) -> Result<MemFile> {
        let mut map = self.0.lock()?;
        match map.entry(p.to_str().unwrap().to_string()) {
            Entry::Occupied(entry) => Ok(entry.get().file.clone()),
            Entry::Vacant(entry) => {
                if !create {
                    return err(
                        StatusCode::NotFound,
                        &format!("open_read: file not found: {}", p.display()),
                    );
                }
                let file = MemFile::new();
                entry.insert(MemEnvEntry {
                    file: file.clone(),
                    locked: false,
                });
                Ok(file)
            }
        }
    }

    fn open_write(&self, p: &Path, append: bool, truncate: bool) -> Result<Box<dyn Write>> {
        let file = self.open(p, true)?;
        if truncate {
            file.0.lock().unwrap().clear();
        }
        Ok(Box::new(MemFileWriter::new(file, append)))
    }
}

impl Env for MemEnv {
    fn open_sequential_file(&self, p: &Path) -> Result<Box<dyn Read>> {
        Ok(Box::new(MemFileReader::new(self.open(p, false)?, 0)))
    }

    fn open_random_access_file(&self, p: &Path) -> Result<Box<dyn RandomAccess>> {
        Ok(Box::new(self.open(p, false)?))
    }

    fn open_writable_file(&self, p: &Path) -> Result<Box<dyn Write>> {
        self.open_write(p, true, true)
    }

    fn open_appendable_file(&self, p: &Path) -> Result<Box<dyn Write>> {
        self.open_write(p, true, false)
    }

    fn exists(&self, p: &Path) -> Result<bool> {
        Ok(self
            .0
            .lock()?
            .contains_key(&p.to_str().unwrap().to_string()))
    }

    fn size_of(&self, p: &Path) -> Result<usize> {
        match self.0.lock()?.entry(p.to_str().unwrap().to_string()) {
            Entry::Occupied(entry) => Ok(entry.get().file.0.lock()?.len()),
            _ => err(
                StatusCode::NotFound,
                &format!("file not found: {}", p.display()),
            ),
        }
    }

    fn children(&self, p: &Path) -> Result<Vec<PathBuf>> {
        let mut prefix = p.to_str().unwrap().to_string();
        if !prefix.ends_with(std::path::MAIN_SEPARATOR) {
            prefix.push(std::path::MAIN_SEPARATOR);
        }

        let mut children = Vec::new();
        let map = self.0.lock()?;
        for key in map.keys() {
            if key.starts_with(&prefix) {
                children.push(Path::new(key.strip_prefix(&prefix).unwrap_or(key)).to_owned());
            }
        }

        Ok(children)
    }

    fn delete(&self, p: &Path) -> Result<()> {
        match self.0.lock()?.entry(p.to_str().unwrap().to_string()) {
            Entry::Occupied(entry) => {
                entry.remove_entry();
                Ok(())
            }
            _ => err(
                StatusCode::NotFound,
                &format!("delete: file not found: {}", p.display()),
            ),
        }
    }

    fn mkdir(&self, p: &Path) -> Result<()> {
        if self.exists(p)? {
            err(
                StatusCode::AlreadyExists,
                &format!("mkdir: path exists: {}", p.display()),
            )
        } else {
            Ok(())
        }
    }

    fn rmdir(&self, p: &Path) -> Result<()> {
        if !self.exists(p)? {
            err(
                StatusCode::NotFound,
                &format!("rmdir: path not found: {}", p.display()),
            )
        } else {
            Ok(())
        }
    }

    fn rename(&self, old: &Path, new: &Path) -> Result<()> {
        let mut map = self.0.lock()?;
        match map.remove(old.to_str().unwrap()) {
            Some(entry) => {
                map.insert(new.to_str().unwrap().to_string(), entry);
                Ok(())
            }
            None => err(
                StatusCode::NotFound,
                &format!("rename: file not found: {}", old.display()),
            ),
        }
    }

    fn lock(&self, p: &Path) -> Result<FileLock> {
        let mut map = self.0.lock()?;
        match map.entry(p.to_str().unwrap().to_string()) {
            Entry::Occupied(mut entry) => {
                if entry.get().locked {
                    err(
                        StatusCode::LockError,
                        &format!("lock: file already locked: {}", p.display()),
                    )
                } else {
                    entry.get_mut().locked = true;
                    Ok(FileLock {
                        id: p.to_str().unwrap().to_string(),
                    })
                }
            }
            Entry::Vacant(entry) => {
                let file = MemFile::new();
                entry.insert(MemEnvEntry {
                    file: file.clone(),
                    locked: true,
                });
                Ok(FileLock {
                    id: p.to_str().unwrap().to_string(),
                })
            }
        }
    }

    fn unlock(&self, lock: FileLock) -> Result<()> {
        let mut map = self.0.lock()?;
        match map.entry(lock.id.clone()) {
            Entry::Occupied(mut entry) => {
                if !entry.get().locked {
                    err(
                        StatusCode::LockError,
                        &format!("unlock: file not locked: {}", lock.id),
                    )
                } else {
                    entry.get_mut().locked = false;
                    Ok(())
                }
            }
            Entry::Vacant(_) => err(
                StatusCode::NotFound,
                &format!("unlock: file not found: {}", lock.id),
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests_leveldb_rs {
        use super::*;

        fn new_memfile(v: Vec<u8>) -> MemFile {
            MemFile(Arc::new(Mutex::new(v)))
        }

        #[test]
        fn test_mem_fs_memfile_read() {
            let f = new_memfile(vec![1, 2, 3, 4, 5, 6, 7, 8]);
            let mut buf: [u8; 1] = [0];
            let mut reader = MemFileReader(f, 0);

            for i in [1, 2, 3, 4, 5, 6, 7, 8].iter() {
                assert_eq!(reader.read(&mut buf).unwrap(), 1);
                assert_eq!(buf, [*i]);
            }
        }

        #[test]
        fn test_mem_fs_memfile_write() {
            let f = new_memfile(vec![]);
            let mut w1 = MemFileWriter::new(f.clone(), false);
            assert_eq!(w1.write(&[1, 2, 3]).unwrap(), 3);

            let mut w2 = MemFileWriter::new(f, true);
            assert_eq!(w1.write(&[1, 7, 8, 9]).unwrap(), 4);
            assert_eq!(w2.write(&[4, 5, 6]).unwrap(), 3);

            assert_eq!(
                (w1.0).0.lock().unwrap().as_ref() as &Vec<u8>,
                &[1, 2, 3, 4, 5, 6, 9]
            );
        }

        #[test]
        fn test_mem_fs_memfile_readat() {
            let f = new_memfile(vec![1, 2, 3, 4, 5]);

            let mut buf = [0; 3];
            assert_eq!(f.read(2, &mut buf).unwrap(), 3);
            assert_eq!(buf, [3, 4, 5]);

            assert_eq!(f.read(0, &mut buf[0..1]).unwrap(), 1);
            assert_eq!(buf, [1, 4, 5]);

            assert_eq!(f.read(5, &mut buf).unwrap(), 0);
            assert_eq!(buf, [1, 4, 5]);

            let mut buf2 = [0; 6];
            assert_eq!(f.read(0, &mut buf2[0..5]).unwrap(), 5);
            assert_eq!(buf2, [1, 2, 3, 4, 5, 0]);
            assert_eq!(f.read(0, &mut buf2[0..6]).unwrap(), 5);
            assert_eq!(buf2, [1, 2, 3, 4, 5, 0]);
        }

        #[test]
        fn test_mem_fs_open_read_write() {
            let fs = MemEnv::new();
            let path = Path::new("/a/b/hello.txt");

            {
                let mut w = fs.open_write(&path, false, false).unwrap();
                write!(w, "Hello").unwrap();
                // Append.
                let mut w2 = fs.open_write(&path, true, false).unwrap();
                write!(w2, "World").unwrap();
            }
            {
                let mut r = MemFileReader::new(fs.open(&path, false).unwrap(), 0);
                let mut s = String::new();
                assert_eq!(r.read_to_string(&mut s).unwrap(), 10);
                assert_eq!(s, "HelloWorld");

                let mut r2 = MemFileReader::new(fs.open(&path, false).unwrap(), 2);
                s.clear();
                assert_eq!(r2.read_to_string(&mut s).unwrap(), 8);
                assert_eq!(s, "lloWorld");
            }
            assert_eq!(fs.size_of(&path).unwrap(), 10);
            assert!(fs.exists(&path).unwrap());
            assert!(!fs.exists(&Path::new("/non/existing/path")).unwrap());
        }

        #[test]
        fn test_mem_fs_open_read_write_append_truncate() {
            let fs = MemEnv::new();
            let path = Path::new("/a/b/hello.txt");

            {
                let mut w0 = fs.open_write(&path, false, true).unwrap();
                write!(w0, "Garbage").unwrap();

                // Truncate.
                let mut w = fs.open_write(&path, false, true).unwrap();
                write!(w, "Xyz").unwrap();
                // Write to the beginning.
                let mut w2 = fs.open_write(&path, false, false).unwrap();
                write!(w2, "OverwritingEverythingWithGarbage").unwrap();
                // Overwrite the overwritten stuff.
                write!(w, "Xyz").unwrap();
                assert!(w.flush().is_ok());
            }
            {
                let mut r = MemFileReader::new(fs.open(&path, false).unwrap(), 0);
                let mut s = String::new();
                assert_eq!(r.read_to_string(&mut s).unwrap(), 32);
                assert_eq!(s, "OveXyzitingEverythingWithGarbage");
            }
            assert!(fs.exists(&path).unwrap());
            assert_eq!(fs.size_of(&path).unwrap(), 32);
            assert!(!fs.exists(&Path::new("/non/existing/path")).unwrap());
        }

        #[test]
        fn test_mem_fs_metadata_operations() {
            let fs = MemEnv::new();
            let path = Path::new("/a/b/hello.file");
            let newpath = Path::new("/a/b/hello2.file");
            let nonexist = Path::new("/blah");

            // Make file/remove file.
            {
                let mut w = fs.open_write(&path, false, false).unwrap();
                write!(w, "Hello").unwrap();
            }
            assert!(fs.exists(&path).unwrap());
            assert_eq!(fs.size_of(&path).unwrap(), 5);
            fs.delete(&path).unwrap();
            assert!(!fs.exists(&path).unwrap());
            assert!(fs.delete(&nonexist).is_err());

            // rename_ file.
            {
                let mut w = fs.open_write(&path, false, false).unwrap();
                write!(w, "Hello").unwrap();
            }
            assert!(fs.exists(&path).unwrap());
            assert!(!fs.exists(&newpath).unwrap());
            assert_eq!(fs.size_of(&path).unwrap(), 5);
            assert!(fs.size_of(&newpath).is_err());

            fs.rename(&path, &newpath).unwrap();

            assert!(!fs.exists(&path).unwrap());
            assert!(fs.exists(&newpath).unwrap());
            assert_eq!(fs.size_of(&newpath).unwrap(), 5);
            assert!(fs.size_of(&path).is_err());

            assert!(fs.rename(&nonexist, &path).is_err());
        }

        fn s2p(x: &str) -> PathBuf {
            Path::new(x).to_owned()
        }

        #[cfg(unix)]
        #[test]
        fn test_mem_fs_children() {
            let fs = MemEnv::new();
            let (path1, path2, path3) = (
                Path::new("/a/1.txt"),
                Path::new("/a/2.txt"),
                Path::new("/b/1.txt"),
            );

            for p in &[&path1, &path2, &path3] {
                fs.open_write(*p, false, false).unwrap();
            }
            let children = fs.children(&Path::new("/a")).unwrap();
            assert!(
                (children == vec![s2p("1.txt"), s2p("2.txt")])
                    || (children == vec![s2p("2.txt"), s2p("1.txt")])
            );
            let children = fs.children(&Path::new("/a/")).unwrap();
            assert!(
                (children == vec![s2p("1.txt"), s2p("2.txt")])
                    || (children == vec![s2p("2.txt"), s2p("1.txt")])
            );
        }

        #[cfg(windows)]
        #[test]
        fn test_mem_fs_children() {
            let fs = MemEnv::new();
            let (path1, path2, path3) = (
                Path::new("\\a\\1.txt"),
                Path::new("\\a\\2.txt"),
                Path::new("\\b\\1.txt"),
            );

            for p in &[&path1, &path2, &path3] {
                fs.open_write(*p, false, false).unwrap();
            }
            let children = fs.children(&Path::new("\\a")).unwrap();
            assert!(
                (children == vec![s2p("1.txt"), s2p("2.txt")])
                    || (children == vec![s2p("2.txt"), s2p("1.txt")])
            );
            let children = fs.children(&Path::new("\\a\\")).unwrap();
            assert!(
                (children == vec![s2p("1.txt"), s2p("2.txt")])
                    || (children == vec![s2p("2.txt"), s2p("1.txt")])
            );
        }

        #[test]
        fn test_mem_fs_lock() {
            let fs = MemEnv::new();
            let p = Path::new("/a/lock");

            {
                let mut f = fs.open_write(p, true, true).unwrap();
                f.write("abcdef".as_bytes()).expect("write failed");
            }

            // Locking on new file.
            let lock = fs.lock(p).unwrap();
            assert!(fs.lock(p).is_err());

            // Unlock of locked file is ok.
            assert!(fs.unlock(lock).is_ok());

            // Lock of unlocked file is ok.
            let lock = fs.lock(p).unwrap();
            assert!(fs.lock(p).is_err());
            assert!(fs.unlock(lock).is_ok());

            // Rogue operation.
            assert!(fs
                .unlock(FileLock {
                    id: "/a/lock".to_string(),
                })
                .is_err());

            // Non-existent files.
            let p2 = Path::new("/a/lock2");
            assert!(fs.lock(p2).is_ok());
            assert!(fs
                .unlock(FileLock {
                    id: "/a/lock2".to_string(),
                })
                .is_ok());
        }

        #[cfg(unix)]
        #[test]
        fn test_memenv_all() {
            let me = MemEnv::new();
            let (p1, p2, p3) = (Path::new("/a/b"), Path::new("/a/c"), Path::new("/a/d"));
            let nonexist = Path::new("/x/y");
            me.open_writable_file(p2).unwrap();
            me.open_appendable_file(p3).unwrap();
            me.open_sequential_file(p2).unwrap();
            me.open_random_access_file(p3).unwrap();

            assert!(me.exists(p2).unwrap());
            assert_eq!(me.children(Path::new("/a/")).unwrap().len(), 2);
            assert_eq!(me.size_of(p2).unwrap(), 0);

            me.delete(p2).unwrap();
            assert!(me.mkdir(p3).is_err());
            me.mkdir(p1).unwrap();
            me.rmdir(p3).unwrap();
            assert!(me.rmdir(nonexist).is_err());

            me.open_writable_file(p1).unwrap();
            me.rename(p1, p3).unwrap();
            assert!(!me.exists(p1).unwrap());
            assert!(me.rename(nonexist, p1).is_err());

            me.unlock(me.lock(p3).unwrap()).unwrap();
            assert!(me.lock(nonexist).is_ok());

            // me.new_logger(p1).unwrap();
            assert!(me.micros() > 0);
            me.sleep_for(10);
        }

        #[cfg(windows)]
        #[test]
        fn test_memenv_all() {
            let me = MemEnv::new();
            let (p1, p2, p3) = (
                Path::new("\\a\\b"),
                Path::new("\\a\\c"),
                Path::new("\\a\\d"),
            );
            let nonexist = Path::new("\\x\\y");
            me.open_writable_file(p2).unwrap();
            me.open_appendable_file(p3).unwrap();
            me.open_sequential_file(p2).unwrap();
            me.open_random_access_file(p3).unwrap();

            assert!(me.exists(p2).unwrap());
            assert_eq!(me.children(Path::new("\\a\\")).unwrap().len(), 2);
            assert_eq!(me.size_of(p2).unwrap(), 0);

            me.delete(p2).unwrap();
            assert!(me.mkdir(p3).is_err());
            me.mkdir(p1).unwrap();
            me.rmdir(p3).unwrap();
            assert!(me.rmdir(nonexist).is_err());

            me.open_writable_file(p1).unwrap();
            me.rename(p1, p3).unwrap();
            assert!(!me.exists(p1).unwrap());
            assert!(me.rename(nonexist, p1).is_err());

            me.unlock(me.lock(p3).unwrap()).unwrap();
            assert!(me.lock(nonexist).is_ok());

            me.new_logger(p1).unwrap();
            assert!(me.micros() > 0);
            me.sleep_for(10);
        }
    }

    mod tests_gpt_4o {
        use super::*;

        #[test]
        fn test_mem_file_new() {
            let file = MemFile::new();
            assert!(file.0.lock().unwrap().is_empty());
        }

        #[test]
        fn test_mem_file_read() {
            let file = MemFile::new();
            {
                let mut f = file.0.lock().unwrap();
                f.extend_from_slice(b"Hello, world!");
            }
            let mut buf = [0; 5];
            assert_eq!(file.read(0, &mut buf).unwrap(), 5);
            assert_eq!(&buf, b"Hello");
        }

        #[test]
        fn test_mem_file_writer() {
            let file = MemFile::new();
            {
                let mut writer = MemFileWriter::new(file.clone(), false);
                writer.write_all(b"Hello").unwrap();
                writer.write_all(b", world!").unwrap();
            }
            assert_eq!(file.0.lock().unwrap().as_slice(), b"Hello, world!");
        }

        #[test]
        fn test_mem_file_writer_append() {
            let file = MemFile::new();
            {
                let mut writer = MemFileWriter::new(file.clone(), false);
                writer.write_all(b"Hello").unwrap();
            }
            {
                let mut writer = MemFileWriter::new(file.clone(), true);
                writer.write_all(b", world!").unwrap();
            }
            assert_eq!(file.0.lock().unwrap().as_slice(), b"Hello, world!");
        }

        #[test]
        fn test_mem_file_writer_truncate() {
            let file = MemFile::new();
            {
                let mut writer = MemFileWriter::new(file.clone(), false);
                writer.write_all(b"Hello, world!").unwrap();
            }
            {
                let mut writer = MemFileWriter::new(file.clone(), false);
                writer.write_all(b"Hi!").unwrap();
            }
            assert_eq!(file.0.lock().unwrap().as_slice(), b"Hi!lo, world!");
        }

        #[test]
        fn test_mem_env_create_open() {
            let env = MemEnv::new();
            let path = Path::new("testfile");
            let file = env.open(path, true).unwrap();
            assert!(file.0.lock().unwrap().is_empty());
        }

        #[test]
        fn test_mem_env_open_existing() {
            let env = MemEnv::new();
            let path = Path::new("testfile");
            let file = env.open(path, true).unwrap();
            {
                let mut f = file.0.lock().unwrap();
                f.extend_from_slice(b"Hello");
            }
            let file2 = env.open(path, false).unwrap();
            let mut buf = [0; 5];
            assert_eq!(file2.read(0, &mut buf).unwrap(), 5);
            assert_eq!(&buf, b"Hello");
        }

        #[test]
        fn test_mem_env_open_not_existing() {
            let env = MemEnv::new();
            let path = Path::new("testfile");
            let result = env.open(path, false);
            assert!(result.is_err());
        }

        #[test]
        fn test_mem_env_exists() {
            let env = MemEnv::new();
            let path = Path::new("testfile");
            assert!(!env.exists(path).unwrap());
            env.open(path, true).unwrap();
            assert!(env.exists(path).unwrap());
        }

        #[test]
        fn test_mem_env_size_of() {
            let env = MemEnv::new();
            let path = Path::new("testfile");
            env.open(path, true).unwrap();
            assert_eq!(env.size_of(path).unwrap(), 0);
            {
                let mut writer = env.open_write(path, false, false).unwrap();
                writer.write_all(b"Hello").unwrap();
            }
            assert_eq!(env.size_of(path).unwrap(), 5);
        }

        #[test]
        fn test_mem_env_delete() {
            let env = MemEnv::new();
            let path = Path::new("testfile");
            env.open(path, true).unwrap();
            assert!(env.exists(path).unwrap());
            env.delete(path).unwrap();
            assert!(!env.exists(path).unwrap());
        }

        #[test]
        fn test_mem_env_children() {
            let env = MemEnv::new();
            let path1 = Path::new("dir1/file1");
            let path2 = Path::new("dir1/file2");
            env.open(path1, true).unwrap();
            env.open(path2, true).unwrap();
            let children = env.children(Path::new("dir1")).unwrap();
            assert_eq!(children.len(), 2);
            assert!(children.contains(&PathBuf::from("file1")));
            assert!(children.contains(&PathBuf::from("file2")));
        }

        #[test]
        fn test_mem_env_rename() {
            let env = MemEnv::new();
            let old_path = Path::new("oldfile");
            let new_path = Path::new("newfile");
            env.open(old_path, true).unwrap();
            env.rename(old_path, new_path).unwrap();
            assert!(!env.exists(old_path).unwrap());
            assert!(env.exists(new_path).unwrap());
        }

        #[test]
        fn test_mem_env_lock_unlock() {
            let env = MemEnv::new();
            let path = Path::new("testfile");
            env.open(path, true).unwrap();
            let lock = env.lock(path).unwrap();
            let result = env.lock(path);
            assert!(result.is_err());
            env.unlock(lock).unwrap();
            let lock = env.lock(path).unwrap();
            env.unlock(lock).unwrap();
        }
    }
}
