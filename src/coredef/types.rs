use super::error::{err, Result, StatusCode};

/// A larger sequence number is more recent
pub type SeqNum = u64;
pub const MAX_SEQNUM: SeqNum = (1 << 56) - 1;
pub const NUM_LEVELS: usize = 7;

#[derive(Clone, Copy, PartialEq)]
pub enum Direction {
    Forward,
    Backward,
}

/// Universal iterator trait
/// An iterator is invalid before first `advance` call (positioned before the first element)
pub trait DbIterator {
    /// Move one step to the next element
    /// Returns false if no more element
    fn advance(&mut self) -> bool;

    fn current(&self, key: &mut Vec<u8>, value: &mut Vec<u8>) -> bool;

    fn current_kv(&self) -> Option<(Vec<u8>, Vec<u8>)> {
        let mut key = Vec::new();
        let mut value = Vec::new();
        if self.current(&mut key, &mut value) {
            Some((key, value))
        } else {
            None
        }
    }

    // Move to the first element >= key
    fn seek(&mut self, key: &[u8]);

    fn seek_to_first(&mut self) {
        self.reset();
        self.advance();
    }

    /// Move to the position before the first element
    /// Will be `!valid()` after this operation
    fn reset(&mut self);

    fn valid(&self) -> bool;

    /// Inefficient for single direction iterator
    fn prev(&mut self) -> bool;

    fn next(&mut self) -> Option<(Vec<u8>, Vec<u8>)> {
        if !self.advance() {
            return None;
        }
        let mut key = Vec::new();
        let mut value = Vec::new();
        if self.current(&mut key, &mut value) {
            Some((key, value))
        } else {
            None
        }
    }
}

pub struct DbIteratorWrapper<'a, It: 'a> {
    inner: &'a mut It,
}

impl<'a, It: DbIterator> DbIteratorWrapper<'a, It> {
    pub fn new(inner: &'a mut It) -> Self {
        Self { inner }
    }
}

impl<'a, It: DbIterator> Iterator for DbIteratorWrapper<'a, It> {
    type Item = (Vec<u8>, Vec<u8>);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

// impl DbIterator for Box<dyn DbIterator> {
//     fn advance(&mut self) -> bool {
//         self.as_mut().advance()
//     }

//     fn current(&self, key: &mut Vec<u8>, value: &mut Vec<u8>) -> bool {
//         self.as_ref().current(key, value)
//     }

//     fn seek(&mut self, key: &[u8]) {
//         self.as_mut().seek(key)
//     }

//     fn reset(&mut self) {
//         self.as_mut().reset()
//     }

//     fn valid(&self) -> bool {
//         self.as_ref().valid()
//     }

//     fn prev(&mut self) -> bool {
//         self.as_mut().prev()
//     }
// }

pub type FileID = u64;

#[derive(Clone, PartialEq)]
pub struct FileMetaData {
    pub allowed_seeks: usize,
    pub id: FileID,
    pub size: usize,
    // Internal key format
    pub smallest: Vec<u8>,
    pub largest: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum FileType {
    Log,
    DBLock,
    Table,
    Descriptor,
    Current,
    Temp,
    InfoLog,
}

pub fn parse_file_name(name: &str) -> Result<(FileID, FileType)> {
    if name == "CURRENT" {
        Ok((0, FileType::Current))
    } else if name == "LOCK" {
        Ok((0, FileType::DBLock))
    } else if name == "LOG" || name == "LOG.old" {
        Ok((0, FileType::InfoLog))
    } else if name.starts_with("MANIFEST-") {
        if let Some(i) = name.find('-') {
            if let Ok(id) = FileID::from_str_radix(&name[i + 1..], 10) {
                Ok((id, FileType::Descriptor))
            } else {
                err(StatusCode::InvalidArgument, "manifest file has invalid id")
            }
        } else {
            err(StatusCode::InvalidArgument, "manifest file has no dash")
        }
    } else if let Some(i) = name.find('.') {
        if let Ok(id) = FileID::from_str_radix(&name[..i], 10) {
            let file_type = match &name[i + 1..] {
                "log" => FileType::Log,
                "sst" | "ldb" => FileType::Table,
                "dbtmp" => FileType::Temp,
                _ => return err(StatusCode::InvalidArgument, "Invalid file type"),
            };
            Ok((id, file_type))
        } else {
            err(StatusCode::InvalidArgument, "Invalid file id or temp file")
        }
    } else {
        err(StatusCode::InvalidArgument, "Invalid file name")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_types_parse_file_name() {
        for c in &[
            ("CURRENT", (0, FileType::Current)),
            ("LOCK", (0, FileType::DBLock)),
            ("LOG", (0, FileType::InfoLog)),
            ("LOG.old", (0, FileType::InfoLog)),
            ("MANIFEST-01234", (1234, FileType::Descriptor)),
            ("001122.sst", (1122, FileType::Table)),
            ("001122.ldb", (1122, FileType::Table)),
            ("001122.dbtmp", (1122, FileType::Temp)),
        ] {
            assert_eq!(parse_file_name(c.0).unwrap(), c.1);
        }
        assert!(parse_file_name("xyz.LOCK").is_err());
        assert!(parse_file_name("01a.sst").is_err());
        assert!(parse_file_name("0011.abc").is_err());
        assert!(parse_file_name("MANIFEST-trolol").is_err());
    }
}
