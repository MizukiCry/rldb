use std::{
    cell::RefCell,
    collections::HashSet,
    io::{Read, Write},
    rc::Rc,
};

use integer_encoding::{VarIntReader, VarIntWriter};

use crate::coredef::{
    cmp::{Cmp, InternalKeyCmp},
    error::{err, Result, StatusCode},
    options::Options,
    types::{FileID, FileMetaData, SeqNum},
    NUM_LEVELS,
};
use crate::storage::version::{FileMetaHandle, Version};

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

    pub fn edit(&mut self) -> &mut VersionEdit {
        &mut self.edit
    }

    pub fn into_edit(self) -> VersionEdit {
        self.edit
    }
}

struct Builder {}

impl Builder {}

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
                let mut buf = Vec::new();
                buf.resize(len, 0);
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
