use super::memtable::Memtable;
use crate::coredef::key::ValueType;
use crate::coredef::types::SeqNum;
use integer_encoding::{FixedInt, VarInt, VarIntWriter};
use std::io::Write;

const HEADER_SIZE: usize = 12;

/// WriteBatch is a collection of Memtable write operations.
/// Consists of a header (12 bytes) and a list of entries.
///
/// Header format:
/// [seq_num (8 bytes), count (4 bytes)]
///
/// Entry format (value length and value are optional):
/// [tag (1 byte), key length (varint), key, value length (varint), value]
pub struct WriteBatch {
    entries: Vec<u8>,
}

impl Default for WriteBatch {
    fn default() -> Self {
        Self::new()
    }
}

impl WriteBatch {
    pub fn new() -> Self {
        let mut v = Vec::with_capacity(128);
        v.resize(HEADER_SIZE, 0);
        Self { entries: v }
    }

    pub fn set_entries(&mut self, entries: &[u8]) {
        self.entries = entries.to_vec();
    }

    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Returns the number of entries in the batch.
    pub fn count(&self) -> u32 {
        u32::decode_fixed(&self.entries[8..12]).unwrap()
    }

    fn set_count(&mut self, count: u32) {
        count.encode_fixed(&mut self.entries[8..12]).unwrap();
    }

    pub fn seq_num(&self) -> SeqNum {
        SeqNum::decode_fixed(&self.entries[0..8]).unwrap()
    }

    fn set_seq_num(&mut self, seq_num: SeqNum) {
        seq_num.encode_fixed(&mut self.entries[0..8]).unwrap();
    }

    pub fn add(&mut self, key: &[u8], value: &[u8]) {
        self.entries
            .write_all(&[ValueType::TypeValue as u8])
            .unwrap();
        self.entries.write_varint(key.len()).unwrap();
        self.entries.write_all(key).unwrap();
        self.entries.write_varint(value.len()).unwrap();
        self.entries.write_all(value).unwrap();
        self.set_count(self.count() + 1);
    }

    /// Adds a deletion entry for the given key.
    pub fn delete(&mut self, key: &[u8]) {
        self.entries
            .write_all(&[ValueType::TypeDeletion as u8])
            .unwrap();
        self.entries.write_varint(key.len()).unwrap();
        self.entries.write_all(key).unwrap();
        self.set_count(self.count() + 1);
    }

    pub fn iter(&self) -> WriteBatchIterator {
        WriteBatchIterator {
            batch: self,
            current: HEADER_SIZE,
        }
    }

    pub fn apply(&self, mut seq_num: SeqNum, memtable: &mut Memtable) {
        for (key, value) in self.iter() {
            if let Some(value) = value {
                memtable.add(key, value, ValueType::TypeValue, seq_num);
            } else {
                memtable.add(key, &[], ValueType::TypeDeletion, seq_num);
            }
            seq_num += 1;
        }
    }

    pub fn encode(mut self, seq_num: SeqNum) -> Vec<u8> {
        self.set_seq_num(seq_num);
        self.entries
    }
}

/// Iterator over the entries in a WriteBatch.
pub struct WriteBatchIterator<'a> {
    batch: &'a WriteBatch,
    current: usize,
}

impl<'a> Iterator for WriteBatchIterator<'a> {
    type Item = (&'a [u8], Option<&'a [u8]>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.current >= self.batch.entries.len() {
            return None;
        }

        let tag = self.batch.entries[self.current];
        self.current += 1;

        let (key_length, x) = usize::decode_var(&self.batch.entries[self.current..])?;
        self.current += x;
        let key = &self.batch.entries[self.current..self.current + key_length];
        self.current += key_length;

        if tag == ValueType::TypeValue as u8 {
            let (value_length, x) = usize::decode_var(&self.batch.entries[self.current..])?;
            self.current += x;
            let value = &self.batch.entries[self.current..self.current + value_length];
            self.current += value_length;
            Some((key, Some(value)))
        } else {
            Some((key, None))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests_leveldb_rs {
        use super::*;

        #[test]
        fn test_write_batch() {
            let mut b = WriteBatch::new();
            let entries = vec![
                ("abc".as_bytes(), "def".as_bytes()),
                ("123".as_bytes(), "456".as_bytes()),
                ("xxx".as_bytes(), "yyy".as_bytes()),
                ("zzz".as_bytes(), "".as_bytes()),
                ("010".as_bytes(), "".as_bytes()),
            ];

            for &(k, v) in entries.iter() {
                if !v.is_empty() {
                    b.add(k, v);
                } else {
                    b.delete(k)
                }
            }

            // eprintln!("{:?}", b.entries);
            assert_eq!(b.entries.len(), 49);
            assert_eq!(b.iter().count(), 5);

            let mut i = 0;

            for (k, v) in b.iter() {
                assert_eq!(k, entries[i].0);

                match v {
                    None => assert!(entries[i].1.is_empty()),
                    Some(v_) => assert_eq!(v_, entries[i].1),
                }

                i += 1;
            }

            assert_eq!(i, 5);
            assert_eq!(b.encode(1).len(), 49);
        }
    }
}
