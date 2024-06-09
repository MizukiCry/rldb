use std::{cmp::Ordering, option, rc::Rc};

use crate::coredef::options::Options;
use crate::coredef::types::DbIterator;

use integer_encoding::{FixedInt, FixedIntWriter, VarInt, VarIntWriter};

/// An immutable ordered collection of key-value pairs
///
/// A data block contains a sequence of key-value pairs.
/// In order to reduce the space overhead, some keys will share the same prefix.
/// To accelerate the search, we will store some complete key in the block - restart points.
///
/// Block format:
/// [Entry1, Entry2, Entry3, ..., EntryN, Restarts ([u32]), NumRestarts (u32)]
/// Restarts: the offset of complete keys in the block
///
/// Entry format:
/// [SharedKeyLength (varint), NonSharedKeyLength (varint), ValueLength (varint), NonSharedKey, Value]
/// SharedKeyLength: the length of the shared prefix of the key with the previous key
/// NonSharedKeyLength: the length of the non-shared suffix of the key
///
#[derive(Clone)]
pub struct Block {
    contents: Rc<Vec<u8>>,
    options: Options,
}

impl Block {
    pub fn new(contents: Vec<u8>, options: Options) -> Self {
        assert!(contents.len() > 4, "Block contents too short");
        Block {
            contents: Rc::new(contents),
            options,
        }
    }

    pub fn contents(&self) -> Rc<Vec<u8>> {
        self.contents.clone()
    }

    pub fn iter(&self) -> BlockIter {
        let num_restarts =
            u32::decode_fixed(&self.contents[self.contents.len() - 4..]).unwrap() as usize;
        let restarts_offset = self.contents.len() - 4 - 4 * num_restarts;
        BlockIter {
            contents: self.contents.clone(),
            options: self.options.clone(),
            restarts_offset,
            num_restarts,
            current_entry_offset: 0,
            next_entry_offset: 0,
            current_restart_idx: 0,
            key: Vec::new(),
            value_offset: 0,
        }
    }
}

pub struct BlockIter {
    contents: Rc<Vec<u8>>,
    options: Options,

    restarts_offset: usize,
    num_restarts: usize,

    current_entry_offset: usize,
    next_entry_offset: usize,
    current_restart_idx: usize,

    // The key and value offset of the current entry
    key: Vec<u8>,
    value_offset: usize,
}

impl std::fmt::Debug for BlockIter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BlockIter")
            .field("contents", &self.contents)
            // .field("options", &self.options)
            .field("restarts_offset", &self.restarts_offset)
            .field("num_restarts", &self.num_restarts)
            .field("current_entry_offset", &self.current_entry_offset)
            .field("next_entry_offset", &self.next_entry_offset)
            .field("current_restart_idx", &self.current_restart_idx)
            .field("key", &self.key)
            .field("value_offset", &self.value_offset)
            .finish()
    }
}

impl BlockIter {
    fn num_restarts(&self) -> usize {
        self.num_restarts
    }

    fn restart_point(&self, idx: usize) -> usize {
        assert!(idx < self.num_restarts, "idx out of range");
        let restart = self.restarts_offset + 4 * idx;
        u32::decode_fixed(&self.contents[restart..restart + 4]).unwrap() as usize
    }

    /// Get (SharedKeyLength, NonSharedKeyLength, ValueLength, HeadLength)
    /// HeadLength: len(SharedKeyLength) + len(NonSharedKeyLength) + len(ValueLength)
    fn parse_entry_and_advance(&mut self) -> (usize, usize, usize, usize) {
        let mut p = 0;
        let (shared_key_len, i) = usize::decode_var(&self.contents[self.next_entry_offset..])
            .expect("shared_key_len decode failed");
        p += i;
        let (non_shared_key_len, i) =
            usize::decode_var(&self.contents[self.next_entry_offset + p..])
                .expect("non_shared_key_len decode failed");
        p += i;
        let (value_len, i) = usize::decode_var(&self.contents[self.next_entry_offset + p..])
            .expect("value_len decode failed");
        p += i;

        self.value_offset = self.next_entry_offset + p + non_shared_key_len;
        self.next_entry_offset = self.value_offset + value_len;

        (shared_key_len, non_shared_key_len, value_len, p)
    }

    fn seek_to_restart_point(&mut self, idx: usize) {
        let restart = self.restart_point(idx);

        self.current_entry_offset = restart;
        self.next_entry_offset = restart;
        self.current_restart_idx = idx;

        let (shared_key_len, non_shared_key_len, _, head_len) = self.parse_entry_and_advance();
        assert_eq!(
            shared_key_len, 0,
            "restart key should not have shared prefix"
        );

        self.key.clear();
        self.key.extend_from_slice(
            &self.contents[restart + head_len..restart + head_len + non_shared_key_len],
        );

        assert_eq!(self.key.len(), non_shared_key_len, "key length mismatch");
        assert!(self.valid(), "invalid iterator");
    }

    pub fn seek_to_last(&mut self) {
        if self.num_restarts == 0 {
            self.reset();
        } else {
            self.seek_to_restart_point(self.num_restarts - 1);
        }

        while self.next_entry_offset < self.restarts_offset {
            self.advance();
        }

        assert!(self.valid(), "invalid iterator");
    }
}

impl DbIterator for BlockIter {
    fn advance(&mut self) -> bool {
        if self.next_entry_offset >= self.restarts_offset {
            self.reset();
            return false;
        }

        self.current_entry_offset = self.next_entry_offset;
        let (shared_key_len, non_shared_key_len, _, head_len) = self.parse_entry_and_advance();

        self.key.truncate(shared_key_len);
        self.key.extend_from_slice(
            &self.contents[self.current_entry_offset + head_len
                ..self.current_entry_offset + head_len + non_shared_key_len],
        );

        if self.current_restart_idx + 1 < self.num_restarts
            && self.restart_point(self.current_restart_idx + 1) < self.current_entry_offset
        {
            self.current_restart_idx += 1;
        }

        true
    }

    fn current(&self, key: &mut Vec<u8>, value: &mut Vec<u8>) -> bool {
        if !self.valid() {
            return false;
        }
        key.clone_from(&self.key);
        value.clear();
        value.extend_from_slice(&self.contents[self.value_offset..self.next_entry_offset]);
        true
    }

    fn prev(&mut self) -> bool {
        let current_offset = self.current_entry_offset;

        if current_offset == 0 {
            self.reset();
            return false;
        }

        if self.restart_point(self.current_restart_idx) >= current_offset {
            assert!(
                self.current_restart_idx > 0,
                "current_restart_idx should be > 0"
            );
            self.current_restart_idx -= 1;
        }

        self.next_entry_offset = self.restart_point(self.current_restart_idx);
        assert!(self.next_entry_offset < current_offset);

        while self.next_entry_offset < current_offset {
            if !self.advance() {
                return false;
            }
        }

        true
    }

    fn reset(&mut self) {
        // self.current_entry_offset = 0;
        self.next_entry_offset = 0;
        self.current_restart_idx = 0;
        self.key.clear();
        self.value_offset = 0;
    }

    fn seek(&mut self, key: &[u8]) {
        self.reset();

        let mut left = 0;
        let mut right = self.num_restarts.saturating_sub(1);

        while left < right {
            let mid = (left + right + 1) / 2;
            self.seek_to_restart_point(mid);

            if self.options.cmp.cmp(&self.key, key) == Ordering::Less {
                left = mid;
            } else {
                right = mid - 1;
            }
        }

        self.current_restart_idx = left;
        self.next_entry_offset = self.restart_point(left);

        while let Some((k, _)) = self.next() {
            if self.options.cmp.cmp(&k, key) != Ordering::Less {
                break;
            }
        }
    }

    fn valid(&self) -> bool {
        !self.key.is_empty() && self.value_offset > 0 && self.value_offset <= self.restarts_offset
    }
}

pub struct BlockBuilder {
    buffer: Vec<u8>,
    options: Options,
    restarts: Vec<u32>,

    size: usize,
    restart_counter: usize,
    last_key: Vec<u8>,
}

impl BlockBuilder {
    pub fn new(options: Options) -> Self {
        Self {
            buffer: Vec::with_capacity(options.block_size),
            options,
            restarts: {
                let mut v = Vec::with_capacity(1024);
                v.push(0);
                v
            },
            size: 0,
            restart_counter: 0,
            last_key: Vec::new(),
        }
    }

    pub fn add(&mut self, key: &[u8], value: &[u8]) {
        assert!(self.size == 0 || self.options.cmp.cmp(&self.last_key, key) == Ordering::Less);

        let mut shared = 0;

        if self.restart_counter < self.options.block_restart_interval {
            shared = self
                .last_key
                .iter()
                .zip(key)
                .take_while(|(a, b)| a == b)
                .count();
        } else {
            self.restarts.push(self.buffer.len() as u32);
            self.restart_counter = 0;
        }

        self.size += 1;
        self.restart_counter += 1;

        self.buffer
            .write_varint(shared)
            .expect("write shared failed");
        self.buffer
            .write_varint(key.len() - shared)
            .expect("write non-shared failed");
        self.buffer
            .write_varint(value.len())
            .expect("write value length failed");
        self.buffer.extend_from_slice(&key[shared..]);
        self.buffer.extend_from_slice(value);

        self.last_key.resize(shared, 0);
        self.last_key.extend_from_slice(&key[shared..]);
    }

    /// Number of key-value pairs in the block
    pub fn entries(&self) -> usize {
        self.size
    }

    pub fn last_key(&self) -> &[u8] {
        &self.last_key
    }

    pub fn estimate_size(&self) -> usize {
        self.buffer.len() + 4 * self.restarts.len() + 4
    }

    pub fn reset(&mut self) {
        self.buffer.clear();
        self.restarts.clear();
        self.size = 0;
        self.restart_counter = 0;
        self.last_key.clear();
    }

    pub fn build(mut self) -> Vec<u8> {
        self.buffer.reserve(self.restarts.len() * 4 + 4);

        for &restart in self.restarts.iter() {
            self.buffer
                .write_fixedint(restart)
                .expect("write restart failed");
        }
        self.buffer
            .write_fixedint(self.restarts.len() as u32)
            .expect("write num restarts failed");

        self.buffer
    }
}

#[derive(Clone, Copy)]
pub struct BlockHandle {
    offset: usize,
    size: usize,
}

impl BlockHandle {
    pub fn new(offset: usize, size: usize) -> Self {
        Self { offset, size }
    }

    pub fn offset(&self) -> usize {
        self.offset
    }

    pub fn size(&self) -> usize {
        self.size
    }

    /// Encodes to dst and returns bytes written
    pub fn encode(&self, dst: &mut [u8]) -> usize {
        assert!(
            self.offset.required_space() + self.size.required_space() <= dst.len(),
            "dst too short"
        );
        let offset_len = self.offset.encode_var(dst);
        let size_len = self.size.encode_var(&mut dst[offset_len..]);
        offset_len + size_len
    }

    /// Decodes from src and returns (BlockHandle, bytes read)
    pub fn decode(src: &[u8]) -> Option<(Self, usize)> {
        let (offset, offset_len) = usize::decode_var(src)?;
        let (size, size_len) = usize::decode_var(&src[offset_len..])?;
        Some((Self { offset, size }, offset_len + size_len))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests_block_iter {
        use crate::{coredef::types::DbIteratorWrapper, utils::test_iterator_properties};

        use super::*;

        fn get_data() -> Vec<(&'static [u8], &'static [u8])> {
            vec![
                ("key1".as_bytes(), "value1".as_bytes()),
                (
                    "loooooooooooooooooooooooooooooooooongerkey1".as_bytes(),
                    "shrtvl1".as_bytes(),
                ),
                ("medium length key 1".as_bytes(), "some value 2".as_bytes()),
                ("prefix_key1".as_bytes(), "value".as_bytes()),
                ("prefix_key2".as_bytes(), "value".as_bytes()),
                ("prefix_key3".as_bytes(), "value".as_bytes()),
            ]
        }

        #[test]
        fn test_block_iterator_properties() {
            let o = Options::default();
            let mut builder = BlockBuilder::new(o.clone());
            let mut data = get_data();
            data.truncate(4);
            for &(k, v) in data.iter() {
                builder.add(k, v);
            }
            let block_contents = builder.build();

            let block = Block::new(block_contents, o.clone()).iter();
            test_iterator_properties(block);
        }

        #[test]
        fn test_block_empty() {
            let mut o = Options::default();
            o.block_restart_interval = 16;
            let builder = BlockBuilder::new(o);

            let blockc = builder.build();
            assert_eq!(blockc.len(), 8);
            assert_eq!(blockc, vec![0, 0, 0, 0, 1, 0, 0, 0]);

            let block = Block::new(blockc, Options::default());

            let mut iter = block.iter();
            assert!(!iter.valid());
            assert!(!iter.advance());
            assert!(!iter.valid());
        }

        #[test]
        fn test_block_build_iterate() {
            let data = get_data();
            let mut builder = BlockBuilder::new(Options::default());

            for &(k, v) in data.iter() {
                builder.add(k, v);
            }

            let block_contents = builder.build();
            let mut block = Block::new(block_contents, Options::default()).iter();
            let mut i = 0;

            assert!(!block.valid());

            for (k, v) in DbIteratorWrapper::new(&mut block) {
                assert_eq!(&k[..], data[i].0);
                assert_eq!(v, data[i].1);
                i += 1;
            }
            assert_eq!(i, data.len());
        }

        #[test]
        fn test_block_iterate_reverse() {
            let mut o = Options::default();
            o.block_restart_interval = 3;
            let data = get_data();
            let mut builder = BlockBuilder::new(o.clone());

            for &(k, v) in data.iter() {
                builder.add(k, v);
            }

            let block_contents = builder.build();
            let mut block = Block::new(block_contents, o.clone()).iter();

            assert!(!block.valid());
            assert_eq!(
                block.next(),
                Some(("key1".as_bytes().to_vec(), "value1".as_bytes().to_vec()))
            );
            assert!(block.valid());
            block.next();
            assert!(block.valid());
            block.prev();
            assert!(block.valid());
            assert_eq!(
                block.current_kv(),
                Some(("key1".as_bytes().to_vec(), "value1".as_bytes().to_vec()))
            );
            block.prev();
            assert!(!block.valid());

            // Verify that prev() from the last entry goes to the prev-to-last entry
            // (essentially, that next() returning None doesn't advance anything)
            while let Some(_) = block.next() {}

            block.prev();
            assert!(block.valid());
            assert_eq!(
                block.current_kv(),
                Some((
                    "prefix_key2".as_bytes().to_vec(),
                    "value".as_bytes().to_vec()
                ))
            );
        }

        #[test]
        fn test_block_seek() {
            let mut o = Options::default();
            o.block_restart_interval = 3;

            let data = get_data();
            let mut builder = BlockBuilder::new(o.clone());

            for &(k, v) in data.iter() {
                builder.add(k, v);
            }

            let block_contents = builder.build();

            let mut block = Block::new(block_contents, o.clone()).iter();

            block.seek(&"prefix_key2".as_bytes());
            assert!(block.valid());
            assert_eq!(
                block.current_kv(),
                Some((
                    "prefix_key2".as_bytes().to_vec(),
                    "value".as_bytes().to_vec()
                ))
            );

            block.seek(&"prefix_key0".as_bytes());
            assert!(block.valid());
            assert_eq!(
                block.current_kv(),
                Some((
                    "prefix_key1".as_bytes().to_vec(),
                    "value".as_bytes().to_vec()
                ))
            );

            block.seek(&"key1".as_bytes());
            assert!(block.valid());
            assert_eq!(
                block.current_kv(),
                Some(("key1".as_bytes().to_vec(), "value1".as_bytes().to_vec()))
            );

            block.seek(&"prefix_key3".as_bytes());
            assert!(block.valid());
            assert_eq!(
                block.current_kv(),
                Some((
                    "prefix_key3".as_bytes().to_vec(),
                    "value".as_bytes().to_vec()
                ))
            );

            block.seek(&"prefix_key8".as_bytes());
            assert!(!block.valid());
            assert_eq!(block.current_kv(), None);
        }

        #[test]
        fn test_block_seek_to_last() {
            let mut o = Options::default();

            // Test with different number of restarts
            for block_restart_interval in vec![2, 6, 10] {
                o.block_restart_interval = block_restart_interval;

                let data = get_data();
                let mut builder = BlockBuilder::new(o.clone());

                for &(k, v) in data.iter() {
                    builder.add(k, v);
                }

                let block_contents = builder.build();

                let mut block = Block::new(block_contents, o.clone()).iter();

                block.seek_to_last();
                assert!(block.valid());
                assert_eq!(
                    block.current_kv(),
                    Some((
                        "prefix_key3".as_bytes().to_vec(),
                        "value".as_bytes().to_vec()
                    ))
                );
            }
        }

        mod tests_gpt_4o {
            use super::*;
            use crate::coredef::options::Options;
            use crate::coredef::types::DbIterator;

            fn get_sample_options() -> Options {
                Options::default()
            }

            fn build_sample_block() -> Block {
                let options = get_sample_options();
                let mut builder = BlockBuilder::new(options.clone());

                let data = vec![
                    (b"key1", b"value1"),
                    (b"key2", b"value2"),
                    (b"key3", b"value3"),
                ];

                for (key, value) in data {
                    builder.add(key, value);
                }

                let contents = builder.build();
                Block::new(contents, options)
            }

            #[test]
            fn test_block_creation() {
                let block = build_sample_block();
                let contents = block.contents();
                assert!(contents.len() > 0);
            }

            #[test]
            #[should_panic(expected = "Block contents too short")]
            fn test_block_creation_too_short() {
                let contents = vec![1, 2, 3];
                let options = get_sample_options();
                Block::new(contents, options);
            }

            #[test]
            fn test_block_contents() {
                let block = build_sample_block();
                let contents = block.contents();
                assert!(contents.len() > 0);
            }

            #[test]
            fn test_block_iter() {
                let block = build_sample_block();
                let iter = block.iter();
                assert!(iter.num_restarts() > 0); // 根据BlockBuilder生成的重启点数量来确定
            }

            #[test]
            fn test_block_iter_advance() {
                let block = build_sample_block();
                let mut iter = block.iter();
                assert!(iter.advance());
                let mut key = Vec::new();
                let mut value = Vec::new();
                assert!(iter.current(&mut key, &mut value));
                assert_eq!(key, b"key1");
                assert_eq!(value, b"value1");
            }

            #[test]
            fn test_block_iter_seek() {
                let block = build_sample_block();
                let mut iter = block.iter();
                iter.seek(b"key2");
                let mut key = Vec::new();
                let mut value = Vec::new();
                assert!(iter.current(&mut key, &mut value));
                assert_eq!(key, b"key2");
                assert_eq!(value, b"value2");
            }

            #[test]
            fn test_block_iter_seek_to_last() {
                let block = build_sample_block();
                let mut iter = block.iter();
                iter.seek_to_last();
                let mut key = Vec::new();
                let mut value = Vec::new();
                assert!(iter.current(&mut key, &mut value));
                assert_eq!(key, b"key3");
                assert_eq!(value, b"value3");
            }

            #[test]
            fn test_block_iter_reset() {
                let block = build_sample_block();
                let mut iter = block.iter();
                iter.advance();
                assert!(iter.valid());
                iter.reset();
                assert!(!iter.valid());
            }

            #[test]
            fn test_block_iter_seek_non_existent() {
                let block = build_sample_block();
                let mut iter = block.iter();
                iter.seek(b"non_existent_key");
                assert!(!iter.valid());
            }

            #[test]
            fn test_block_iter_prev() {
                let block = build_sample_block();
                let mut iter = block.iter();
                iter.seek_to_last();
                assert!(iter.valid());
                iter.prev();
                assert!(iter.valid());
                let mut key = Vec::new();
                let mut value = Vec::new();
                iter.current(&mut key, &mut value);
                assert_eq!(key, b"key2");
                assert_eq!(value, b"value2");
            }

            #[test]
            fn test_block_iter_restart_point() {
                let block = build_sample_block();
                let iter = block.iter();
                assert_eq!(iter.restart_point(0), 0); // 根据BlockBuilder生成的重启点数量来确定
            }

            #[test]
            fn test_block_iter_parse_entry_and_advance() {
                let block = build_sample_block();
                let mut iter = block.iter();
                let (shared_key_len, non_shared_key_len, value_len, head_len) =
                    iter.parse_entry_and_advance();
                // 具体值需要根据BlockBuilder生成的内容来调整
                assert_eq!(shared_key_len, 0);
                assert_eq!(non_shared_key_len, 4);
                assert_eq!(value_len, 6);
                assert_eq!(head_len, 3);
            }
        }
    }

    mod tests_block_builder {
        use super::*;

        fn get_data() -> Vec<(&'static [u8], &'static [u8])> {
            vec![
                ("key1".as_bytes(), "value1".as_bytes()),
                (
                    "loooooooooooooooooooooooooooooooooongerkey1".as_bytes(),
                    "shrtvl1".as_bytes(),
                ),
                ("medium length key 1".as_bytes(), "some value 2".as_bytes()),
                ("prefix_key1".as_bytes(), "value".as_bytes()),
                ("prefix_key2".as_bytes(), "value".as_bytes()),
                ("prefix_key3".as_bytes(), "value".as_bytes()),
            ]
        }

        #[test]
        fn test_block_builder_sanity() {
            let mut o = Options::default();
            o.block_restart_interval = 3;
            let mut builder = BlockBuilder::new(o);
            let d = get_data();

            for &(k, v) in d.iter() {
                builder.add(k, v);
                assert!(builder.restart_counter <= 3);
                assert_eq!(builder.last_key(), k);
            }

            assert_eq!(149, builder.estimate_size());
            assert_eq!(d.len(), builder.entries());

            let block = builder.build();
            assert_eq!(block.len(), 149);
        }

        #[test]
        fn test_block_builder_reset() {
            let mut o = Options::default();
            o.block_restart_interval = 3;
            let mut builder = BlockBuilder::new(o);
            let d = get_data();

            for &(k, v) in d.iter() {
                builder.add(k, v);
                assert!(builder.restart_counter <= 3);
                assert_eq!(builder.last_key(), k);
            }

            assert_eq!(d.len(), builder.entries());
            builder.reset();
            assert_eq!(0, builder.entries());
            assert_eq!(4, builder.estimate_size());
        }

        #[test]
        #[should_panic]
        fn test_block_builder_panics() {
            let mut d = get_data();
            // Identical key as d[3].
            d[4].0 = b"prefix_key1";

            let mut builder = BlockBuilder::new(Options::default());
            for &(k, v) in d.iter() {
                builder.add(k, v);
                assert_eq!(k, builder.last_key());
            }
        }

        mod tests_gpt_4o {
            use super::*;
            use crate::coredef::{options::Options, types::DbIteratorWrapper};

            fn get_sample_options() -> Options {
                Options::default()
            }

            fn get_sample_data() -> Vec<(&'static [u8], &'static [u8])> {
                vec![
                    (b"key1", b"value1"),
                    (b"key2", b"value2"),
                    (b"key3", b"value3"),
                ]
            }

            #[test]
            fn test_block_builder_creation() {
                let options = get_sample_options();
                let builder = BlockBuilder::new(options.clone());
                assert!(builder.buffer.is_empty());
                // assert_eq!(builder.options, options);
                assert_eq!(builder.restarts.len(), 1);
                assert_eq!(builder.restarts[0], 0);
                assert_eq!(builder.size, 0);
                assert_eq!(builder.restart_counter, 0);
                assert!(builder.last_key.is_empty());
            }

            #[test]
            fn test_block_builder_add() {
                let options = get_sample_options();
                let mut builder = BlockBuilder::new(options.clone());
                let data = get_sample_data();

                for (key, value) in data.iter() {
                    builder.add(key, value);
                }

                assert_eq!(builder.entries(), data.len());
                assert_eq!(builder.last_key(), b"key3");
            }

            #[test]
            fn test_block_builder_entries() {
                let options = get_sample_options();
                let mut builder = BlockBuilder::new(options.clone());
                let data = get_sample_data();

                for (key, value) in data.iter() {
                    builder.add(key, value);
                }

                assert_eq!(builder.entries(), data.len());
            }

            #[test]
            fn test_block_builder_last_key() {
                let options = get_sample_options();
                let mut builder = BlockBuilder::new(options.clone());
                let data = get_sample_data();

                for (key, value) in data.iter() {
                    builder.add(key, value);
                }

                assert_eq!(builder.last_key(), b"key3");
            }

            #[test]
            fn test_block_builder_estimate_size() {
                let options = get_sample_options();
                let mut builder = BlockBuilder::new(options.clone());
                let data = get_sample_data();

                for (key, value) in data.iter() {
                    builder.add(key, value);
                }

                let estimated_size = builder.estimate_size();
                assert!(estimated_size > 0);
            }

            #[test]
            fn test_block_builder_reset() {
                let options = get_sample_options();
                let mut builder = BlockBuilder::new(options.clone());
                let data = get_sample_data();

                for (key, value) in data.iter() {
                    builder.add(key, value);
                }

                builder.reset();

                assert!(builder.buffer.is_empty());
                // assert_eq!(builder.restarts.len(), 1);
                // assert_eq!(builder.restarts[0], 0);
                assert_eq!(builder.size, 0);
                assert_eq!(builder.restart_counter, 0);
                assert!(builder.last_key.is_empty());
            }

            #[test]
            fn test_block_builder_build() {
                let options = get_sample_options();
                let mut builder = BlockBuilder::new(options.clone());
                let data = get_sample_data();

                for (key, value) in data.iter() {
                    builder.add(key, value);
                }

                let block = builder.build();
                assert!(block.len() > 0);

                // 验证生成的块内容
                let mut block_iter = Block::new(block, options).iter();
                let mut i = 0;
                for (k, v) in DbIteratorWrapper::new(&mut block_iter) {
                    assert_eq!(&k[..], data[i].0);
                    assert_eq!(v, data[i].1);
                    i += 1;
                }
                assert_eq!(i, data.len());
            }

            #[test]
            #[should_panic]
            fn test_block_builder_add_out_of_order() {
                let options = get_sample_options();
                let mut builder = BlockBuilder::new(options.clone());

                builder.add(b"key2", b"value2");
                builder.add(b"key1", b"value1"); // 这应该会导致panic
            }

            #[test]
            fn test_block_builder_multiple_blocks() {
                let options = get_sample_options();
                let mut builder = BlockBuilder::new(options.clone());
                let data1 = vec![(b"key1", b"value1")];
                let data2 = vec![(b"key2", b"value2"), (b"key3", b"value3")];

                for (key, value) in data1.iter() {
                    builder.add(*key, *value);
                }

                let block1 = builder.build();
                assert!(block1.len() > 0);

                // builder.reset();
                let mut builder = BlockBuilder::new(options.clone());

                for (key, value) in data2.iter() {
                    builder.add(*key, *value);
                }

                let block2 = builder.build();
                assert!(block2.len() > 0);

                // 验证第一个块
                let mut block_iter1 = Block::new(block1, options.clone()).iter();
                let mut i = 0;
                for (k, v) in DbIteratorWrapper::new(&mut block_iter1) {
                    assert_eq!(&k[..], data1[i].0);
                    assert_eq!(v, data1[i].1);
                    i += 1;
                }
                assert_eq!(i, data1.len());

                // 验证第二个块
                let mut block_iter2 = Block::new(block2, options).iter();
                let mut j = 0;
                for (k, v) in DbIteratorWrapper::new(&mut block_iter2) {
                    assert_eq!(&k[..], data2[j].0);
                    assert_eq!(v, data2[j].1);
                    j += 1;
                }
                assert_eq!(j, data2.len());
            }
        }
    }

    mod tests_block_handle {
        use super::*;

        #[test]
        fn test_blockhandle() {
            let bh = BlockHandle::new(890, 777);
            let mut dst = [0 as u8; 128];
            let enc_sz = bh.encode(&mut dst[..]);

            let (bh2, dec_sz) = BlockHandle::decode(&dst).unwrap();

            assert_eq!(enc_sz, dec_sz);
            assert_eq!(bh.size(), bh2.size());
            assert_eq!(bh.offset(), bh2.offset());
        }

        mod tests_gpt_4o {
            use super::*;

            #[test]
            fn test_block_handle_creation() {
                let handle = BlockHandle::new(100, 200);
                assert_eq!(handle.offset(), 100);
                assert_eq!(handle.size(), 200);
            }

            #[test]
            fn test_block_handle_offset() {
                let handle = BlockHandle::new(150, 300);
                assert_eq!(handle.offset(), 150);
            }

            #[test]
            fn test_block_handle_size() {
                let handle = BlockHandle::new(150, 300);
                assert_eq!(handle.size(), 300);
            }

            #[test]
            fn test_block_handle_encode() {
                let handle = BlockHandle::new(100, 200);
                let mut dst = [0u8; 10];
                let size = handle.encode(&mut dst);
                assert!(size > 0);
            }

            #[test]
            fn test_block_handle_decode() {
                let handle = BlockHandle::new(100, 200);
                let mut dst = [0u8; 10];
                let size = handle.encode(&mut dst);
                let (decoded_handle, decoded_size) = BlockHandle::decode(&dst).unwrap();
                assert_eq!(size, decoded_size);
                assert_eq!(handle.offset(), decoded_handle.offset());
                assert_eq!(handle.size(), decoded_handle.size());
            }

            #[test]
            fn test_block_handle_encode_decode_boundary() {
                let handle = BlockHandle::new(usize::MAX, usize::MAX);
                let mut dst = [0u8; 20];
                let size = handle.encode(&mut dst);
                let (decoded_handle, decoded_size) = BlockHandle::decode(&dst).unwrap();
                assert_eq!(size, decoded_size);
                assert_eq!(handle.offset(), decoded_handle.offset());
                assert_eq!(handle.size(), decoded_handle.size());
            }

            #[test]
            fn test_block_handle_encode_decode_zero() {
                let handle = BlockHandle::new(0, 0);
                let mut dst = [0u8; 10];
                let size = handle.encode(&mut dst);
                let (decoded_handle, decoded_size) = BlockHandle::decode(&dst).unwrap();
                assert_eq!(size, decoded_size);
                assert_eq!(handle.offset(), decoded_handle.offset());
                assert_eq!(handle.size(), decoded_handle.size());
            }
        }
    }
}
