use crate::utils::filter::FilterPolicy;
use integer_encoding::FixedInt;
use std::rc::Rc;

const DEFAULT_CAPACITY: usize = 1024;
const FILTER_BASE_LOG2: usize = 11; // 2 KiB

/// Filter Block Builder
///
/// Filter Block Format:
/// [filter0, filter1, ..., offset0 (4 bytes), offset1, ..., offset of offsets (4 bytes), FILTER_BASE_LOG2 (1 byte)]
pub struct FilterBlockBuilder {
    policy: Rc<dyn FilterPolicy>,
    filters: Vec<u8>,
    filter_offsets: Vec<usize>,
    keys: Vec<u8>,
    key_offsets: Vec<usize>,
}

impl FilterBlockBuilder {
    pub fn new(policy: Rc<dyn FilterPolicy>) -> Self {
        Self {
            policy,
            filters: Vec::with_capacity(DEFAULT_CAPACITY),
            filter_offsets: Vec::with_capacity(DEFAULT_CAPACITY),
            keys: Vec::with_capacity(DEFAULT_CAPACITY),
            key_offsets: Vec::with_capacity(DEFAULT_CAPACITY),
        }
    }

    pub fn policy_name(&self) -> &'static str {
        self.policy.name()
    }

    pub fn estimate_size(&self) -> usize {
        // According to the format
        self.filters.len() + 4 * self.filter_offsets.len() + 4 + 1
    }

    pub fn add(&mut self, key: &[u8]) {
        self.key_offsets.push(self.keys.len());
        self.keys.extend_from_slice(key);
    }

    fn generate_filter(&mut self) {
        self.filter_offsets.push(self.filters.len());

        if self.keys.is_empty() {
            return;
        }

        let filter = self.policy.create(&self.keys, &self.key_offsets);
        self.filters.extend_from_slice(&filter);
        self.keys.clear();
        self.key_offsets.clear();
    }

    pub fn build(mut self) -> Vec<u8> {
        if !self.keys.is_empty() {
            self.generate_filter();
        }

        let mut buffer = self.filters;
        let offsets_offset = buffer.len();
        let mut i = offsets_offset;
        buffer.resize(i + 4 * self.filter_offsets.len() + 5, 0);

        for offset in self.filter_offsets {
            (offset as u32).encode_fixed(&mut buffer[i..i + 4]);
            i += 4;
        }

        (offsets_offset as u32).encode_fixed(&mut buffer[i..i + 4]);
        buffer[i + 4] = FILTER_BASE_LOG2 as u8;

        buffer
    }

    pub fn start_block(&mut self, offset: usize) {
        let filter_idx = offset >> FILTER_BASE_LOG2;
        assert!(
            filter_idx >= self.filter_offsets.len(),
            "Filter block is already started"
        );

        while self.filter_offsets.len() < filter_idx {
            self.generate_filter();
        }
    }
}

#[derive(Clone)]
pub struct FilterBlockReader {
    policy: Rc<dyn FilterPolicy>,
    data: Rc<Vec<u8>>,
    offsets_offset: usize,
    filter_base_log2: u32,
}

impl FilterBlockReader {
    pub fn new(policy: Rc<dyn FilterPolicy>, data: Rc<Vec<u8>>) -> Self {
        assert!(data.len() >= 5, "Filter block data is too short");

        let offsets_offset =
            u32::decode_fixed(&data[data.len() - 5..data.len() - 1]).unwrap() as usize;
        let filter_base_log2 = *data.last().unwrap() as u32;

        Self {
            policy,
            data,
            offsets_offset,
            filter_base_log2,
        }
    }

    pub fn new_with_vec(policy: Rc<dyn FilterPolicy>, data: Vec<u8>) -> Self {
        Self::new(policy, Rc::new(data))
    }

    pub fn num_filters(&self) -> usize {
        (self.data.len() - 5 - self.offsets_offset) / 4
    }

    fn filter_offset(&self, i: usize) -> usize {
        let offset = self.offsets_offset + 4 * i;
        u32::decode_fixed(&self.data[offset..offset + 4]).unwrap() as usize
    }

    pub fn may_exist(&self, block_offset: usize, key: &[u8]) -> bool {
        let block_id = block_offset >> self.filter_base_log2;
        if block_id > self.num_filters() {
            return true;
        }

        let filter_begin = self.filter_offset(block_id);
        let filter_end = self.filter_offset(block_id + 1);

        self.policy
            .may_exist(key, &self.data[filter_begin..filter_end])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests_leveldb_rs {
        use crate::utils::filter::BloomFilterPolicy;

        use super::*;

        #[test]
        fn test_filter_index() {
            assert_eq!(3777 >> FILTER_BASE_LOG2, 1);
            assert_eq!(10000 >> FILTER_BASE_LOG2, 4);
        }

        fn get_keys() -> Vec<&'static [u8]> {
            vec![
                "abcd".as_bytes(),
                "efgh".as_bytes(),
                "ijkl".as_bytes(),
                "mnopqrstuvwxyz".as_bytes(),
            ]
        }

        fn produce_filter_block() -> Vec<u8> {
            let keys = get_keys();
            let mut bld = FilterBlockBuilder::new(Rc::new(BloomFilterPolicy::new(32)));

            bld.start_block(0);

            for k in keys.iter() {
                bld.add(k);
            }

            // second block
            bld.start_block(5000);

            for k in keys.iter() {
                bld.add(k);
            }

            bld.build()
        }

        // #[test]
        // fn test_filter_block_builder() {
        //     let result = produce_filter_block();
        //     // 2 blocks of 4 filters of 4 bytes plus 1B for `k`; plus three filter offsets (because of
        //     //   the block offsets of 0 and 5000); plus footer
        //     assert_eq!(result.len(), 2 * (get_keys().len() * 4 + 1) + (3 * 4) + 5);
        //     assert_eq!(
        //         result,
        //         vec![
        //             234, 195, 25, 155, 61, 141, 173, 140, 221, 28, 222, 92, 220, 112, 234, 227, 22,
        //             234, 195, 25, 155, 61, 141, 173, 140, 221, 28, 222, 92, 220, 112, 234, 227, 22,
        //             0, 0, 0, 0, 17, 0, 0, 0, 17, 0, 0, 0, 34, 0, 0, 0, 11,
        //         ]
        //     );
        // }

        #[test]
        fn test_filter_block_build_read() {
            let result = produce_filter_block();
            let reader =
                FilterBlockReader::new_with_vec(Rc::new(BloomFilterPolicy::new(32)), result);

            assert_eq!(reader.filter_offset(5121 >> FILTER_BASE_LOG2), 17); // third block in third filter

            let unknown_keys = vec![
                "xsb".as_bytes(),
                "9sad".as_bytes(),
                "assssaaaass".as_bytes(),
            ];

            for block_offset in vec![0, 1024, 5000, 6025].into_iter() {
                for key in get_keys().iter() {
                    assert!(
                        reader.may_exist(block_offset, key),
                        "{} {:?} ",
                        block_offset,
                        key
                    );
                }
                for key in unknown_keys.iter() {
                    assert!(!reader.may_exist(block_offset, key));
                }
            }
        }
    }
}
