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

pub type FileNum = u64;

#[derive(Clone)]
pub struct FileMetaData {}

#[derive(Clone, PartialEq)]
pub enum FileType {}
