use crate::coredef::types::SeqNum;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

type SnapshotID = u64;

#[derive(Clone)]
struct InnerSnapshot {
    id: u64,
    seqnum: SeqNum,
    list: SnapshotList,
}

impl Drop for InnerSnapshot {
    fn drop(&mut self) {
        self.list.inner.borrow_mut().map.remove(&self.id);
    }
}

#[derive(Clone)]
pub struct Snapshot {
    inner: Rc<InnerSnapshot>,
}

impl Snapshot {
    pub fn seqnum(&self) -> SeqNum {
        self.inner.seqnum
    }
}

#[derive(Clone)]
struct InnerSnapshotList {
    map: HashMap<SnapshotID, SeqNum>,
    current_id: SnapshotID,
}

#[derive(Clone)]
pub struct SnapshotList {
    inner: Rc<RefCell<InnerSnapshotList>>,
}

impl Default for SnapshotList {
    fn default() -> Self {
        Self::new()
    }
}

impl SnapshotList {
    pub fn new() -> Self {
        Self {
            inner: Rc::new(RefCell::new(InnerSnapshotList {
                map: HashMap::new(),
                current_id: 0,
            })),
        }
    }

    pub fn new_snapshot(&mut self, seqnum: SeqNum) -> Snapshot {
        let list = self.clone();
        let mut inner = self.inner.borrow_mut();

        inner.current_id += 1;
        let current_id = inner.current_id;
        inner.map.insert(current_id, seqnum);

        Snapshot {
            inner: Rc::new(InnerSnapshot {
                id: current_id,
                seqnum,
                list,
            }),
        }
    }

    /// Returns the smallest sequence number
    pub fn oldest(&self) -> (SnapshotID, SeqNum) {
        self.inner
            .borrow()
            .map
            .iter()
            .min_by_key(|(_, v)| **v)
            .map_or((0, 0), |(x, y)| (*x, *y))
    }

    /// Returns the largest sequence number
    pub fn newest(&self) -> (SnapshotID, SeqNum) {
        self.inner
            .borrow()
            .map
            .iter()
            .max_by_key(|(_, v)| **v)
            .map_or((0, 0), |(x, y)| (*x, *y))
    }

    pub fn empty(&self) -> bool {
        self.inner.borrow().current_id == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(unused_variables)]
    #[test]
    fn test_snapshot_list() {
        let mut l = SnapshotList::new();

        {
            assert!(l.empty());
            let a = l.new_snapshot(1);

            {
                let b = l.new_snapshot(2);

                {
                    let c = l.new_snapshot(3);

                    assert!(!l.empty());
                    assert_eq!(l.oldest().1, 1);
                    assert_eq!(l.newest().1, 3);
                }

                assert_eq!(l.newest().1, 2);
                assert_eq!(l.oldest().1, 1);
            }

            assert_eq!(l.oldest().1, 1);
        }
        assert_eq!(l.oldest().1, 0);
    }
}
