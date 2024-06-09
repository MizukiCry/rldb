use std::rc::Rc;

use super::cmp::{Cmp, DefaultCmp};

const MAX_BLOCK_SIZE: usize = 4 * 1024; // 4KB

#[derive(Clone)]
pub struct Options {
    pub cmp: Rc<dyn Cmp>,

    pub block_size: usize,

    // Number of keys per restart point
    pub block_restart_interval: usize,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            cmp: Rc::new(DefaultCmp),
            block_size: MAX_BLOCK_SIZE,
            block_restart_interval: 16,
        }

        // todo!()
    }
}
