// use rand::rngs::StdRng;
// use std::{cell::RefCell, rc::Rc};

// struct Node {
//     key: Vec<u8>,
//     value: Vec<u8>,
//     next: Option<Box<Node>>,
//     skips: Vec<Option<*mut Node>>,
// }

// struct InnerSkipList {
//     head: Box<Node>,
//     rand_rng: StdRng,
//     len: usize,
//     approx_size: usize,
//     cmp: Rc<dyn Cmp>,
// }

// impl InnerSkipList {}

// pub struct SkipList(Rc<RefCell<InnerSkipList>>);

// impl SkipList {}

// #[cfg(test)]
// mod tests {
//     use super::*;
// }
