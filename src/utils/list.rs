/// A doubly linked list with a fixed capacity.
/// Implemented based on vector.
use std::fmt::Display;

pub struct List<T> {
    head: usize,
    tail: usize,
    prev: Vec<usize>,
    next: Vec<usize>,
    value: Vec<Option<T>>,
    pool: Vec<usize>,
    capacity: usize,
    size: usize,
}

impl<T> List<T> {
    pub fn new(capacity: usize) -> Self {
        // two extra nodes for head and tail
        // head: capacity, tail: capacity + 1
        let mut list = List {
            head: capacity,
            tail: capacity + 1,
            prev: vec![0; capacity + 2],
            next: vec![0; capacity + 2],
            value: (0..capacity).map(|_| None).collect(),
            pool: (0..capacity).collect(),
            capacity,
            size: 0,
        };
        list.next[list.head] = list.tail;
        list.prev[list.tail] = list.head;
        list
    }

    pub fn size(&self) -> usize {
        self.size
    }

    #[allow(dead_code)]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    pub fn empty(&self) -> bool {
        self.size == 0
    }

    pub fn push_front(&mut self, value: T) -> usize {
        assert!(self.size < self.capacity, "list is full");
        let pos = self.pool[self.size];
        self.value[pos] = Some(value);
        self.prev[pos] = self.head;
        self.next[pos] = self.next[self.head];
        self.prev[self.next[self.head]] = pos;
        self.next[self.head] = pos;
        self.size += 1;
        pos
    }

    pub fn remove(&mut self, pos: usize) -> T {
        assert!(pos < self.capacity, "invalid position");
        assert!(self.value[pos].is_some(), "position is empty");
        self.next[self.prev[pos]] = self.next[pos];
        self.prev[self.next[pos]] = self.prev[pos];
        self.size -= 1;
        self.pool[self.size] = pos;
        self.value[pos].take().unwrap()
    }

    pub fn pop_back(&mut self) -> T {
        assert!(!self.empty(), "list is empty");
        self.remove(self.prev[self.tail])
    }

    pub fn move_to_front(&mut self, pos: usize) {
        assert!(pos < self.capacity, "invalid position");
        assert!(self.value[pos].is_some(), "position is empty");
        let value = self.remove(pos);
        self.push_front(value);
    }
}

impl<T: Display> List<T> {
    #[allow(dead_code)]
    fn print(&self) {
        println!("List size: {}", self.size);
        let mut pos = self.next[self.head];
        while pos != self.tail {
            print!("{} ", self.value[pos].as_ref().unwrap());
            pos = self.next[pos];
        }
        println!();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_list() {
        let mut list = List::new(3);
        assert_eq!(list.size(), 0);
        assert_eq!(list.capacity(), 3);

        let node1 = list.push_front(1);
        assert_eq!(list.size(), 1);
        assert_eq!(list.capacity(), 3);
        assert_eq!(node1, 0);

        let node2 = list.push_front(2);
        assert_eq!(list.size(), 2);
        assert_eq!(list.capacity(), 3);
        assert_eq!(node2, 1);

        let node3 = list.push_front(3);
        assert_eq!(list.size(), 3);
        assert_eq!(list.capacity(), 3);
        assert_eq!(node3, 2);

        let value = list.remove(node2);
        assert_eq!(value, 2);
        assert_eq!(list.size(), 2);
        assert_eq!(list.capacity(), 3);

        let value = list.pop_back();
        assert_eq!(value, 1);
        assert_eq!(list.size(), 1);
        assert_eq!(list.capacity(), 3);

        list.move_to_front(node3);
        assert_eq!(list.size(), 1);
        assert_eq!(list.capacity(), 3);
    }

    #[test]
    fn test_list_random() {
        const N: usize = 200;
        for _ in 0..N {
            let mut list = List::new(N);
            let mut pos = Vec::with_capacity(N);
            let mut values = Vec::with_capacity(N);
            for i in 0..N {
                let value = rand::random::<i32>();
                pos.push(list.push_front(value));
                assert!(list.size() == i + 1);
                values.insert(0, (i, value));
            }

            for _ in 0..N {
                let i = rand::random::<usize>() % N;
                list.move_to_front(pos[i]);

                let pair = values.remove(values.iter().position(|&(j, _)| i == j).unwrap());
                values.insert(0, pair);
            }

            for _ in 0..N {
                assert_eq!(list.pop_back(), values.pop().unwrap().1);
            }
            assert!(list.empty());
        }
    }

    #[test]
    #[should_panic]
    fn test_list_panic_1() {
        let mut list: List<i32> = List::new(3);
        list.remove(0);
    }

    #[test]
    #[should_panic]
    fn test_list_panic_2() {
        let mut list = List::new(3);
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        list.push_front(4);
    }

    #[test]
    #[should_panic]
    fn test_list_panic_3() {
        let mut list = List::new(3);
        list.push_front(1);
        list.remove(1);
    }

    #[test]
    #[should_panic]
    fn test_list_panic_4() {
        let mut list = List::new(3);
        list.push_front(1);
        list.move_to_front(1);
    }

    mod tests_gpt_4o {
        use super::*;

        #[test]
        fn test_new_list() {
            let list: List<i32> = List::new(5);
            assert_eq!(list.size(), 0);
            assert_eq!(list.capacity(), 5);
            assert!(list.empty());
        }

        #[test]
        fn test_push_front() {
            let mut list = List::new(5);
            list.push_front(1);
            assert_eq!(list.size(), 1);
            assert!(!list.empty());
        }

        #[test]
        fn test_multiple_push_front() {
            let mut list = List::new(5);
            list.push_front(1);
            list.push_front(2);
            list.push_front(3);
            assert_eq!(list.size(), 3);
        }

        #[test]
        fn test_remove() {
            let mut list = List::new(5);
            let pos1 = list.push_front(1);
            let pos2 = list.push_front(2);
            assert_eq!(list.size(), 2);
            assert_eq!(list.remove(pos1), 1);
            assert_eq!(list.size(), 1);
            assert_eq!(list.remove(pos2), 2);
            assert_eq!(list.size(), 0);
            assert!(list.empty());
        }

        #[test]
        fn test_pop_back() {
            let mut list = List::new(5);
            list.push_front(1);
            list.push_front(2);
            assert_eq!(list.pop_back(), 1);
            assert_eq!(list.size(), 1);
            assert_eq!(list.pop_back(), 2);
            assert_eq!(list.size(), 0);
            assert!(list.empty());
        }

        #[test]
        fn test_move_to_front() {
            let mut list = List::new(5);
            let pos1 = list.push_front(1);
            let _ = list.push_front(2);
            let _ = list.push_front(3);
            list.move_to_front(pos1);
            assert_eq!(list.size(), 3);

            // Verify the order
            assert_eq!(list.pop_back(), 2);
            assert_eq!(list.pop_back(), 3);
            assert_eq!(list.pop_back(), 1);
        }

        #[test]
        #[should_panic(expected = "list is full")]
        fn test_push_front_overflow() {
            let mut list = List::new(1);
            list.push_front(1);
            list.push_front(2); // This should panic
        }

        #[test]
        #[should_panic(expected = "invalid position")]
        fn test_remove_invalid_position() {
            let mut list: List<i32> = List::new(5);
            list.remove(10); // This should panic
        }

        #[test]
        #[should_panic(expected = "position is empty")]
        fn test_remove_empty_position() {
            let mut list: List<i32> = List::new(5);
            list.remove(0); // This should panic
        }

        #[test]
        #[should_panic(expected = "list is empty")]
        fn test_pop_back_empty_list() {
            let mut list: List<i32> = List::new(5);
            list.pop_back(); // This should panic
        }

        #[test]
        #[should_panic(expected = "invalid position")]
        fn test_move_to_front_invalid_position() {
            let mut list: List<i32> = List::new(5);
            list.move_to_front(10); // This should panic
        }

        #[test]
        #[should_panic(expected = "position is empty")]
        fn test_move_to_front_empty_position() {
            let mut list: List<i32> = List::new(5);
            list.move_to_front(0); // This should panic
        }
    }

    mod tests_gemini_1_5_flash {
        use super::*;

        #[test]
        fn test_new() {
            let list: List<i32> = List::new(10);
            assert_eq!(list.capacity(), 10);
            assert_eq!(list.size(), 0);
            assert!(list.empty());
        }

        #[test]
        fn test_push_front() {
            let mut list: List<i32> = List::new(3);
            assert_eq!(list.push_front(1), 0);
            assert_eq!(list.push_front(2), 1);
            assert_eq!(list.push_front(3), 2);
            assert_eq!(list.size(), 3);
        }

        #[test]
        #[should_panic(expected = "list is full")]
        fn test_push_front_full() {
            let mut list: List<i32> = List::new(1);
            list.push_front(1);
            list.push_front(2);
        }

        #[test]
        fn test_remove() {
            let mut list: List<i32> = List::new(3);
            list.push_front(1);
            list.push_front(2);
            list.push_front(3);
            assert_eq!(list.remove(1), 2);
            assert_eq!(list.size(), 2);
        }

        #[test]
        #[should_panic(expected = "invalid position")]
        fn test_remove_invalid_position() {
            let mut list: List<i32> = List::new(3);
            list.push_front(1);
            list.push_front(2);
            list.push_front(3);
            list.remove(3);
        }

        #[test]
        #[should_panic(expected = "position is empty")]
        fn test_remove_empty_position() {
            let mut list: List<i32> = List::new(3);
            list.push_front(1);
            list.push_front(2);
            list.push_front(3);
            list.remove(1);
            list.remove(1);
        }

        #[test]
        fn test_pop_back() {
            let mut list: List<i32> = List::new(3);
            list.push_front(1);
            list.push_front(2);
            list.push_front(3);
            assert_eq!(list.pop_back(), 1);
            assert_eq!(list.size(), 2);
        }

        #[test]
        #[should_panic(expected = "list is empty")]
        fn test_pop_back_empty() {
            let mut list: List<i32> = List::new(3);
            list.pop_back();
        }

        #[test]
        fn test_move_to_front() {
            let mut list: List<i32> = List::new(3);
            list.push_front(1);
            list.push_front(2);
            list.push_front(3);
            list.move_to_front(1);
            assert_eq!(list.size(), 3);
            assert_eq!(list.next[list.head], 1);
            assert_eq!(list.prev[list.tail], 0);
            assert_eq!(list.pop_back(), 1);
            assert_eq!(list.pop_back(), 3);
            assert_eq!(list.pop_back(), 2);
            assert!(list.empty());
        }

        #[test]
        #[should_panic(expected = "invalid position")]
        fn test_move_to_front_invalid_position() {
            let mut list: List<i32> = List::new(3);
            list.push_front(1);
            list.push_front(2);
            list.push_front(3);
            list.move_to_front(3);
        }

        #[test]
        #[should_panic(expected = "position is empty")]
        fn test_move_to_front_empty_position() {
            let mut list: List<i32> = List::new(3);
            list.push_front(1);
            list.push_front(2);
            list.push_front(3);
            list.remove(1);
            list.move_to_front(1);
        }
    }
}
