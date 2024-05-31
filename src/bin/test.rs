pub struct Node {
    next: Option<Box<Node>>,
}

pub struct List {
    head: Box<Node>,
}

impl List {
    pub fn new() -> Self {
        List {
            head: Box::new(Node { next: None }),
        }
    }

    pub fn push_front(&mut self) -> *mut Box<Node> {
        let mut node = Box::new(Node { next: None });
        let ref_node: *mut Box<Node> = &mut node;
        println!("-- {}", ref_node as usize);

        node.next = self.head.next.take();
        self.head.next = Some(node);
        ref_node
    }
}

fn main() {
    let mut list = List::new();
    let node1 = list.push_front();
    let node2 = list.push_front();
    println!("{}, {}", node1 as usize, node2 as usize);
}
