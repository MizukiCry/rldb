use crate::coredef::types::DbIterator;

pub mod cache;
mod list;
pub mod skip_list;

pub fn test_iterator_properties(mut iter: impl DbIterator) {
    assert!(!iter.valid());
    assert!(iter.advance());
    assert!(iter.valid());
    let first = iter.current_kv();
    assert!(iter.advance());
    let second = iter.current_kv();
    assert!(iter.advance());
    let third = iter.current_kv();
    assert!(iter.advance());
    assert!(iter.valid());
    let fourth = iter.current_kv();
    assert!(!iter.advance());
    assert!(!iter.valid());

    iter.reset();
    iter.seek(&fourth.as_ref().unwrap().0);
    assert!(iter.valid());
    iter.seek(&second.as_ref().unwrap().0);
    assert!(iter.valid());
    iter.prev();
    assert_eq!(first, iter.current_kv());

    iter.reset();
    assert!(!iter.valid());
    assert!(iter.advance());
    assert_eq!(first, iter.current_kv());
    assert!(iter.advance());
    assert_eq!(second, iter.current_kv());
    assert!(iter.advance());
    assert_eq!(third, iter.current_kv());
    assert!(iter.prev());
    assert_eq!(second, iter.current_kv());
    assert!(iter.prev());
    assert_eq!(first, iter.current_kv());
    assert!(!iter.prev());
    assert!(!iter.valid());
}
