use crate::coredef::types::DbIterator;
use crc::Crc;

pub mod cache;
pub mod filter;
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

pub const CRC: Crc<u32> = Crc::<u32>::new(&crc::CRC_32_CKSUM);
const MASK_DELTA: u32 = 0xa282ead8;

pub fn mask_crc(c: u32) -> u32 {
    (c.wrapping_shr(15) | c.wrapping_shl(17)).wrapping_add(MASK_DELTA)
}

pub fn unmask_crc(c: u32) -> u32 {
    let c = c.wrapping_sub(MASK_DELTA);
    c.wrapping_shr(17) | c.wrapping_shl(15)
}
