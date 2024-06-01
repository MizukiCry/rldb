use super::types::SeqNum;
use integer_encoding::{FixedInt, FixedIntWriter, VarInt, VarIntWriter};
use std::io::Write as _;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ValueType {
    TypeDeletion = 0,
    TypeValue = 1,
}

pub type UserKey<'a> = &'a [u8];

/// InternalKey
/// [key, tag]
pub type InternalKey<'a> = &'a [u8];

/// MemtableKey
/// [key_len, key, tag, (value_len, value)]
/// key_len: varint32, len(key) + 8 (tag length)
/// tag: 8 bytes, entry type + sequence number
/// (value_len, value): optional
pub type MemtableKey<'a> = &'a [u8];

/// LookupKey
/// [key_len, key, tag]
/// key_len: varint32, len(key) + 8 (tag length)
pub struct LookupKey {
    key: Vec<u8>,
    key_offset: usize,
}

impl LookupKey {
    pub fn new(key: UserKey, seqnum: SeqNum) -> Self {
        Self::new_with_type(key, seqnum, ValueType::TypeValue)
    }

    pub fn new_with_type(key: UserKey, seqnum: SeqNum, t: ValueType) -> Self {
        let ikey_len = key.len() + 8;
        let mut buf = vec![0; ikey_len + ikey_len.required_space()];
        let mut writer = buf.as_mut_slice();
        writer.write_varint(ikey_len).unwrap();
        writer.write_all(key).unwrap();
        writer.write_fixedint(seqnum << 8 | t as u64).unwrap();
        Self {
            key: buf,
            key_offset: ikey_len.required_space(),
        }
    }

    pub fn user_key(&self) -> UserKey {
        &self.key[self.key_offset..self.key.len() - 8]
    }

    pub fn internal_key(&self) -> InternalKey {
        &self.key[self.key_offset..]
    }

    pub fn memtable_key(&self) -> MemtableKey {
        &self.key
    }
}

pub fn parse_tag(tag: u64) -> (ValueType, SeqNum) {
    match tag & 0xff {
        0 => (ValueType::TypeDeletion, tag >> 8),
        _ => (ValueType::TypeValue, tag >> 8),
    }
}

pub fn parse_internal_key(ikey: InternalKey) -> (ValueType, SeqNum, UserKey) {
    if ikey.is_empty() {
        return (ValueType::TypeValue, 0, ikey);
    }
    assert!(ikey.len() >= 8);
    let (t, seqnum) = parse_tag(FixedInt::decode_fixed(&ikey[ikey.len() - 8..]).unwrap());
    (t, seqnum, &ikey[..ikey.len() - 8])
}

/// In-place truncate the internal key to the user key
pub fn truncate_ikey_to_key(ikey: &mut Vec<u8>) {
    assert!(ikey.len() >= 8);
    ikey.truncate(ikey.len() - 8);
}

/// Parse the memtable key
/// (key_len, key_offset, tag, value_len, value_offset)
pub fn parse_memtable_key(mkey: MemtableKey) -> (usize, usize, u64, usize, usize) {
    let (key_len, key_offset) = usize::decode_var(mkey).unwrap();
    let p = key_offset + key_len - 8;
    if mkey.len() <= p {
        return (key_len - 8, key_offset, 0, 0, 0);
    }
    let tag = u64::decode_fixed(&mkey[p..p + 8]).unwrap();
    let (value_len, value_offset) = usize::decode_var(&mkey[p + 8..]).unwrap();
    (
        key_len - 8,
        key_offset,
        tag,
        value_len,
        p + 8 + value_offset,
    )
}

pub fn build_memtable_key(key: &[u8], value: &[u8], t: ValueType, seqnum: SeqNum) -> Vec<u8> {
    let key_len = key.len() + 8;
    let value_len = value.len();
    let mut buf =
        vec![0; key_len + key_len.required_space() + value_len + value_len.required_space()];
    let mut writer = buf.as_mut_slice();

    writer.write_varint(key_len).unwrap();
    writer.write_all(key).unwrap();
    writer.write_fixedint(seqnum << 8 | t as u64).unwrap();
    writer.write_varint(value_len).unwrap();
    writer.write_all(value).unwrap();

    buf
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests_leveldb_rs {
        use super::*;

        #[test]
        fn test_memtable_lookupkey() {
            use integer_encoding::VarInt;

            let lk1 = LookupKey::new("abcde".as_bytes(), 123);
            let lk2 = LookupKey::new("xyabxy".as_bytes(), 97);

            // Assert correct allocation strategy
            assert_eq!(lk1.key.len(), 14);
            assert_eq!(lk1.key.capacity(), 14);

            assert_eq!(lk1.user_key(), "abcde".as_bytes());
            assert_eq!(u32::decode_var(lk1.memtable_key()).unwrap(), (13, 1));
            assert_eq!(
                lk2.internal_key(),
                vec![120, 121, 97, 98, 120, 121, 1, 97, 0, 0, 0, 0, 0, 0].as_slice()
            );
        }

        #[test]
        fn test_build_memtable_key() {
            assert_eq!(
                build_memtable_key(
                    "abc".as_bytes(),
                    "123".as_bytes(),
                    ValueType::TypeValue,
                    231
                ),
                vec![11, 97, 98, 99, 1, 231, 0, 0, 0, 0, 0, 0, 3, 49, 50, 51]
            );
            assert_eq!(
                build_memtable_key("".as_bytes(), "123".as_bytes(), ValueType::TypeValue, 231),
                vec![8, 1, 231, 0, 0, 0, 0, 0, 0, 3, 49, 50, 51]
            );
            assert_eq!(
                build_memtable_key(
                    "abc".as_bytes(),
                    "123".as_bytes(),
                    ValueType::TypeDeletion,
                    231
                ),
                vec![11, 97, 98, 99, 0, 231, 0, 0, 0, 0, 0, 0, 3, 49, 50, 51]
            );
            assert_eq!(
                build_memtable_key(
                    "abc".as_bytes(),
                    "".as_bytes(),
                    ValueType::TypeDeletion,
                    231
                ),
                vec![11, 97, 98, 99, 0, 231, 0, 0, 0, 0, 0, 0, 0]
            );
        }
    }

    mod tests_gpt_4o {
        use super::*;

        #[test]
        fn test_lookup_key_new() {
            let key: UserKey = b"test_key";
            let seqnum: SeqNum = 12345;
            let lookup_key = LookupKey::new(key, seqnum);

            assert_eq!(lookup_key.user_key(), key);
            assert_eq!(lookup_key.internal_key().len(), key.len() + 8);
        }

        #[test]
        fn test_lookup_key_new_with_type() {
            let key: UserKey = b"test_key";
            let seqnum: SeqNum = 12345;
            let lookup_key = LookupKey::new_with_type(key, seqnum, ValueType::TypeDeletion);

            assert_eq!(lookup_key.user_key(), key);
            assert_eq!(lookup_key.internal_key().len(), key.len() + 8);
        }

        #[test]
        fn test_parse_tag() {
            let tag = 12345 << 8 | ValueType::TypeValue as u64;
            let (value_type, seqnum) = parse_tag(tag);

            assert_eq!(value_type, ValueType::TypeValue);
            assert_eq!(seqnum, 12345);

            let tag = 12345 << 8 | ValueType::TypeDeletion as u64;
            let (value_type, seqnum) = parse_tag(tag);

            assert_eq!(value_type, ValueType::TypeDeletion);
            assert_eq!(seqnum, 12345);
        }

        #[test]
        fn test_parse_internal_key() {
            let key: UserKey = b"test_key";
            let seqnum: SeqNum = 12345;
            let mut buf = vec![0; key.len() + 8];
            let mut writer = buf.as_mut_slice();
            writer.write_all(key).unwrap();
            writer
                .write_fixedint(seqnum << 8 | ValueType::TypeValue as u64)
                .unwrap();

            let (value_type, parsed_seqnum, parsed_key) = parse_internal_key(&buf);

            assert_eq!(value_type, ValueType::TypeValue);
            assert_eq!(parsed_seqnum, seqnum);
            assert_eq!(parsed_key, key);
        }

        #[test]
        fn test_truncate_ikey_to_key() {
            let key: UserKey = b"test_key";
            let seqnum: SeqNum = 12345;
            let mut buf = vec![0; key.len() + 8];
            let mut writer = buf.as_mut_slice();
            writer.write_all(key).unwrap();
            writer
                .write_fixedint(seqnum << 8 | ValueType::TypeValue as u64)
                .unwrap();

            truncate_ikey_to_key(&mut buf);

            assert_eq!(buf, key);
        }

        #[test]
        fn test_parse_memtable_key() {
            let key: UserKey = b"test_key";
            let value: &[u8] = b"test_value";
            let seqnum: SeqNum = 12345;
            let mkey = build_memtable_key(key, value, ValueType::TypeValue, seqnum);

            let (key_len, key_offset, tag, value_len, value_offset) = parse_memtable_key(&mkey);

            assert_eq!(key_len, key.len());
            assert_eq!(key_offset, 1);
            assert_eq!(tag, seqnum << 8 | ValueType::TypeValue as u64);
            assert_eq!(value_len, value.len());
            assert_eq!(&mkey[value_offset..value_offset + value_len], value);
        }

        #[test]
        fn test_build_memtable_key() {
            let key: UserKey = b"test_key";
            let value: &[u8] = b"test_value";
            let seqnum: SeqNum = 12345;
            let mkey = build_memtable_key(key, value, ValueType::TypeValue, seqnum);

            let (key_len, key_offset, tag, value_len, value_offset) = parse_memtable_key(&mkey);

            assert_eq!(key_len, key.len());
            assert_eq!(key_offset, 1);
            assert_eq!(tag, seqnum << 8 | ValueType::TypeValue as u64);
            assert_eq!(value_len, value.len());
            assert_eq!(&mkey[value_offset..value_offset + value_len], value);
        }

        #[test]
        fn test_edge_cases() {
            // Test with empty key and value
            let key: UserKey = b"";
            let value: &[u8] = b"";
            let seqnum: SeqNum = 0;

            let lookup_key = LookupKey::new(key, seqnum);
            assert_eq!(lookup_key.user_key(), key);

            let (value_type, parsed_seqnum) = parse_tag(seqnum << 8 | ValueType::TypeValue as u64);
            assert_eq!(value_type, ValueType::TypeValue);
            assert_eq!(parsed_seqnum, seqnum);

            let ikey = lookup_key.internal_key();
            let (value_type, parsed_seqnum, parsed_key) = parse_internal_key(ikey);
            assert_eq!(value_type, ValueType::TypeValue);
            assert_eq!(parsed_seqnum, seqnum);
            assert_eq!(parsed_key, key);

            let mkey = build_memtable_key(key, value, ValueType::TypeValue, seqnum);
            let (key_len, key_offset, tag, value_len, _) = parse_memtable_key(&mkey);
            assert_eq!(key_len, key.len());
            assert_eq!(key_offset, 1);
            assert_eq!(tag, seqnum << 8 | ValueType::TypeValue as u64);
            assert_eq!(value_len, value.len());
        }
    }
}
