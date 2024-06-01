use super::{
    key::{parse_internal_key, parse_tag, LookupKey},
    types::MAX_SEQNUM,
};
use integer_encoding::{FixedInt, VarInt};
use std::{cmp::Ordering, rc::Rc};

pub trait Cmp {
    fn cmp(&self, a: &[u8], b: &[u8]) -> Ordering;

    /// Returns the shortest separator between a and b
    /// such that a < separator < b.
    fn find_shortest_separator(&self, a: &[u8], b: &[u8]) -> Vec<u8>;

    /// Returns the shortest successor of a
    /// such that a < successor.
    fn find_shortest_successor(&self, a: &[u8]) -> Vec<u8>;

    fn name(&self) -> &'static str;
}

/// Default bytewise comparator
#[derive(Clone, Copy)]
pub struct DefaultCmp;

impl Cmp for DefaultCmp {
    fn cmp(&self, a: &[u8], b: &[u8]) -> Ordering {
        a.cmp(b)
    }

    fn find_shortest_separator(&self, a: &[u8], b: &[u8]) -> Vec<u8> {
        if a == b {
            return a.to_vec();
        }
        assert!(a < b);

        let mut len = (0..=a.len())
            .into_iter()
            .find(|&i| i >= a.len() || i >= b.len() || a[i] != b[i])
            .unwrap();
        let mut result = a[..len].to_vec();

        if len < a.len() && len < b.len() {
            if a[len] + 1 < b[len] {
                result.push(a[len] + 1);
                return result;
            }
            result.push(a[len]);
            len += 1;
        }

        loop {
            if len < a.len() {
                if a[len] < u8::MAX {
                    result.push(a[len] + 1);
                    return result;
                }
                result.push(a[len]);
            } else {
                result.push(0);
                if len >= b.len() || b[len] != 0 {
                    return result;
                }
            }
        }
    }

    fn find_shortest_successor(&self, a: &[u8]) -> Vec<u8> {
        let mut result = a.to_vec();
        if let Some(p) = result.iter().position(|&x| x != u8::MAX) {
            result[p] += 1;
            result.truncate(p + 1);
        } else {
            result.push(0);
        }
        result
    }

    fn name(&self) -> &'static str {
        "rldb.DefaultCmp"
    }
}

#[derive(Clone)]
pub struct InternalKeyCmp(pub Rc<dyn Cmp>);

impl Cmp for InternalKeyCmp {
    fn cmp(&self, a: &[u8], b: &[u8]) -> Ordering {
        // Ignore the tag
        match self.0.cmp(&a[..a.len() - 8], &b[..b.len() - 8]) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal => {
                let a_seqnum = parse_tag(FixedInt::decode_fixed(&a[a.len() - 8..]).unwrap()).1;
                let b_seqnum = parse_tag(FixedInt::decode_fixed(&b[b.len() - 8..]).unwrap()).1;
                b_seqnum.cmp(&a_seqnum)
            }
        }
    }

    fn find_shortest_separator(&self, a: &[u8], b: &[u8]) -> Vec<u8> {
        if a == b {
            return a.to_vec();
        }
        let (_, a_seqnum, a_key) = parse_internal_key(a);
        let b_key = parse_internal_key(b).2;

        let sep = self.0.find_shortest_separator(a_key, b_key);
        let seqnum = if sep.len() < a_key.len() && self.0.cmp(a_key, &sep) == Ordering::Less {
            MAX_SEQNUM
        } else {
            a_seqnum
        };
        LookupKey::new(&sep, seqnum).internal_key().to_vec()
    }

    fn find_shortest_successor(&self, a: &[u8]) -> Vec<u8> {
        let (_, seqnum, key) = parse_internal_key(a);
        let key = self.0.find_shortest_successor(key);
        LookupKey::new(&key, seqnum).internal_key().to_vec()
    }

    fn name(&self) -> &'static str {
        self.0.name()
    }
}

#[derive(Clone)]
pub struct MemtableKeyCmp(pub Rc<dyn Cmp>);

impl Cmp for MemtableKeyCmp {
    fn cmp(&self, a: &[u8], b: &[u8]) -> Ordering {
        let (a_len, a_offset) = usize::decode_var(&a).unwrap();
        let (b_len, b_offset) = usize::decode_var(&b).unwrap();

        let a_key = &a[a_offset..a_offset + a_len - 8];
        let b_key = &b[b_offset..b_offset + b_len - 8];
        let a_tag = &a[a_offset + a_len - 8..a_offset + a_len];
        let b_tag = &b[b_offset + b_len - 8..b_offset + b_len];

        match self.0.cmp(a_key, b_key) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal => {
                let a_seqnum = parse_tag(FixedInt::decode_fixed(a_tag).unwrap()).1;
                let b_seqnum = parse_tag(FixedInt::decode_fixed(b_tag).unwrap()).1;
                b_seqnum.cmp(&a_seqnum)
            }
        }
    }

    fn find_shortest_separator(&self, _a: &[u8], _b: &[u8]) -> Vec<u8> {
        unimplemented!()
    }

    fn find_shortest_successor(&self, _a: &[u8]) -> Vec<u8> {
        unimplemented!()
    }

    fn name(&self) -> &'static str {
        self.0.name()
    }
}

#[cfg(test)]
mod tests {
    use super::super::key::{build_memtable_key, ValueType};
    use super::*;

    mod tests_leveldb_rs {
        use super::*;

        #[test]
        fn test_cmp_defaultcmp_shortest_separator() {
            assert_eq!(
                DefaultCmp.find_shortest_separator("abcd".as_bytes(), "abcf".as_bytes()),
                "abce".as_bytes()
            );
            assert_eq!(
                DefaultCmp.find_shortest_separator("abc".as_bytes(), "acd".as_bytes()),
                "abd".as_bytes()
            );
            assert_eq!(
                DefaultCmp.find_shortest_separator("abcdefghi".as_bytes(), "abcffghi".as_bytes()),
                "abce".as_bytes()
            );
            assert_eq!(
                DefaultCmp.find_shortest_separator("a".as_bytes(), "a".as_bytes()),
                "a".as_bytes()
            );
            assert_eq!(
                DefaultCmp.find_shortest_separator("a".as_bytes(), "b".as_bytes()),
                "a\0".as_bytes()
            );
            assert_eq!(
                DefaultCmp.find_shortest_separator("abc".as_bytes(), "zzz".as_bytes()),
                "b".as_bytes()
            );
            assert_eq!(
                DefaultCmp.find_shortest_separator("yyy".as_bytes(), "z".as_bytes()),
                "yz".as_bytes()
            );
            assert_eq!(
                DefaultCmp.find_shortest_separator("".as_bytes(), "".as_bytes()),
                "".as_bytes()
            );
        }

        #[test]
        fn test_cmp_defaultcmp_short_successor() {
            assert_eq!(
                DefaultCmp.find_shortest_successor("abcd".as_bytes()),
                "b".as_bytes()
            );
            assert_eq!(
                DefaultCmp.find_shortest_successor("zzzz".as_bytes()),
                "{".as_bytes()
            );
            assert_eq!(DefaultCmp.find_shortest_successor(&[]), &[0]);
            assert_eq!(
                DefaultCmp.find_shortest_successor(&[0xff, 0xff, 0xff]),
                &[0xff, 0xff, 0xff, 0]
            );
        }

        #[test]
        fn test_cmp_internalkeycmp_shortest_sep() {
            let cmp = InternalKeyCmp(Rc::new(DefaultCmp));
            assert_eq!(
                cmp.find_shortest_separator(
                    LookupKey::new("abcd".as_bytes(), 1).internal_key(),
                    LookupKey::new("abcf".as_bytes(), 2).internal_key()
                ),
                LookupKey::new("abce".as_bytes(), 1).internal_key()
            );
            assert_eq!(
                cmp.find_shortest_separator(
                    LookupKey::new("abcd".as_bytes(), 1).internal_key(),
                    LookupKey::new("abce".as_bytes(), 2).internal_key()
                ),
                LookupKey::new("abcd\0".as_bytes(), 1).internal_key()
            );
            assert_eq!(
                cmp.find_shortest_separator(
                    LookupKey::new("abc".as_bytes(), 1).internal_key(),
                    LookupKey::new("zzz".as_bytes(), 2).internal_key()
                ),
                LookupKey::new("b".as_bytes(), MAX_SEQNUM).internal_key()
            );
            assert_eq!(
                cmp.find_shortest_separator(
                    LookupKey::new("abc".as_bytes(), 1).internal_key(),
                    LookupKey::new("acd".as_bytes(), 2).internal_key()
                ),
                LookupKey::new("abd".as_bytes(), 1).internal_key()
            );
            assert_eq!(
                cmp.find_shortest_separator(
                    LookupKey::new("abc".as_bytes(), 1).internal_key(),
                    LookupKey::new("abe".as_bytes(), 2).internal_key()
                ),
                LookupKey::new("abd".as_bytes(), 1).internal_key()
            );
            assert_eq!(
                cmp.find_shortest_separator(
                    LookupKey::new("".as_bytes(), 1).internal_key(),
                    LookupKey::new("".as_bytes(), 2).internal_key()
                ),
                LookupKey::new("".as_bytes(), 1).internal_key()
            );
            assert_eq!(
                cmp.find_shortest_separator(
                    LookupKey::new("abc".as_bytes(), 2).internal_key(),
                    LookupKey::new("abc".as_bytes(), 2).internal_key()
                ),
                LookupKey::new("abc".as_bytes(), 2).internal_key()
            );
        }

        #[test]
        fn test_cmp_internalkeycmp() {
            let cmp = InternalKeyCmp(Rc::new(DefaultCmp));
            // a < b < c
            let a = LookupKey::new("abc".as_bytes(), 2).internal_key().to_vec();
            let b = LookupKey::new("abc".as_bytes(), 1).internal_key().to_vec();
            let c = LookupKey::new("abd".as_bytes(), 3).internal_key().to_vec();
            let d = "xyy".as_bytes();
            let e = "xyz".as_bytes();

            assert_eq!(Ordering::Less, cmp.cmp(&a, &b));
            assert_eq!(Ordering::Equal, cmp.cmp(&a, &a));
            assert_eq!(Ordering::Greater, cmp.cmp(&b, &a));
            assert_eq!(Ordering::Less, cmp.cmp(&a, &c));
            assert_eq!(Ordering::Less, cmp.0.cmp(d, e));
            assert_eq!(Ordering::Greater, cmp.0.cmp(e, d));
        }

        #[test]
        #[should_panic]
        fn test_cmp_memtablekeycmp_panics() {
            let cmp = MemtableKeyCmp(Rc::new(DefaultCmp));
            cmp.cmp(&[1, 2, 3], &[4, 5, 6]);
        }
    }

    mod tests_gpt_4o {
        use super::*;

        #[test]
        fn test_default_cmp() {
            let cmp = DefaultCmp;

            // Test cmp
            assert_eq!(cmp.cmp(b"a", b"b"), Ordering::Less);
            assert_eq!(cmp.cmp(b"b", b"a"), Ordering::Greater);
            assert_eq!(cmp.cmp(b"a", b"a"), Ordering::Equal);

            // Test find_shortest_separator
            assert_eq!(
                cmp.find_shortest_separator(b"abc", b"abd"),
                b"abc\x00".to_vec()
            );
            assert_eq!(cmp.find_shortest_separator(b"abc", b"abc"), b"abc".to_vec());

            // Test find_shortest_successor
            assert_eq!(cmp.find_shortest_successor(b"abc"), b"b".to_vec());
            assert_eq!(
                cmp.find_shortest_successor(b"\xff\xff"),
                b"\xff\xff\x00".to_vec()
            );

            // Test name
            assert_eq!(cmp.name(), "rldb.DefaultCmp");
        }

        #[test]
        fn test_internal_key_cmp() {
            let cmp = InternalKeyCmp(Rc::new(DefaultCmp));

            // Create internal keys
            let key1 = LookupKey::new(b"key1", 1);
            let key2 = LookupKey::new(b"key2", 2);
            let key1_with_high_seqnum = LookupKey::new(b"key1", 3);

            // Test cmp
            assert_eq!(
                cmp.cmp(key1.internal_key(), key2.internal_key()),
                Ordering::Less
            );
            assert_eq!(
                cmp.cmp(key2.internal_key(), key1.internal_key()),
                Ordering::Greater
            );
            assert_eq!(
                cmp.cmp(key1.internal_key(), key1_with_high_seqnum.internal_key()),
                Ordering::Greater
            );
            assert_eq!(
                cmp.cmp(key1_with_high_seqnum.internal_key(), key1.internal_key()),
                Ordering::Less
            );
            assert_eq!(
                cmp.cmp(key1.internal_key(), key1.internal_key()),
                Ordering::Equal
            );

            // Test find_shortest_separator
            let sep = cmp.find_shortest_separator(key1.internal_key(), key2.internal_key());
            assert_eq!(parse_internal_key(&sep).2, b"key1\x00");

            // Test find_shortest_successor
            let suc = cmp.find_shortest_successor(key1.internal_key());
            assert_eq!(parse_internal_key(&suc).2, b"l");

            // Test name
            assert_eq!(cmp.name(), "rldb.DefaultCmp");
        }

        #[test]
        fn test_memtable_key_cmp() {
            let cmp = MemtableKeyCmp(Rc::new(DefaultCmp));

            // Create memtable keys
            let key1 = build_memtable_key(b"key1", b"value1", ValueType::TypeValue, 1);
            let key2 = build_memtable_key(b"key2", b"value2", ValueType::TypeValue, 2);
            let key1_with_high_seqnum =
                build_memtable_key(b"key1", b"value1", ValueType::TypeValue, 3);

            // Test cmp
            assert_eq!(cmp.cmp(&key1, &key2), Ordering::Less);
            assert_eq!(cmp.cmp(&key2, &key1), Ordering::Greater);
            assert_eq!(cmp.cmp(&key1, &key1_with_high_seqnum), Ordering::Greater);
            assert_eq!(cmp.cmp(&key1_with_high_seqnum, &key1), Ordering::Less);
            assert_eq!(cmp.cmp(&key1, &key1), Ordering::Equal);

            // Test name
            assert_eq!(cmp.name(), "rldb.DefaultCmp");
        }
    }
}
