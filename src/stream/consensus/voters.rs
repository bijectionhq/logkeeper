//! A stream's voter roster: three or five keepers, fixed when the stream is
//! created.
//!
//! # Encoding
//!
//! Geneses, stages, configurations and placement proofs carry a roster on
//! the wire, in the WAL, in checkpoints and in snapshot images. A roster of
//! three encodes exactly as the `[Uuid; 3]` it replaced: a bincode tuple of
//! three length-prefixed 16-byte strings. A roster of five keeps the
//! three-element tuple and packs its keepers as byte strings of 32, 32 and
//! 16 bytes. A reader tells the two apart by the first length, and a build
//! that only knows three-voter rosters refuses a five-voter one as an
//! invalid UUID instead of misreading it. Five-voter rosters are written
//! only once the cluster finalized `CLUSTER_VERSION_REPLICATION`, so no
//! keeper that cannot read them is left (`decisions::creates_replication`).
//!
//! Human-readable formats (JSON configuration and reports) see a plain list
//! of UUIDs.

use std::{fmt, ops::Deref};

use serde::{
    Deserialize, Deserializer, Serialize, Serializer,
    de::{self, SeqAccess, Visitor},
    ser::SerializeTuple,
};
use uuid::Uuid;

use super::decisions;

/// The largest roster a stream may have.
pub const MAX_VOTERS: usize = 5;

/// A stream's voters. The roster holds three or five keepers; the slots past
/// its length are nil, so derived comparisons only see the roster itself.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Voters {
    ids: [Uuid; MAX_VOTERS],
    len: u8,
}

impl Voters {
    /// The roster `ids` in the given order, or `None` unless it names three
    /// or five keepers.
    pub fn new(ids: &[Uuid]) -> Option<Self> {
        if !decisions::replication_factor(ids.len()) {
            return None;
        }
        let mut slots = [Uuid::nil(); MAX_VOTERS];
        slots[..ids.len()].copy_from_slice(ids);
        Some(Self {
            ids: slots,
            len: ids.len() as u8,
        })
    }

    /// The roster `ids`, sorted.
    pub fn sorted(ids: &[Uuid]) -> Option<Self> {
        let mut voters = Self::new(ids)?;
        voters.sort();
        Some(voters)
    }

    fn sort(&mut self) {
        self.ids[..usize::from(self.len)].sort_unstable();
    }

    /// Sorts the roster in place.
    pub fn sort_unstable(&mut self) {
        self.sort();
    }

    /// Each voter mapped through `f`, in roster order.
    pub fn map<T>(self, f: impl FnMut(Uuid) -> T) -> Vec<T> {
        self.into_iter().map(f).collect()
    }

    /// This roster sorted.
    pub fn into_sorted(mut self) -> Self {
        self.sort();
        self
    }

    pub fn as_slice(&self) -> &[Uuid] {
        &self.ids[..usize::from(self.len)]
    }

    /// Votes that commit an entry or elect a leader: a majority.
    pub fn quorum(&self) -> usize {
        decisions::quorum(self.len())
    }

    /// Voters the stream may lose and still commit.
    pub fn tolerated(&self) -> usize {
        self.len() - self.quorum()
    }

    /// Whether the roster is strictly ascending, which also makes it
    /// duplicate free.
    pub fn ascending(&self) -> bool {
        self.windows(2).all(|pair| pair[0] < pair[1])
    }

    /// Whether every pre-replication-factor build can read this roster.
    pub fn legacy(&self) -> bool {
        self.len == 3
    }

    /// The roster with `leaving` replaced by `joining`, sorted.
    pub fn replacing(&self, leaving: Uuid, joining: Uuid) -> Self {
        let mut next = *self;
        for id in &mut next.ids[..usize::from(self.len)] {
            if *id == leaving {
                *id = joining;
            }
        }
        next.into_sorted()
    }

    pub fn to_u128(&self) -> Vec<u128> {
        self.iter().map(|id| id.as_u128()).collect()
    }
}

impl Deref for Voters {
    type Target = [Uuid];

    fn deref(&self) -> &[Uuid] {
        self.as_slice()
    }
}

impl fmt::Debug for Voters {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.as_slice()).finish()
    }
}

impl From<[Uuid; 3]> for Voters {
    fn from(ids: [Uuid; 3]) -> Self {
        Self::new(&ids).expect("three voters")
    }
}

impl From<[Uuid; 5]> for Voters {
    fn from(ids: [Uuid; 5]) -> Self {
        Self::new(&ids).expect("five voters")
    }
}

impl TryFrom<&[Uuid]> for Voters {
    type Error = ();

    fn try_from(ids: &[Uuid]) -> Result<Self, ()> {
        Self::new(ids).ok_or(())
    }
}

impl TryFrom<Vec<Uuid>> for Voters {
    type Error = ();

    fn try_from(ids: Vec<Uuid>) -> Result<Self, ()> {
        Self::new(&ids).ok_or(())
    }
}

impl<const N: usize> PartialEq<[Uuid; N]> for Voters {
    fn eq(&self, other: &[Uuid; N]) -> bool {
        self.as_slice() == other
    }
}

impl IntoIterator for Voters {
    type Item = Uuid;
    type IntoIter = std::iter::Take<std::array::IntoIter<Uuid, MAX_VOTERS>>;

    fn into_iter(self) -> Self::IntoIter {
        self.ids.into_iter().take(usize::from(self.len))
    }
}

impl<'a> IntoIterator for &'a Voters {
    type Item = &'a Uuid;
    type IntoIter = std::slice::Iter<'a, Uuid>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

/// A byte string, serialized the way `Uuid` serializes its 16 bytes.
struct Raw<'a>(&'a [u8]);

impl Serialize for Raw<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(self.0)
    }
}

struct Owned(Vec<u8>);

impl<'de> Deserialize<'de> for Owned {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct Bytes;
        impl<'de> Visitor<'de> for Bytes {
            type Value = Owned;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("a packed voter byte string")
            }
            fn visit_bytes<E: de::Error>(self, bytes: &[u8]) -> Result<Owned, E> {
                Ok(Owned(bytes.to_vec()))
            }
            fn visit_byte_buf<E: de::Error>(self, bytes: Vec<u8>) -> Result<Owned, E> {
                Ok(Owned(bytes))
            }
        }
        deserializer.deserialize_bytes(Bytes)
    }
}

impl Serialize for Voters {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if serializer.is_human_readable() {
            return serializer.collect_seq(self.as_slice());
        }
        let mut packed = [[0; 32]; 2];
        let parts: [&[u8]; 3] = match self.as_slice() {
            [a, b, c] => [a.as_bytes(), b.as_bytes(), c.as_bytes()],
            [a, b, c, d, e] => {
                packed[0][..16].copy_from_slice(a.as_bytes());
                packed[0][16..].copy_from_slice(b.as_bytes());
                packed[1][..16].copy_from_slice(c.as_bytes());
                packed[1][16..].copy_from_slice(d.as_bytes());
                let [first, second] = &packed;
                [first, second, e.as_bytes()]
            }
            _ => unreachable!("a roster holds three or five voters"),
        };
        let mut tuple = serializer.serialize_tuple(3)?;
        for part in parts {
            tuple.serialize_element(&Raw(part))?;
        }
        tuple.end()
    }
}

impl<'de> Deserialize<'de> for Voters {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        if deserializer.is_human_readable() {
            let ids = Vec::<Uuid>::deserialize(deserializer)?;
            return Self::new(&ids)
                .ok_or_else(|| de::Error::custom("a stream has three or five voters"));
        }
        struct Packed;
        impl<'de> Visitor<'de> for Packed {
            type Value = Voters;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("three or five packed voters")
            }
            fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Voters, A::Error> {
                let mut parts = Vec::with_capacity(3);
                for index in 0..3 {
                    let Owned(bytes) = seq
                        .next_element()?
                        .ok_or_else(|| de::Error::invalid_length(index, &self))?;
                    parts.push(bytes);
                }
                let lengths = parts.iter().map(Vec::len).collect::<Vec<_>>();
                if lengths != [16, 16, 16] && lengths != [32, 32, 16] {
                    return Err(de::Error::custom("invalid packed voter roster"));
                }
                let ids = parts
                    .iter()
                    .flat_map(|part| part.chunks_exact(16))
                    .map(|id| Uuid::from_slice(id).expect("16 bytes"))
                    .collect::<Vec<_>>();
                Voters::new(&ids).ok_or_else(|| de::Error::custom("invalid packed voter roster"))
            }
        }
        deserializer.deserialize_tuple(3, Packed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stream::consensus::{decode, encode};

    fn ids(count: u128) -> Vec<Uuid> {
        (1..=count)
            .map(|id| Uuid::from_u128(id << 64 | id))
            .collect()
    }

    #[test]
    fn three_voters_keep_the_fixed_array_encoding() {
        let three: [Uuid; 3] = ids(3).try_into().unwrap();
        let voters = Voters::from(three);
        assert_eq!(encode(&voters).unwrap(), encode(&three).unwrap());
        assert_eq!(decode::<Voters>(&encode(&three).unwrap()).unwrap(), voters);
        assert_eq!(
            serde_json::to_string(&voters).unwrap(),
            serde_json::to_string(&three).unwrap()
        );
    }

    #[test]
    fn five_voters_round_trip_and_an_old_reader_refuses_them() {
        let five: [Uuid; 5] = ids(5).try_into().unwrap();
        let voters = Voters::from(five);
        let bytes = encode(&voters).unwrap();
        assert_eq!(bytes.len(), 3 * 8 + 5 * 16);
        assert_eq!(decode::<Voters>(&bytes).unwrap(), voters);
        assert!(decode::<[Uuid; 3]>(&bytes).is_err());
        let json = serde_json::to_string(&voters).unwrap();
        assert_eq!(serde_json::from_str::<Voters>(&json).unwrap(), voters);
        assert_eq!(voters.quorum(), 3);
        assert_eq!(voters.tolerated(), 2);
    }

    #[test]
    fn only_three_or_five_voters_form_a_roster() {
        for count in [0, 1, 2, 4, 6] {
            assert!(Voters::new(&ids(count)).is_none());
        }
        assert!(
            serde_json::from_str::<Voters>(r#"["00000000-0000-0000-0000-000000000001"]"#).is_err()
        );
        // Packed lengths that are neither layout.
        let mut bytes = encode(&Voters::from(<[Uuid; 5]>::try_from(ids(5)).unwrap())).unwrap();
        bytes[8 + 32] = 16;
        assert!(decode::<Voters>(&bytes).is_err());
    }
}
