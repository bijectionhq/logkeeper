// Foreign representations and operations at the verification boundary.
use crate::ordered::{Checkpoint, Cut, Enrollment, Fingerprint, Placement, Receipt, Refusal, RequestId};
use std::io;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Uuid {
    pub bytes: [u8; 16],
}

impl Uuid {
    pub fn as_bytes(&self) -> (out: &[u8; 16])
        ensures *out == self.bytes,
    { &self.bytes }
}

pub struct Bytes {
    pub contents: Ghost<Seq<u8>>,
}
pub struct BytesMut {
    pub contents: Ghost<Seq<u8>>,
}

impl View for Bytes {
    type V = Seq<u8>;
    open spec fn view(&self) -> Seq<u8> { self.contents@ }
}

impl View for BytesMut {
    type V = Seq<u8>;
    open spec fn view(&self) -> Seq<u8> { self.contents@ }
}

pub open spec fn be64(value: u64) -> Seq<u8> {
    vstd::bytes::spec_u64_to_le_bytes(value).reverse()
}

impl Bytes {
    pub fn is_empty(&self) -> (out: bool)
        ensures out == (self@.len() == 0),
    {
        self.as_ref().is_empty()
    }

    #[verifier::external_body]
    pub fn as_ref(&self) -> (out: &[u8])
        ensures out@ == self@,
    { unimplemented!() }
}

// The normalization proof does not require an interpretation of decoded fields.
pub struct Input(pub Bytes);

impl Input {
    #[verifier::external_body]
    pub fn take<const N: usize>(&mut self) -> Result<[u8; N], Refusal> { unimplemented!() }

    #[verifier::external_body]
    pub fn placement(&mut self) -> Result<Placement, Refusal> { unimplemented!() }

    #[verifier::external_body]
    pub fn enrollment(&mut self) -> Result<Enrollment, Refusal> { unimplemented!() }

    #[verifier::external_body]
    pub fn request_id(&mut self) -> Result<RequestId, Refusal> { unimplemented!() }

    #[verifier::external_body]
    pub fn u64(&mut self) -> Result<u64, Refusal> { unimplemented!() }

    #[verifier::external_body]
    pub fn checkpoint(&mut self) -> Result<Checkpoint, Refusal> { unimplemented!() }

    #[verifier::external_body]
    pub fn cut(&mut self) -> Result<Cut, Refusal> { unimplemented!() }
}

pub trait BufMut: View<V = Seq<u8>> {
    fn put_slice(&mut self, bytes: &[u8])
        ensures final(self)@ == old(self)@ + bytes@;
    fn put_u64(&mut self, value: u64)
        ensures final(self)@ == old(self)@ + be64(value);
}

impl BytesMut {
    pub fn new() -> (out: Self)
        ensures out@ == Seq::<u8>::empty(),
    { BytesMut { contents: Ghost(Seq::empty()) } }

    pub fn freeze(self) -> (out: Bytes)
        ensures out@ == self@,
    { Bytes { contents: self.contents } }
}

impl BufMut for BytesMut {
    fn put_slice(&mut self, bytes: &[u8]) {
        self.contents = Ghost(self@ + bytes@);
    }

    fn put_u64(&mut self, value: u64) {
        self.contents = Ghost(self@ + be64(value));
    }
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct IoError(std::io::Error);

pub struct Sha256;
pub trait Digest {
    fn digest(key: &Fingerprint) -> (out: Fingerprint)
        ensures out == fingerprint(*key);
}
pub uninterp spec fn fingerprint(key: Fingerprint) -> Fingerprint;

impl Digest for Sha256 {
    #[verifier::external_body]
    fn digest(key: &Fingerprint) -> Fingerprint {
        unimplemented!()
    }
}

pub uninterp spec fn signed_message(key: Fingerprint, signature: Seq<u8>) -> Option<Seq<u8>>;

#[verifier::external_body]
pub fn verify_bytes(key: &Fingerprint, bytes: &[u8], signature: &[u8]) -> (out: io::Result<()>)
    ensures (out is Ok) == (signed_message(*key, signature@) == Some(bytes@)),
{ unimplemented!() }

#[verifier::external_body]
pub fn invalid(message: &'static str) -> io::Error {
    unimplemented!()
}

pub uninterp spec fn receipt_bytes(decision: Receipt) -> Seq<u8>;

#[verifier::external_body]
pub fn receipt(output: &mut BytesMut, decision: Receipt)
    ensures final(output)@ == old(output)@ + receipt_bytes(decision),
{ unimplemented!() }

pub struct BTreeMap<K, V> {
    pub entries: Ghost<Map<K, V>>,
}

impl<K, V> View for BTreeMap<K, V> {
    type V = Map<K, V>;
    open spec fn view(&self) -> Map<K, V> { self.entries@ }
}

impl<K, V> BTreeMap<K, V> {
    #[verifier::external_body]
    pub fn get(&self, key: &K) -> (out: Option<&V>)
        ensures
            (out is Some) == self@.contains_key(*key),
            out matches Some(value) ==> *value == self@[*key],
    { unimplemented!() }
}

// The native map's iterator exposes its values, then copies and collects them.
pub struct Values<V> {
    pub values: Ghost<Set<V>>,
}

impl<K, V> BTreeMap<K, V> {
    pub fn values(&self) -> (out: Values<V>)
        ensures out.values@ == self@.values(),
    { Values { values: Ghost(self@.values()) } }
}

impl<V: Copy> Values<V> {
    pub fn copied(self) -> (out: Self)
        ensures out.values@ == self.values@,
    { self }

    pub fn collect(self) -> (out: BTreeSet<V>)
        ensures out@ == self.values@,
    { BTreeSet { keys: self.values } }
}

pub struct BTreeSet<K> {
    pub keys: Ghost<Set<K>>,
}

impl<K> View for BTreeSet<K> {
    type V = Set<K>;
    open spec fn view(&self) -> Set<K> { self.keys@ }
}

impl<K> BTreeSet<K> {
    #[verifier::external_body]
    pub fn extend(&mut self, keys: &Vec<K>)
        ensures final(self)@ == old(self)@.union(keys@.to_set()),
    { unimplemented!() }

    #[verifier::external_body]
    pub fn contains(&self, key: &K) -> (out: bool)
        ensures out == self@.contains(*key),
    { unimplemented!() }

    #[verifier::external_body]
    pub fn is_subset(&self, other: &Self) -> (out: bool)
        ensures out == self@.subset_of(other@),
    { unimplemented!() }
}

}
