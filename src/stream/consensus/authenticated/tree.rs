use std::sync::Arc;

use journal_contract::{Lsn, StreamId};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use sha2::{Digest, Sha256};

use super::{Hash, Leaf, ProofError};

/// Leaves per page. A tree and its snapshot share pages of this size.
pub const PAGE: usize = 256;

/// Append-only Merkle tree indexed by one-based journal positions.
///
/// Leaves live in immutable pages shared between clones, each with its
/// subtree root, so a clone copies page pointers and a proof hashes at most
/// one page's leaves.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Tree {
    pages: Vec<Page>,
    // Level h holds the root of every complete, aligned run of 2^h pages.
    levels: Vec<Vec<Hash>>,
    tail: Vec<Leaf>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Page {
    leaves: Arc<[Leaf]>,
}

impl Tree {
    pub fn append(&mut self, leaf: Leaf) -> Result<(), ProofError> {
        Self::check_append(&leaf, self.size() + 1, self.stream())?;
        self.insert(leaf);
        Ok(())
    }

    pub fn extend(&mut self, leaves: impl IntoIterator<Item = Leaf>) -> Result<(), ProofError> {
        let leaves: Vec<_> = leaves.into_iter().collect();
        let stream = self
            .stream()
            .or_else(|| leaves.first().map(|leaf| leaf.stream));
        for (index, leaf) in leaves.iter().enumerate() {
            let at = self.size() + index as u64 + 1;
            Self::check_append(leaf, at, stream)?;
        }
        for leaf in leaves {
            self.insert(leaf);
        }
        Ok(())
    }

    fn check_append(leaf: &Leaf, at: u64, stream: Option<StreamId>) -> Result<(), ProofError> {
        if !leaf.valid() || stream.is_some_and(|expected| expected != leaf.stream) {
            return Err(ProofError::Leaf);
        }
        if leaf.at.0 != at {
            return Err(ProofError::Position);
        }
        Ok(())
    }

    fn insert(&mut self, leaf: Leaf) {
        self.tail.push(leaf);
        if self.tail.len() < PAGE {
            return;
        }
        let leaves: Arc<[Leaf]> = std::mem::take(&mut self.tail).into();
        let mut hash = leaves_root(&leaves);
        self.pages.push(Page { leaves });
        let mut nodes = self.pages.len();
        let mut height = 0;
        loop {
            if height == self.levels.len() {
                self.levels.push(Vec::new());
            }
            let level = &mut self.levels[height];
            level.push(hash);
            if nodes % 2 == 1 {
                return;
            }
            hash = parent(level[level.len() - 2], hash);
            nodes /= 2;
            height += 1;
        }
    }

    /// Every leaf in position order.
    pub fn leaves(&self) -> impl Iterator<Item = &Leaf> {
        self.pages().flatten()
    }

    /// Leaves in pages of [`PAGE`], the last possibly partial.
    pub fn pages(&self) -> impl Iterator<Item = &[Leaf]> {
        self.pages
            .iter()
            .map(|page| &page.leaves[..])
            .chain(Some(&self.tail[..]).filter(|tail| !tail.is_empty()))
    }

    /// The leaves at zero-based indexes `start..end`.
    pub fn leaf_range(&self, start: u64, end: u64) -> Vec<Leaf> {
        (start..end.min(self.size()))
            .filter_map(|index| self.leaf_at(index).copied())
            .collect()
    }

    fn leaf_at(&self, index: u64) -> Option<&Leaf> {
        let page = usize::try_from(index / PAGE as u64).ok()?;
        let offset = (index % PAGE as u64) as usize;
        match self.pages.get(page) {
            Some(page) => page.leaves.get(offset),
            None if page == self.pages.len() => self.tail.get(offset),
            None => None,
        }
    }

    pub fn leaf(&self, at: Lsn) -> Option<&Leaf> {
        self.leaf_at(at.0.checked_sub(1)?)
    }

    pub fn stream(&self) -> Option<StreamId> {
        self.leaf_at(0).map(|leaf| leaf.stream)
    }

    pub fn size(&self) -> u64 {
        (self.pages.len() * PAGE + self.tail.len()) as u64
    }

    pub fn empty_root() -> Hash {
        Sha256::digest([]).into()
    }

    pub fn root(&self) -> Hash {
        self.root_range(0, self.size())
    }

    pub fn root_at(&self, size: u64) -> Result<Hash, ProofError> {
        if size > self.size() {
            return Err(ProofError::Position);
        }
        Ok(self.root_range(0, size))
    }

    pub fn prefix(&self, size: u64) -> Result<Self, ProofError> {
        if size > self.size() {
            return Err(ProofError::Position);
        }
        let mut prefix = Self::default();
        prefix.extend(self.leaves().take(size as usize).copied())?;
        Ok(prefix)
    }

    fn root_range(&self, start: u64, size: u64) -> Hash {
        if size == 0 {
            return Self::empty_root();
        }
        let page = PAGE as u64;
        if size.is_power_of_two() && size >= page && start % size == 0 {
            let height = (size / page).trailing_zeros() as usize;
            return self.levels[height][(start / size) as usize];
        }
        if size <= page && start / page == (start + size - 1) / page {
            let leaves = self.leaf_range(start, start + size);
            return leaves_root(&leaves);
        }
        let split = split(size);
        parent(
            self.root_range(start, split),
            self.root_range(start + split, size - split),
        )
    }

    pub fn inclusion(&self, at: Lsn, size: u64) -> Result<Vec<Hash>, ProofError> {
        if at.0 == 0 || at.0 > size || size > self.size() {
            return Err(ProofError::Position);
        }
        let mut path = Vec::new();
        self.inclusion_path(0, at.0 - 1, size, &mut path);
        Ok(path)
    }

    fn inclusion_path(&self, start: u64, index: u64, size: u64, path: &mut Vec<Hash>) {
        if size == 1 {
            return;
        }
        let split = split(size);
        if index < split {
            self.inclusion_path(start, index, split, path);
            path.push(self.root_range(start + split, size - split));
        } else {
            self.inclusion_path(start + split, index - split, size - split, path);
            path.push(self.root_range(start, split));
        }
    }

    pub fn consistency(&self, earlier_size: u64, later_size: u64) -> Result<Vec<Hash>, ProofError> {
        if earlier_size > later_size || later_size > self.size() {
            return Err(ProofError::Position);
        }
        let mut path = Vec::new();
        if earlier_size != 0 {
            self.consistency_path(0, earlier_size, later_size, true, &mut path);
        }
        Ok(path)
    }

    fn consistency_path(
        &self,
        start: u64,
        earlier: u64,
        size: u64,
        known: bool,
        path: &mut Vec<Hash>,
    ) {
        if earlier == size {
            if !known {
                path.push(self.root_range(start, size));
            }
            return;
        }
        let split = split(size);
        if earlier <= split {
            self.consistency_path(start, earlier, split, known, path);
            path.push(self.root_range(start + split, size - split));
        } else {
            self.consistency_path(start + split, earlier - split, size - split, false, path);
            path.push(self.root_range(start, split));
        }
    }
}

impl Serialize for Tree {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeSeq;
        let mut sequence = serializer.serialize_seq(Some(self.size() as usize))?;
        for leaf in self.leaves() {
            sequence.serialize_element(leaf)?;
        }
        sequence.end()
    }
}

impl<'de> Deserialize<'de> for Tree {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let leaves = Vec::<Leaf>::deserialize(deserializer)?;
        let mut tree = Self::default();
        tree.extend(leaves).map_err(serde::de::Error::custom)?;
        Ok(tree)
    }
}

/// The Merkle root of a contiguous run of leaves.
fn leaves_root(leaves: &[Leaf]) -> Hash {
    match leaves {
        [] => Tree::empty_root(),
        [leaf] => leaf.hash(),
        _ => {
            let (left, right) = leaves.split_at(split(leaves.len() as u64) as usize);
            parent(leaves_root(left), leaves_root(right))
        }
    }
}

fn parent(left: Hash, right: Hash) -> Hash {
    let mut digest = Sha256::new();
    digest.update([1]);
    digest.update(left);
    digest.update(right);
    digest.finalize().into()
}

// The largest power of two strictly smaller than size.
fn split(size: u64) -> u64 {
    1 << (size - 1).ilog2()
}

pub(super) fn verify_inclusion(
    at: Lsn,
    leaf: Hash,
    size: u64,
    expected: Hash,
    path: &[Hash],
) -> Result<(), ProofError> {
    if at.0 == 0 || at.0 > size {
        return Err(ProofError::Position);
    }
    let mut path = path.iter().copied();
    let root = inclusion_root(&mut path, at.0 - 1, size, leaf)?;
    if root != expected || path.next().is_some() {
        return Err(ProofError::Path);
    }
    Ok(())
}

fn inclusion_root(
    path: &mut impl Iterator<Item = Hash>,
    index: u64,
    size: u64,
    leaf: Hash,
) -> Result<Hash, ProofError> {
    if size == 1 {
        return Ok(leaf);
    }
    let split = split(size);
    if index < split {
        let left = inclusion_root(path, index, split, leaf)?;
        Ok(parent(left, path.next().ok_or(ProofError::Path)?))
    } else {
        let right = inclusion_root(path, index - split, size - split, leaf)?;
        Ok(parent(path.next().ok_or(ProofError::Path)?, right))
    }
}

pub(super) fn verify_consistency(
    earlier_size: u64,
    later_size: u64,
    earlier: Hash,
    later: Hash,
    path: &[Hash],
) -> Result<(), ProofError> {
    if earlier_size > later_size {
        return Err(ProofError::Position);
    }
    if earlier_size == 0 {
        return if earlier == Tree::empty_root() && path.is_empty() {
            Ok(())
        } else {
            Err(ProofError::Path)
        };
    }
    let mut path = path.iter().copied();
    let roots = consistency_roots(&mut path, earlier_size, later_size, Some(earlier))?;
    if roots != (earlier, later) || path.next().is_some() {
        return Err(ProofError::Path);
    }
    Ok(())
}

fn consistency_roots(
    path: &mut impl Iterator<Item = Hash>,
    earlier: u64,
    size: u64,
    known: Option<Hash>,
) -> Result<(Hash, Hash), ProofError> {
    if earlier == size {
        let root = known.or_else(|| path.next()).ok_or(ProofError::Path)?;
        return Ok((root, root));
    }
    let split = split(size);
    if earlier <= split {
        let (earlier, left) = consistency_roots(path, earlier, split, known)?;
        let right = path.next().ok_or(ProofError::Path)?;
        Ok((earlier, parent(left, right)))
    } else {
        let (before, after) = consistency_roots(path, earlier - split, size - split, None)?;
        let left = path.next().ok_or(ProofError::Path)?;
        Ok((parent(left, before), parent(left, after)))
    }
}
