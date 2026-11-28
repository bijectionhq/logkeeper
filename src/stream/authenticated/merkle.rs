//! Append-only Merkle trees over one stream's committed records.
//!
//! The tree shape and hashing follow RFC 6962: a leaf hash is domain separated by
//! its leaf type and a parent hash is `SHA-256(1 || left || right)`, splitting at
//! the largest power of two strictly below the size. Both the consensus keeper
//! and the writer-driven keepers use this module with their own leaf types.

use journal_contract::{Lsn, StreamId};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use sha2::{Digest, Sha256};

use super::{Hash, ProofError};

/// One committed record's authenticated metadata.
pub trait MerkleLeaf: Copy {
    fn stream(&self) -> StreamId;
    fn at(&self) -> Lsn;
    fn valid(&self) -> bool;
    fn hash(&self) -> Hash;
}

/// Append-only Merkle tree indexed by one-based journal positions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Tree<L> {
    leaves: Vec<L>,
    // Level h holds every complete, aligned subtree of 2^h leaves.
    levels: Vec<Vec<Hash>>,
}

impl<L> Default for Tree<L> {
    fn default() -> Self {
        Self {
            leaves: Vec::new(),
            levels: Vec::new(),
        }
    }
}

impl<L: MerkleLeaf> Tree<L> {
    pub fn append(&mut self, leaf: L) -> Result<(), ProofError> {
        Self::check_append(&leaf, self.size() + 1, self.stream())?;
        self.insert(leaf);
        Ok(())
    }

    pub fn extend(&mut self, leaves: impl IntoIterator<Item = L>) -> Result<(), ProofError> {
        let leaves: Vec<_> = leaves.into_iter().collect();
        let stream = self
            .stream()
            .or_else(|| leaves.first().map(|leaf| leaf.stream()));
        for (index, leaf) in leaves.iter().enumerate() {
            let at = self.size() + index as u64 + 1;
            Self::check_append(leaf, at, stream)?;
        }
        for leaf in leaves {
            self.insert(leaf);
        }
        Ok(())
    }

    fn check_append(leaf: &L, at: u64, stream: Option<StreamId>) -> Result<(), ProofError> {
        if !leaf.valid() || stream.is_some_and(|expected| expected != leaf.stream()) {
            return Err(ProofError::Leaf);
        }
        if leaf.at().0 != at {
            return Err(ProofError::Position);
        }
        Ok(())
    }

    fn insert(&mut self, leaf: L) {
        let mut hash = leaf.hash();
        self.leaves.push(leaf);
        let mut nodes = self.leaves.len();
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

    pub fn leaves(&self) -> &[L] {
        &self.leaves
    }

    pub fn leaf(&self, at: Lsn) -> Option<&L> {
        let index = usize::try_from(at.0.checked_sub(1)?).ok()?;
        self.leaves.get(index)
    }

    pub fn stream(&self) -> Option<StreamId> {
        self.leaves.first().map(|leaf| leaf.stream())
    }

    pub fn size(&self) -> u64 {
        self.leaves.len() as u64
    }

    pub fn empty_root() -> Hash {
        empty_root()
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
        prefix.extend(self.leaves[..size as usize].iter().copied())?;
        Ok(prefix)
    }

    fn root_range(&self, start: u64, size: u64) -> Hash {
        if size == 0 {
            return empty_root();
        }
        if size.is_power_of_two() {
            let height = size.trailing_zeros();
            return self.levels[height as usize][(start >> height) as usize];
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

impl<L: MerkleLeaf + Serialize> Serialize for Tree<L> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.leaves.serialize(serializer)
    }
}

impl<'de, L: MerkleLeaf + Deserialize<'de>> Deserialize<'de> for Tree<L> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let leaves = Vec::<L>::deserialize(deserializer)?;
        let mut tree = Self::default();
        tree.extend(leaves).map_err(serde::de::Error::custom)?;
        Ok(tree)
    }
}

/// The right edge of a tree: the roots of its maximal complete subtrees, largest
/// first. It extends the tree and computes its root without the leaves.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Frontier {
    size: u64,
    // (height, root) of each maximal aligned subtree, in decreasing height.
    peaks: Vec<(u32, Hash)>,
}

impl Frontier {
    pub fn size(&self) -> u64 {
        self.size
    }

    pub fn push(&mut self, leaf: Hash) {
        let mut node = (0, leaf);
        while let Some(&(height, left)) = self.peaks.last() {
            if height != node.0 {
                break;
            }
            self.peaks.pop();
            node = (height + 1, parent(left, node.1));
        }
        self.peaks.push(node);
        self.size += 1;
    }

    /// The tree root, `parent(p0, parent(p1, ... pn))` over the peaks, which is
    /// the same split rule as `Tree::root`.
    pub fn root(&self) -> Hash {
        let mut peaks = self.peaks.iter().rev();
        let Some(&(_, mut root)) = peaks.next() else {
            return empty_root();
        };
        for &(_, left) in peaks {
            root = parent(left, root);
        }
        root
    }
}

pub fn empty_root() -> Hash {
    Sha256::digest([]).into()
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

pub fn verify_inclusion(
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

pub fn verify_consistency(
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
        return if earlier == empty_root() && path.is_empty() {
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
