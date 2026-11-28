//! The framed archive format shared by consensus and writer-driven archives:
//! an 8-byte magic, bincode items with per-item size limits, then the tree's
//! leaves one at a time, and no trailing bytes. Each archive type chooses its
//! magic and its header items. An archive is read in full and must be verified
//! against its trust root before its proofs are used.

use std::io::{self, Read, Write};

use bincode::Options;
use serde::{Serialize, de::DeserializeOwned};

use super::{
    Archive, SignedHead,
    merkle::{MerkleLeaf, Tree},
};

/// Largest single header item, matching the consensus wire message limit.
pub(crate) const MAX_ITEM_BYTES: u64 = 32 * 1024 * 1024;
const MAGIC: &[u8; 8] = b"LKSARCH1";
const MAX_LEAF_BYTES: u64 = 256;

fn options() -> impl Options {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .reject_trailing_bytes()
}

pub(crate) fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

pub(crate) struct ArchiveWriter<'a, W: Write>(&'a mut W);

impl<'a, W: Write> ArchiveWriter<'a, W> {
    pub(crate) fn start(file: &'a mut W, magic: &[u8; 8]) -> io::Result<Self> {
        file.write_all(magic)?;
        Ok(Self(file))
    }

    pub(crate) fn item(&mut self, item: &impl Serialize) -> io::Result<()> {
        options()
            .serialize_into(&mut *self.0, item)
            .map_err(io::Error::other)
    }

    pub(crate) fn leaves<L: MerkleLeaf + Serialize>(&mut self, tree: &Tree<L>) -> io::Result<()> {
        for leaf in tree.leaves() {
            self.item(leaf)?;
        }
        Ok(())
    }
}

pub(crate) struct ArchiveReader<'a, R: Read>(&'a mut R);

impl<'a, R: Read> ArchiveReader<'a, R> {
    pub(crate) fn start(file: &'a mut R, magic: &[u8; 8], format: &str) -> io::Result<Self> {
        let mut found = [0; 8];
        file.read_exact(&mut found)?;
        if &found != magic {
            return Err(invalid(format));
        }
        Ok(Self(file))
    }

    pub(crate) fn item<T: DeserializeOwned>(&mut self, limit: u64) -> io::Result<T> {
        options()
            .with_limit(limit)
            .deserialize_from(&mut *self.0)
            .map_err(io::Error::other)
    }

    /// Reads exactly `size` leaves. Each leaf must extend the tree at its next position.
    pub(crate) fn tree<L: MerkleLeaf + DeserializeOwned>(
        &mut self,
        size: u64,
        leaf_limit: u64,
    ) -> io::Result<Tree<L>> {
        let mut tree = Tree::default();
        for _ in 0..size {
            let leaf: L = self.item(leaf_limit)?;
            tree.append(leaf).map_err(io::Error::other)?;
        }
        Ok(tree)
    }

    pub(crate) fn finish(self) -> io::Result<()> {
        if self.0.read(&mut [0])? != 0 {
            return Err(invalid("unexpected bytes after authenticated archive"));
        }
        Ok(())
    }
}

impl Archive {
    /// Writes an archive without limiting its total size to a wire message.
    pub fn write_to(&self, file: &mut impl Write) -> io::Result<()> {
        if self.tree.size() != self.signed_head.head.size {
            return Err(invalid("archive size differs from signed head"));
        }
        let mut writer = ArchiveWriter::start(file, MAGIC)?;
        writer.item(&self.signed_head)?;
        writer.leaves(&self.tree)
    }

    /// Reads the full archive. Verify it against the installed keeper keys
    /// before using its proofs.
    pub fn read_from(file: &mut impl Read) -> io::Result<Self> {
        let mut reader =
            ArchiveReader::start(file, MAGIC, "invalid writer-driven authenticated archive")?;
        let signed_head: SignedHead = reader.item(MAX_ITEM_BYTES)?;
        if !signed_head.head.valid() {
            return Err(invalid("invalid authenticated archive head"));
        }
        let tree = reader.tree(signed_head.head.size, MAX_LEAF_BYTES)?;
        reader.finish()?;
        Ok(Self { tree, signed_head })
    }
}
