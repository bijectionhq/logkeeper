use std::io::{self, Read, Write};

use super::{Archive, CatalogHistory, SignedHead};
use crate::stream::{
    authenticated::{ArchiveReader, ArchiveWriter},
    consensus::{MAX_MESSAGE, invalid},
};

const MAGIC: &[u8; 8] = b"LKAARCH1";
const MAX_LEAF_BYTES: u64 = 128;

impl Archive {
    /// Writes an archive without limiting its total size to a wire message.
    pub fn write_to(&self, file: &mut impl Write) -> io::Result<()> {
        if self.tree.size() != self.signed_head.head.size {
            return Err(invalid("archive size differs from signed head"));
        }
        let mut writer = ArchiveWriter::start(file, MAGIC)?;
        writer.item(&(
            &self.signed_head,
            &self.history.genesis,
            self.history.transitions.len() as u64,
        ))?;
        for transition in &self.history.transitions {
            writer.item(transition)?;
        }
        writer.leaves(&self.tree)
    }

    /// Reads the full archive. Verify it against a pinned catalog root before using its proofs.
    pub fn read_from(file: &mut impl Read) -> io::Result<Self> {
        let mut reader = ArchiveReader::start(file, MAGIC, "invalid authenticated archive format")?;
        let signed_head: SignedHead = reader.item(MAX_MESSAGE)?;
        if !signed_head.head.valid() {
            return Err(invalid("invalid authenticated archive head"));
        }
        let genesis = reader.item(MAX_MESSAGE)?;
        let transition_count: u64 = reader.item(8)?;
        let mut transitions = Vec::new();
        for _ in 0..transition_count {
            transitions.push(reader.item(MAX_MESSAGE)?);
        }
        let history = CatalogHistory {
            genesis,
            transitions,
        };
        let tree = reader.tree(signed_head.head.size, MAX_LEAF_BYTES)?;
        reader.finish()?;
        Ok(Self {
            tree,
            signed_head,
            history,
        })
    }
}
