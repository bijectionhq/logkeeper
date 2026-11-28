use std::io::{self, Read, Write};

use bincode::Options;
use serde::de::DeserializeOwned;

use super::{Archive, CatalogHistory, Certification, Leaf, SignedHead, Tree};
use crate::stream::consensus::{MAX_MESSAGE, invalid, options};

const MAGIC: &[u8; 8] = b"LKAARCH2";
const MAX_LEAF_BYTES: u64 = 128;

impl Archive {
    /// Writes an archive without limiting its total size to a wire message.
    pub fn write_to(&self, file: &mut impl Write) -> io::Result<()> {
        if self.tree.size() != self.signed_head.head.size {
            return Err(invalid("archive size differs from signed head"));
        }
        file.write_all(MAGIC)?;
        options()
            .serialize_into(
                &mut *file,
                &(
                    &self.signed_head,
                    &self.certification.history.genesis,
                    self.certification.history.transitions.len() as u64,
                ),
            )
            .map_err(io::Error::other)?;
        for transition in &self.certification.history.transitions {
            options()
                .serialize_into(&mut *file, transition)
                .map_err(io::Error::other)?;
        }
        options()
            .serialize_into(&mut *file, &(self.certification.stream.len() as u64))
            .map_err(io::Error::other)?;
        for authority in &self.certification.stream {
            options()
                .serialize_into(&mut *file, authority)
                .map_err(io::Error::other)?;
        }
        for leaf in self.tree.leaves() {
            options()
                .serialize_into(&mut *file, leaf)
                .map_err(io::Error::other)?;
        }
        Ok(())
    }

    /// Reads the full archive. Verify it against a pinned catalog root before using its proofs.
    pub fn read_from(file: &mut impl Read) -> io::Result<Self> {
        let mut magic = [0; MAGIC.len()];
        file.read_exact(&mut magic)?;
        if &magic != MAGIC {
            return Err(invalid("invalid authenticated archive format"));
        }

        let signed_head: SignedHead = read_item(file, MAX_MESSAGE)?;
        if !signed_head.head.valid() {
            return Err(invalid("invalid authenticated archive head"));
        }
        let genesis = read_item(file, MAX_MESSAGE)?;
        let transition_count: u64 = read_item(file, 8)?;
        let mut transitions = Vec::new();
        for _ in 0..transition_count {
            transitions.push(read_item(file, MAX_MESSAGE)?);
        }
        let history = CatalogHistory {
            genesis,
            transitions,
        };
        let authority_count: u64 = read_item(file, 8)?;
        let mut stream = Vec::new();
        for _ in 0..authority_count {
            stream.push(read_item(file, MAX_MESSAGE)?);
        }

        let mut tree = Tree::default();
        for _ in 0..signed_head.head.size {
            let leaf: Leaf = read_item(file, MAX_LEAF_BYTES)?;
            tree.append(leaf).map_err(io::Error::other)?;
        }
        if file.read(&mut [0])? != 0 {
            return Err(invalid("unexpected bytes after authenticated archive"));
        }
        Ok(Self {
            tree,
            signed_head,
            certification: Certification { history, stream },
        })
    }
}

fn read_item<T: DeserializeOwned>(file: &mut impl Read, limit: u64) -> io::Result<T> {
    options()
        .with_limit(limit)
        .deserialize_from(file)
        .map_err(io::Error::other)
}
