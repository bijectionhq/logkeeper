use std::{
    fs::{self, File, OpenOptions},
    io::{self, Read, Write},
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use uuid::Uuid;

use super::{CatalogAuthority, CatalogHistory, MAX_RECORD, SignedAuthority, decode, encode};
use crate::server::durability::{sync_directory, sync_file};
use crate::stream::consensus::{authenticated::Hash, invalid, keeper::authenticated::HISTORY_PAGE};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub(super) struct Reference {
    through: u64,
    authority_sha256: Hash,
    tail: Option<Hash>,
}

#[derive(Serialize, Deserialize)]
struct Page {
    previous: Option<Hash>,
    transitions: Vec<SignedAuthority>,
}

impl Reference {
    fn valid(self) -> bool {
        (self.through == 0) == self.tail.is_none()
    }

    fn matches_prefix(self, history: &CatalogHistory) -> bool {
        let authority = if self.through == 0 {
            Some(&history.genesis)
        } else {
            usize::try_from(self.through - 1)
                .ok()
                .and_then(|index| history.transitions.get(index))
                .map(|transition| &transition.authority)
        };
        self.valid()
            && authority.is_some_and(|authority| authority.digest() == self.authority_sha256)
    }

    pub(super) fn matches(self, history: &CatalogHistory) -> bool {
        history.latest().revision == self.through && self.matches_prefix(history)
    }

    pub(super) fn save(
        root: &Path,
        history: &CatalogHistory,
        previous: Option<Self>,
    ) -> io::Result<Self> {
        let directory = directory(root, history.genesis.catalog);
        let mut tail = None;
        let mut from = 0;
        if let Some(previous) = previous {
            if !previous.matches_prefix(history) {
                return Err(invalid("retained catalog history left its archived prefix"));
            }
            tail = previous.tail;
            from = usize::try_from(previous.through).map_err(io::Error::other)?;
        }
        if let Some(digest) = tail {
            read_page(&directory, digest)?;
        }
        let delta = &history.transitions[from..];
        if !delta.is_empty() {
            fs::create_dir_all(&directory)?;
            sync_directory(root)?;
            for transitions in delta.chunks(HISTORY_PAGE) {
                let page = Page {
                    previous: tail,
                    transitions: transitions.to_vec(),
                };
                tail = Some(write_page(&directory, &page)?);
            }
            sync_directory(&directory)?;
        }
        Ok(Self {
            through: history.latest().revision,
            authority_sha256: history.latest().digest(),
            tail,
        })
    }

    pub(super) fn load(self, root: &Path, genesis: CatalogAuthority) -> io::Result<CatalogHistory> {
        let directory = directory(root, genesis.catalog);
        let mut remaining = self.through;
        let mut tail = self.tail;
        let mut pages = Vec::new();
        while let Some(digest) = tail {
            let bytes = read_page(&directory, digest)?;
            let page: Page = decode(&bytes).map_err(|_| invalid("invalid catalog history page"))?;
            let count = page.transitions.len();
            if count == 0 || count > HISTORY_PAGE || count as u64 > remaining {
                return Err(invalid("invalid archived catalog history page range"));
            }
            remaining -= count as u64;
            tail = page.previous;
            pages.push(page.transitions);
        }
        if remaining != 0 {
            return Err(invalid("incomplete archived catalog history"));
        }
        let history = CatalogHistory {
            genesis,
            transitions: pages.into_iter().rev().flatten().collect(),
        };
        if !self.matches(&history) || history.verify(history.genesis.root()).is_err() {
            return Err(invalid(
                "archived catalog history does not match its committed reference",
            ));
        }
        Ok(history)
    }
}

fn directory(root: &Path, catalog: Uuid) -> PathBuf {
    root.join(format!("catalog-history-{:032x}", catalog.as_u128()))
}

fn page_path(directory: &Path, digest: Hash) -> PathBuf {
    let mut name = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write;
        write!(&mut name, "{byte:02x}").unwrap();
    }
    directory.join(name)
}

fn read_page(directory: &Path, digest: Hash) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    File::open(page_path(directory, digest))?
        .take(MAX_RECORD as u64 + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() > MAX_RECORD || Hash::from(Sha256::digest(&bytes)) != digest {
        return Err(invalid(
            "archived catalog history page has a different digest",
        ));
    }
    Ok(bytes)
}

fn write_page(directory: &Path, page: &Page) -> io::Result<Hash> {
    let bytes = encode(page)?;
    if bytes.len() > MAX_RECORD {
        return Err(invalid("catalog history page exceeds its size bound"));
    }
    let digest = Sha256::digest(&bytes).into();
    match read_page(directory, digest) {
        Ok(_) => return Ok(digest),
        Err(error) if error.kind() == io::ErrorKind::NotFound => (),
        Err(error) => return Err(error),
    }
    let temporary = directory.join(format!(".{}.tmp", Uuid::new_v4()));
    let result = (|| {
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)?;
        file.write_all(&bytes)?;
        sync_file(&file)?;
        match fs::hard_link(&temporary, page_path(directory, digest)) {
            Ok(()) => (),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                read_page(directory, digest)?;
            }
            Err(error) => return Err(error),
        }
        Ok(digest)
    })();
    let _ = fs::remove_file(temporary);
    result
}

#[cfg(test)]
mod tests;
