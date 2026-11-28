use super::*;

impl Authentication {
    pub(super) fn archive_directory(&self, stream: StreamId) -> PathBuf {
        self.archive_directory.join(format!("{:032x}", stream.0))
    }

    pub(super) fn save_archive(&self, archive: &Archive) -> io::Result<()> {
        let head = archive.signed_head.head;
        let directory = self.archive_directory(head.stream);
        fs::create_dir_all(&directory)?;
        sync_directory(&self.archive_directory)?;
        let target = directory.join(format!("{:016x}.archive", head.size));
        let temporary = directory.join(format!(".{}.tmp", Uuid::new_v4()));
        let result = (|| {
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&temporary)?;
            archive.write_to(&mut file)?;
            sync_file(&file)?;
            match fs::hard_link(&temporary, &target) {
                Ok(()) => (),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                    let existing = Archive::read_from(&mut File::open(&target)?)?;
                    existing
                        .verify(archive.certification.history.genesis.root())
                        .map_err(io::Error::other)?;
                    if existing.signed_head.head.stream != head.stream
                        || existing.signed_head.head.size != head.size
                        || existing.signed_head.head.root != head.root
                    {
                        return Err(invalid(
                            "retirement left a conflicting authenticated archive",
                        ));
                    }
                }
                Err(error) => return Err(error),
            }
            sync_directory(&directory)
        })();
        let _ = fs::remove_file(temporary);
        result
    }

    pub(super) fn read_archive(&self, stream: StreamId, size: Option<u64>) -> io::Result<Archive> {
        let directory = self.archive_directory(stream);
        let size = match size {
            Some(size) => size,
            None => {
                let mut largest = None;
                for entry in fs::read_dir(&directory)? {
                    let entry = entry?;
                    if let Some(size) = entry
                        .file_name()
                        .to_str()
                        .and_then(|name| name.strip_suffix(".archive"))
                        .and_then(|name| u64::from_str_radix(name, 16).ok())
                    {
                        largest = largest.max(Some(size));
                    }
                }
                largest.ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?
            }
        };
        let archive = Archive::read_from(&mut File::open(
            directory.join(format!("{size:016x}.archive")),
        )?)?;
        if archive.signed_head.head.stream != stream
            || archive.verify(archive.certification.history.genesis.root()).is_err()
        {
            return Err(invalid("authenticated archive does not match its stream"));
        }
        Ok(archive)
    }
}

impl Engine {
    pub(in crate::stream::consensus::keeper) async fn read_authentication_archive(
        &self,
        stream: StreamId,
        request: AuthenticationRequest,
    ) -> Option<Reply> {
        let authentication = Arc::clone(self.authentication.as_ref()?);
        let size = match &request {
            AuthenticationRequest::Head { size }
            | AuthenticationRequest::Inclusion { size, .. } => *size,
            _ => None,
        };
        let archive =
            tokio::task::spawn_blocking(move || authentication.read_archive(stream, size))
                .await
                .ok()?
                .ok()?;
        Some(match request {
            AuthenticationRequest::Head { size }
                if size.is_none_or(|size| size == archive.tree.size()) =>
            {
                authentication_reply(&archive.signed_head)
            }
            AuthenticationRequest::Inclusion { at, size }
                if size.is_none_or(|size| size == archive.tree.size()) =>
            {
                match (
                    archive.tree.leaf(at),
                    archive.tree.inclusion(at, archive.tree.size()),
                ) {
                    (Some(leaf), Ok(path)) => authentication_reply(&Included {
                        leaf: leaf.clone(),
                        path,
                        signed_head: archive.signed_head,
                    }),
                    _ => failure(JournalError::NotFound),
                }
            }
            request => Self::tree_read(&archive.tree, request),
        })
    }

    pub(in crate::stream::consensus::keeper) async fn archive_and_delete(&self, group: &Group) -> Reply {
        let Some(authentication) = self.authentication.clone() else {
            return failure(JournalError::Unsupported);
        };
        if let Err(reply) = group.barrier(Instant::now() + REQUEST_TIMEOUT).await {
            return reply;
        }
        let Some(tree) = group.state.authenticated_tree() else {
            return failure(JournalError::Unavailable);
        };
        let size = tree.size();
        let root = tree.root();
        let signed_head = match self.certify_head(group, size, root).await {
            Ok(head) => head,
            Err(reply) => return reply,
        };
        let history = match self.authentication_history().await {
            Ok(history) => history,
            Err(error) => return failure(error),
        };
        let stream = match self.fetch_stream_authorities(group.genesis.stream).await {
            Ok(stream) => stream,
            Err(error) => return failure(error),
        };
        let archive = Archive {
            tree,
            signed_head,
            certification: Certification { history, stream },
        };
        if archive.verify(archive.certification.history.genesis.root()).is_err() {
            return failure(JournalError::Corrupted);
        }
        if !matches!(
            tokio::task::spawn_blocking(move || authentication.save_archive(&archive)).await,
            Ok(Ok(()))
        ) {
            return failure(JournalError::Unavailable);
        }
        group
            .write(Command::DeleteAuthenticated { size, root })
            .await
    }
}
