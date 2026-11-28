//! Quorum-signed history proofs for writer-driven streams.
//!
//! Each call asks the stream's current ensemble, so it follows replacements
//! like any other read. Every proof is verified against the installed
//! `KeeperKeys` before it is returned. Proof reads never use the writer's
//! epoch, so any client of the stream can make them.

use std::sync::Arc;

use futures::{StreamExt, stream::FuturesUnordered};
use journal_contract::{BoxFuture, JournalError, Lsn, Result, StreamId};

use super::{Io, QUORUM, Stream, Writer, head, refusal};
use crate::stream::{
    authenticated::{
        Archive, AuthenticatedJournal, Consistency, Head, HeadSignature, Inclusion, KeeperKeys,
        SignedHead, Tree,
        protocol::{self, AuthReply, AuthRequest, LEAF_PAGE},
    },
    wire::{KeeperId, Reply, Request},
};

impl Writer {
    /// Mount the operator-installed keeper key set, the trust root of every proof.
    pub fn with_authentication(mut self, keys: KeeperKeys) -> Result<Self> {
        if !keys.valid() {
            return Err(JournalError::Unavailable);
        }
        self.authentication = Some(Arc::new(keys));
        Ok(self)
    }

    pub fn keeper_keys(&self) -> Option<&KeeperKeys> {
        self.authentication.as_deref()
    }

    fn trust(&self) -> Result<Arc<KeeperKeys>> {
        self.authentication.clone().ok_or(JournalError::Unsupported)
    }

    /// `Ok` when two members keep the stream's complete leaf history.
    pub async fn require_authenticated(&self, stream: StreamId) -> Result<()> {
        self.trust()?;
        self.following(stream, |stream| async move {
            let mut complete = 0;
            let mut errors = Vec::new();
            for (_, reply) in ask_all(&self.io, &stream, &AuthRequest::Status).await {
                match reply {
                    Ok(AuthReply::Status { complete: true, .. }) => complete += 1,
                    Ok(AuthReply::Unsupported) => errors.push(JournalError::Unsupported),
                    Ok(_) => errors.push(JournalError::Unavailable),
                    Err(error) => errors.push(error),
                }
            }
            if complete >= QUORUM {
                Ok(())
            } else {
                Err(refusal(&errors))
            }
        })
        .await
    }

    /// A head signed by two members of the stream's ensemble, at `size` or at
    /// the current linearizable head.
    pub async fn authenticated_head(
        &self,
        stream: StreamId,
        size: Option<u64>,
    ) -> Result<SignedHead> {
        let keys = self.trust()?;
        let keys = &*keys;
        self.following(stream, |stream| async move {
            let size = self.size(&stream, size).await?;
            certify(&self.io, keys, &stream, size).await
        })
        .await
    }

    pub async fn inclusion(
        &self,
        stream: StreamId,
        at: Lsn,
        size: Option<u64>,
    ) -> Result<Inclusion> {
        let keys = self.trust()?;
        let keys = &*keys;
        self.following(stream, |stream| async move {
            let size = self.size(&stream, size).await?;
            if at.0 == 0 || at.0 > size {
                return Err(JournalError::Conflict { head: Lsn(size) });
            }
            let signed_head = certify(&self.io, keys, &stream, size).await?;
            let request = AuthRequest::Path { at, size };
            for keeper in self.io.transport.read_order(stream.ensemble) {
                if let Ok(AuthReply::Path { leaf, path }) =
                    ask(&self.io, keeper, stream.id, &request).await
                {
                    let proof = Inclusion {
                        leaf,
                        path,
                        signed_head: signed_head.clone(),
                    };
                    if leaf.at == at && proof.verify(keys).is_ok() {
                        return Ok(proof);
                    }
                }
            }
            Err(JournalError::Unavailable)
        })
        .await
    }

    /// Proves that `later` extends `earlier`. The heads can name different
    /// ensembles. Both must verify against the installed keys.
    pub async fn consistency(&self, earlier: SignedHead, later: SignedHead) -> Result<Consistency> {
        let keys = self.trust()?;
        let keys = &*keys;
        if earlier.verify(keys).is_err() || later.verify(keys).is_err() {
            return Err(JournalError::Corrupted);
        }
        let stream = earlier.head.stream;
        if later.head.stream != stream || earlier.head.size > later.head.size {
            return Err(JournalError::Conflict {
                head: Lsn(later.head.size),
            });
        }
        let (earlier, later) = (&earlier, &later);
        self.following(stream, |stream| async move {
            let request = AuthRequest::Consistency {
                earlier: earlier.head.size,
                later: later.head.size,
            };
            for keeper in self.io.transport.read_order(stream.ensemble) {
                if let Ok(AuthReply::Consistency(path)) =
                    ask(&self.io, keeper, stream.id, &request).await
                {
                    let proof = Consistency {
                        earlier: earlier.clone(),
                        later: later.clone(),
                        path,
                    };
                    // A head from another history fails here rather than being trusted.
                    match proof.verify(keys) {
                        Ok(()) => return Ok(proof),
                        Err(_) => return Err(JournalError::Corrupted),
                    }
                }
            }
            Err(JournalError::Unavailable)
        })
        .await
    }

    /// Every leaf through a certified head. Leaves can come from any single
    /// member, since the archive is checked against the quorum-signed root.
    pub async fn authenticated_archive(
        &self,
        stream: StreamId,
        size: Option<u64>,
    ) -> Result<Archive> {
        let keys = self.trust()?;
        let keys = &*keys;
        self.following(stream, |stream| async move {
            let size = self.size(&stream, size).await?;
            let signed_head = certify(&self.io, keys, &stream, size).await?;
            let mut tree = Tree::default();
            let keepers = self.io.transport.read_order(stream.ensemble);
            'pages: while tree.size() < size {
                let request = AuthRequest::Leaves {
                    from: Lsn(tree.size() + 1),
                    through: size,
                };
                for keeper in keepers {
                    if let Ok(AuthReply::Leaves(leaves)) =
                        ask(&self.io, keeper, stream.id, &request).await
                        && !leaves.is_empty()
                        && tree.extend(leaves).is_ok()
                    {
                        continue 'pages;
                    }
                }
                return Err(JournalError::Unavailable);
            }
            let archive = Archive { tree, signed_head };
            archive.verify(keys).map_err(|_| JournalError::Corrupted)?;
            Ok(archive)
        })
        .await
    }

    /// Install missing leaves on every member that lacks them, for example a
    /// keeper replaced in after the stream was trimmed. Run it after a repair
    /// moves a stream, while two members still hold the full history.
    pub async fn seed_authenticated(&self, stream: StreamId) -> Result<()> {
        let keys = self.trust()?;
        let keys = &*keys;
        self.following(stream, |stream| async move {
            let size = head::head(self.io.clone(), stream.clone()).await?.0;
            let signed = certify(&self.io, keys, &stream, size).await?;
            for (keeper, reply) in ask_all(&self.io, &stream, &AuthRequest::Status).await {
                if let Ok(AuthReply::Status {
                    ingested,
                    floor,
                    complete: false,
                }) = reply
                {
                    seed(&self.io, stream.id, keeper, ingested, floor, &signed).await?;
                }
            }
            Ok(())
        })
        .await
    }

    async fn size(&self, stream: &Arc<Stream>, size: Option<u64>) -> Result<u64> {
        match size {
            Some(size) => Ok(size),
            None => Ok(head::head(self.io.clone(), stream.clone()).await?.0),
        }
    }
}

impl AuthenticatedJournal for Writer {
    fn keys(&self) -> Option<&KeeperKeys> {
        self.keeper_keys()
    }

    fn require_authenticated(&self, stream: StreamId) -> BoxFuture<'_, Result<()>> {
        Box::pin(Writer::require_authenticated(self, stream))
    }

    fn authenticated_head(
        &self,
        stream: StreamId,
        size: Option<u64>,
    ) -> BoxFuture<'_, Result<SignedHead>> {
        Box::pin(Writer::authenticated_head(self, stream, size))
    }

    fn inclusion(
        &self,
        stream: StreamId,
        at: Lsn,
        size: Option<u64>,
    ) -> BoxFuture<'_, Result<Inclusion>> {
        Box::pin(Writer::inclusion(self, stream, at, size))
    }

    fn consistency(
        &self,
        earlier: SignedHead,
        later: SignedHead,
    ) -> BoxFuture<'_, Result<Consistency>> {
        Box::pin(Writer::consistency(self, earlier, later))
    }

    fn authenticated_archive(
        &self,
        stream: StreamId,
        size: Option<u64>,
    ) -> BoxFuture<'_, Result<Archive>> {
        Box::pin(Writer::authenticated_archive(self, stream, size))
    }
}

async fn ask(
    io: &Io,
    keeper: KeeperId,
    stream: StreamId,
    request: &AuthRequest,
) -> Result<AuthReply> {
    let request = protocol::encode(request).map_err(|_| JournalError::Unavailable)?;
    match io
        .call(keeper, Request::Authenticated { stream, request })
        .await?
    {
        Reply::Authenticated(body) => {
            protocol::decode(&body).map_err(|_| JournalError::Unavailable)
        }
        _ => Err(JournalError::Unavailable),
    }
}

async fn ask_all(
    io: &Io,
    stream: &Stream,
    request: &AuthRequest,
) -> Vec<(KeeperId, Result<AuthReply>)> {
    FuturesUnordered::from_iter(
        stream
            .ensemble
            .map(|keeper| async move { (keeper, ask(io, keeper, stream.id, request).await) }),
    )
    .collect()
    .await
}

/// Collect signatures over one identical statement from two members. Each
/// share is checked on arrival, so a faulty member cannot block a quorum of
/// two honest ones. A member that reports missing leaves is seeded once the
/// quorum head is known.
async fn certify(
    io: &Arc<Io>,
    keys: &KeeperKeys,
    stream: &Stream,
    size: u64,
) -> Result<SignedHead> {
    let request = AuthRequest::Sign { size };
    let request = &request;
    let mut calls = FuturesUnordered::from_iter(
        stream
            .ensemble
            .map(|keeper| async move { (keeper, ask(io, keeper, stream.id, request).await) }),
    );
    let mut shares: Vec<(Head, HeadSignature)> = Vec::new();
    let mut missing = Vec::new();
    let mut errors = Vec::new();
    while let Some((keeper, reply)) = calls.next().await {
        match reply {
            Ok(AuthReply::Signed { head, signature })
                if head.stream == stream.id
                    && head.size == size
                    && head.journal == keys.journal
                    && signature.keeper == keeper
                    && keys.verify_one(&head.statement(), &signature) =>
            {
                shares.push((head, signature));
                let mut signatures: Vec<_> = shares
                    .iter()
                    .filter(|(seen, _)| *seen == head)
                    .map(|(_, signature)| signature.clone())
                    .collect();
                if signatures.len() < QUORUM {
                    continue;
                }
                signatures.sort_by_key(|signature| signature.keeper);
                let signed = SignedHead { head, signatures };
                if signed.verify(keys).is_ok() {
                    for (keeper, ingested, floor) in std::mem::take(&mut missing) {
                        let (io, id, signed) = (io.clone(), stream.id, signed.clone());
                        tokio::spawn(async move {
                            let _ = seed(&io, id, keeper, ingested, floor, &signed).await;
                        });
                    }
                    return Ok(signed);
                }
                // Two shares over one statement that still fail is a key-set fault.
                errors.push(JournalError::Corrupted);
            }
            Ok(AuthReply::Missing { ingested, floor }) => {
                missing.push((keeper, ingested, floor));
                errors.push(JournalError::Unavailable);
            }
            Ok(AuthReply::Unsupported) => errors.push(JournalError::Unsupported),
            Ok(_) => errors.push(JournalError::Unavailable),
            Err(error) => errors.push(error),
        }
    }
    // Members that disagree on the root or the ensemble cannot certify a head.
    Err(refusal(&errors))
}

/// Copy the leaves `ingested + 1 .. floor` from the head's signers to `target`.
/// The target installs them only if they extend to the signed root through its
/// own records, so a faulty relay cannot plant leaves.
async fn seed(
    io: &Io,
    stream: StreamId,
    target: KeeperId,
    ingested: u64,
    floor: Lsn,
    signed: &SignedHead,
) -> Result<()> {
    let end = floor.0.saturating_sub(1);
    if ingested >= end || signed.head.size < end {
        return Ok(());
    }
    let sources: Vec<KeeperId> = signed
        .signatures
        .iter()
        .map(|signature| signature.keeper)
        .filter(|keeper| *keeper != target)
        .collect();
    let mut from = ingested + 1;
    while from <= end {
        let through = end.min(from + LEAF_PAGE as u64 - 1);
        let mut page = None;
        for &source in &sources {
            let request = AuthRequest::Leaves {
                from: Lsn(from),
                through,
            };
            if let Ok(AuthReply::Leaves(leaves)) = ask(io, source, stream, &request).await
                && !leaves.is_empty()
                && leaves.len() as u64 <= through - from + 1
            {
                page = Some(leaves);
                break;
            }
        }
        let leaves = page.ok_or(JournalError::Unavailable)?;
        let next = from + leaves.len() as u64;
        let request = AuthRequest::Seed {
            from: Lsn(from),
            leaves,
            head: (next > end).then(|| signed.clone()),
        };
        match ask(io, target, stream, &request).await? {
            AuthReply::Seeded { .. } => from = next,
            _ => return Err(JournalError::Unavailable),
        }
    }
    Ok(())
}
