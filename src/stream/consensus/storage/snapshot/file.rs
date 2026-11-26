//! Snapshot transport holds a selected image and materializes a private wire
//! file only when OpenRaft actually seeks or reads. Maintenance never spools it.

use std::{
    future::Future,
    io::{self, SeekFrom},
    path::{Path, PathBuf},
    pin::Pin,
    sync::Arc,
    task::{Context, Poll, ready},
};

use tokio::{
    fs::File,
    io::{AsyncRead, AsyncSeek, AsyncWrite, ReadBuf},
    task::JoinHandle,
};

use crate::stream::consensus::{
    SnapshotMeta, invalid,
    storage::space::{Space, Transfer},
};

pub(super) struct Temporary {
    pub path: PathBuf,
    pub transfer: Transfer,
    pub _pin: Option<Arc<()>>,
}

impl Drop for Temporary {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

pub(super) struct Open {
    pub file: File,
    pub temporary: Temporary,
    pub digest: Option<Arc<[u8; 32]>>,
    pub _source: Option<Box<dyn Send + Sync>>,
}

type MakeFile = Box<dyn FnOnce() -> io::Result<Open> + Send>;

pub(in crate::stream::consensus) struct SnapshotFile {
    meta: SnapshotMeta,
    open: Option<Open>,
    make: Option<MakeFile>,
    running: Option<JoinHandle<io::Result<Open>>>,
    seek: Option<SeekFrom>,
    position: u64,
    incoming: bool,
}

impl SnapshotFile {
    pub(super) async fn receive(
        path: &Path,
        space: &Space,
        lifetime: Arc<()>,
        digest: [u8; 32],
        meta: SnapshotMeta,
    ) -> io::Result<Self> {
        let transfer = space.transfer()?;
        let path = path.join(format!("incoming-{}", uuid::Uuid::new_v4()));
        let file = tokio::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(&path)
            .await?;
        Ok(Self {
            meta,
            open: Some(Open {
                file,
                temporary: Temporary {
                    path,
                    transfer,
                    _pin: Some(lifetime),
                },
                digest: Some(Arc::new(digest)),
                _source: None,
            }),
            make: None,
            running: None,
            seek: None,
            position: 0,
            incoming: true,
        })
    }

    pub(super) fn send(
        meta: SnapshotMeta,
        make: impl FnOnce() -> io::Result<Open> + Send + 'static,
    ) -> Self {
        Self {
            meta,
            open: None,
            make: Some(Box::new(make)),
            running: None,
            seek: None,
            position: 0,
            incoming: false,
        }
    }

    /// The metadata the image records, including its transfer id.
    pub fn meta(&self) -> &SnapshotMeta {
        &self.meta
    }

    pub(super) async fn received(mut self) -> io::Result<(std::fs::File, Temporary, [u8; 32])> {
        if !self.incoming {
            return Err(invalid("snapshot is not an incoming transfer"));
        }
        let Open {
            file,
            temporary,
            digest,
            ..
        } = self.open.take().unwrap();
        let digest = digest.ok_or_else(|| invalid("missing authenticated snapshot digest"))?;
        Ok((file.into_std().await, temporary, *digest))
    }

    fn poll_open(&mut self, cx: &mut Context<'_>) -> Poll<io::Result<&mut Open>> {
        if self.open.is_none() {
            if let Some(make) = self.make.take() {
                self.running = Some(tokio::task::spawn_blocking(make));
            }
            let Some(task) = self.running.as_mut() else {
                return Poll::Ready(Err(invalid("snapshot transfer could not be staged")));
            };
            let result = ready!(Pin::new(task).poll(cx)).map_err(io::Error::other);
            self.running = None;
            self.open = Some(result??);
        }
        Poll::Ready(Ok(self.open.as_mut().unwrap()))
    }
}

impl AsyncRead for SnapshotFile {
    fn poll_read(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        let file = ready!(self.poll_open(cx))?;
        Pin::new(&mut file.file).poll_read(cx, buf)
    }
}

impl AsyncSeek for SnapshotFile {
    fn start_seek(mut self: Pin<&mut Self>, seek: SeekFrom) -> io::Result<()> {
        if self.seek.is_some() {
            return Err(invalid("snapshot already has a pending seek"));
        }
        self.seek = Some(seek);
        Ok(())
    }

    fn poll_complete(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<u64>> {
        ready!(self.poll_open(cx))?;
        let pending = self.seek.take();
        let open = self.open.as_mut().unwrap();
        if let Some(seek) = pending {
            Pin::new(&mut open.file).start_seek(seek)?;
        }
        let at = ready!(Pin::new(&mut open.file).poll_complete(cx))?;
        self.position = at;
        Poll::Ready(Ok(at))
    }
}

impl AsyncWrite for SnapshotFile {
    fn poll_write(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<io::Result<usize>> {
        if !self.incoming {
            return Poll::Ready(Err(invalid("snapshot transfer is read-only")));
        }
        let end = self
            .position
            .checked_add(buf.len() as u64)
            .ok_or_else(|| invalid("snapshot transfer offset overflow"))?;
        let open = self.open.as_mut().unwrap();
        open.temporary
            .transfer
            .account(&std::fs::metadata(&open.temporary.path)?);
        open.temporary.transfer.grow(end)?;
        let wrote = ready!(Pin::new(&mut open.file).poll_write(cx, buf))?;
        self.position += wrote as u64;
        Poll::Ready(Ok(wrote))
    }

    fn poll_flush(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        let open = ready!(self.poll_open(cx))?;
        Pin::new(&mut open.file).poll_flush(cx)
    }

    fn poll_shutdown(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        let open = ready!(self.poll_open(cx))?;
        Pin::new(&mut open.file).poll_shutdown(cx)
    }
}
