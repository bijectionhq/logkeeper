use std::{collections::BTreeMap, io, path::PathBuf, sync::Arc};

use journal_contract::StreamId;
use parking_lot::Mutex;
use tokio::sync::Semaphore;
use uuid::Uuid;

// These floors are never loaned to ordinary work or transfers. The external
// floor includes directory/allocation overhead from other volume users.
use crate::stream::consensus::decisions::{
    COVERED_FLOOR, MAINTENANCE_BYTES, MAINTENANCE_FLOOR, ORDINARY_FLOOR, PROTOCOL_FLOOR,
    SCRATCH_BYTES, SCRATCH_FLOOR, fits, suffix_admits,
};
const MAX_TRANSFER_TOTAL: u64 = 512 * MIB;
pub(in crate::stream::consensus) const MAX_TRANSFER_FILE: u64 = 256 * MIB;
const MIB: u64 = 1024 * 1024;
pub(in crate::stream::consensus) const WAL_METADATA_BYTES: u64 = 768 * 1024;

#[derive(Clone)]
pub(in crate::stream::consensus) struct Space(Arc<Inner>);

struct Inner {
    path: PathBuf,
    block: u64,
    #[cfg(test)]
    measured: std::sync::atomic::AtomicU64,
    state: Mutex<Ledger>,
    scratch: Arc<Semaphore>,
}

#[derive(Default)]
struct Ledger {
    pending: u64,
    slots: BTreeMap<StreamId, usize>,
    tickets: BTreeMap<(StreamId, Uuid), (u64, usize)>,
    transfers: u64,
    sessions: usize,
    covered: u64,
}

pub(in crate::stream::consensus) struct Reservation {
    inner: Arc<Inner>,
    bytes: u64,
    slot: Option<(StreamId, Uuid)>,
    covered: bool,
    uncertain: bool,
}

pub(super) struct Transfer {
    inner: Arc<Inner>,
    bytes: u64,
    allocated: u64,
}

#[derive(Debug)]
pub(in crate::stream::consensus) enum Admission {
    FullSuffix,
    Space,
}

impl Space {
    pub fn new(path: PathBuf) -> io::Result<Self> {
        let block = fs2::allocation_granularity(&path)?;
        if !block.is_power_of_two() || block > 16 * 1024 {
            return Err(super::super::invalid(
                "keeper volume allocation unit exceeds its geometry",
            ));
        }
        Ok(Self(Arc::new(Inner {
            path,
            block,
            #[cfg(test)]
            measured: std::sync::atomic::AtomicU64::new(u64::MAX),
            state: Mutex::default(),
            scratch: Arc::new(Semaphore::new(1)),
        })))
    }

    pub fn allocation_unit(&self) -> u64 {
        self.0.block
    }

    pub fn reserve(&self, bytes: u64) -> io::Result<Reservation> {
        self.book(bytes, ORDINARY_FLOOR, None)
    }

    pub fn ordinary_slot(
        &self,
        scope: StreamId,
        ticket: Uuid,
        limit: usize,
        bytes: u64,
        occupied: impl FnOnce() -> usize,
    ) -> Result<Reservation, Admission> {
        self.ordinary_slots(scope, ticket, limit, bytes, || (occupied(), 1))
    }

    pub fn ordinary_slots(
        &self,
        scope: StreamId,
        ticket: Uuid,
        limit: usize,
        bytes: u64,
        occupancy: impl FnOnce() -> (usize, usize),
    ) -> Result<Reservation, Admission> {
        let mut state = self.0.state.lock();
        let (occupied, new) = occupancy();
        if !suffix_admits(
            occupied,
            new,
            state.slots.get(&scope).copied().unwrap_or(0),
            limit,
        ) {
            return Err(Admission::FullSuffix);
        }
        let key = (scope, ticket);
        if state.tickets.contains_key(&key) {
            return Err(Admission::Space);
        }
        self.available(&state, bytes, ORDINARY_FLOOR)
            .map_err(|_| Admission::Space)?;
        state.pending += bytes;
        *state.slots.entry(scope).or_default() += new;
        state.tickets.insert(key, (bytes, new));
        Ok(Reservation {
            inner: self.0.clone(),
            bytes,
            slot: Some(key),
            covered: false,
            uncertain: false,
        })
    }

    pub fn protocol(&self, bytes: u64) -> io::Result<Reservation> {
        self.book(bytes, PROTOCOL_FLOOR, None)
    }

    pub fn maintenance(&self, bytes: u64) -> io::Result<Reservation> {
        self.book(bytes, MAINTENANCE_FLOOR, None)
    }

    pub fn covered(&self, bytes: u64) -> io::Result<Reservation> {
        let mut state = self.0.state.lock();
        if state.covered.saturating_add(bytes) > MAINTENANCE_BYTES {
            return Err(exhausted());
        }
        self.available(&state, bytes, COVERED_FLOOR)?;
        state.covered += bytes;
        state.pending += bytes;
        Ok(Reservation {
            inner: self.0.clone(),
            bytes,
            slot: None,
            covered: true,
            uncertain: false,
        })
    }

    pub async fn scratch(
        &self,
        bytes: u64,
    ) -> io::Result<(Reservation, tokio::sync::OwnedSemaphorePermit)> {
        if bytes > SCRATCH_BYTES {
            return Err(exhausted());
        }
        let permit = self
            .0
            .scratch
            .clone()
            .acquire_owned()
            .await
            .map_err(io::Error::other)?;
        let reservation = self.book(bytes, SCRATCH_FLOOR, None)?;
        Ok((reservation, permit))
    }

    fn book(
        &self,
        bytes: u64,
        floor: u64,
        slot: Option<(StreamId, Uuid)>,
    ) -> io::Result<Reservation> {
        let mut state = self.0.state.lock();
        self.available(&state, bytes, floor)?;
        state.pending += bytes;
        Ok(Reservation {
            inner: self.0.clone(),
            bytes,
            slot,
            covered: false,
            uncertain: false,
        })
    }

    /// Whether ordinary writes still have room above the ordinary floor,
    /// with headroom for 64 MiB more.
    pub fn accepts_streams(&self) -> bool {
        let state = self.0.state.lock();
        self.available(&state, 64 * MIB, ORDINARY_FLOOR).is_ok()
    }

    fn available(&self, state: &Ledger, bytes: u64, floor: u64) -> io::Result<()> {
        if !fits(self.measured_space()?, state.pending, bytes, floor) {
            return Err(exhausted());
        }
        Ok(())
    }

    fn measured_space(&self) -> io::Result<u64> {
        #[cfg(test)]
        {
            let measured = self.0.measured.load(std::sync::atomic::Ordering::Relaxed);
            if measured != u64::MAX {
                return Ok(measured);
            }
        }
        fs2::available_space(&self.0.path)
    }

    #[cfg(test)]
    pub fn set_available(&self, bytes: u64) {
        self.0
            .measured
            .store(bytes, std::sync::atomic::Ordering::Relaxed);
    }

    #[cfg(test)]
    pub fn outstanding(&self, scope: StreamId) -> (usize, u64) {
        let ledger = self.0.state.lock();
        ledger
            .tickets
            .iter()
            .filter(|((stream, _), _)| *stream == scope)
            .fold((0, 0), |(count, bytes), (_, &(reserved, _))| {
                (count + 1, bytes + reserved)
            })
    }

    pub(super) fn transfer(&self) -> io::Result<Transfer> {
        let mut state = self.0.state.lock();
        if state.sessions >= 4 {
            return Err(exhausted());
        }
        state.sessions += 1;
        Ok(Transfer {
            inner: self.0.clone(),
            bytes: 0,
            allocated: 0,
        })
    }
    pub fn settle(&self, tickets: &[(StreamId, Uuid)], install: impl FnOnce()) {
        let mut state = self.0.state.lock();
        install();
        for &ticket in tickets {
            state.close(ticket);
        }
    }
}

impl Transfer {
    pub fn grow(&mut self, end: u64) -> io::Result<()> {
        let block = self.inner.block;
        let end = end.checked_add(block - 1).ok_or_else(exhausted)? / block * block;
        if end > MAX_TRANSFER_FILE {
            return Err(exhausted());
        }
        let extra = end.saturating_sub(self.bytes);
        if extra == 0 {
            return Ok(());
        }
        let mut state = self.inner.state.lock();
        if state.transfers.saturating_add(extra) > MAX_TRANSFER_TOTAL {
            return Err(exhausted());
        }
        let floor = ORDINARY_FLOOR;
        Space(self.inner.clone()).available(&state, extra, floor)?;
        // Retain the full reservation through descriptor close and unlink.
        // Filesystem free space also accounts for any uncertain physical bytes.
        self.bytes += extra;
        state.transfers += extra;
        state.pending += extra;
        Ok(())
    }
    pub fn account(&mut self, metadata: &std::fs::Metadata) {
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            let allocated = metadata.blocks().saturating_mul(512).min(self.bytes);
            let new = allocated.saturating_sub(self.allocated);
            self.inner.state.lock().pending -= new;
            self.allocated += new;
        }
        #[cfg(not(unix))]
        let _ = metadata;
    }
}

impl Drop for Reservation {
    fn drop(&mut self) {
        if self.uncertain {
            return;
        }
        let mut state = self.inner.state.lock();
        if let Some(ticket) = self.slot {
            state.close(ticket);
        } else {
            state.pending -= self.bytes;
        }
        if self.covered {
            state.covered -= self.bytes;
        }
    }
}

impl Reservation {
    pub fn ticket(&self) -> Option<(StreamId, Uuid)> {
        self.slot
    }

    pub fn hold_until_reconciled(&mut self, hold: bool) {
        self.uncertain = hold;
    }
}

impl Drop for Transfer {
    fn drop(&mut self) {
        let mut state = self.inner.state.lock();
        state.pending -= self.bytes - self.allocated;
        state.transfers -= self.bytes;
        state.sessions -= 1;
    }
}

impl Ledger {
    fn close(&mut self, ticket: (StreamId, Uuid)) {
        if let Some((bytes, slots)) = self.tickets.remove(&ticket) {
            self.pending -= bytes;
            if slots != 0 {
                *self.slots.get_mut(&ticket.0).unwrap() -= slots;
            }
            if self.slots.get(&ticket.0) == Some(&0) {
                self.slots.remove(&ticket.0);
            }
        }
    }
}

fn exhausted() -> io::Error {
    io::Error::new(
        io::ErrorKind::StorageFull,
        "keeper volume admission exhausted",
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[tokio::test]
    async fn full_ordinary_and_bulk_bytes_leave_the_idle_maintenance_and_control_floors() {
        let root = tempfile::tempdir().unwrap();
        let space = Space::new(root.path().to_owned()).unwrap();
        let measured = 704 * MIB;
        space.set_available(measured);

        let mut incoming = space.transfer().unwrap();
        let mut outgoing = space.transfer().unwrap();
        incoming.grow(MAX_TRANSFER_FILE).unwrap();
        outgoing.grow(MAX_TRANSFER_FILE).unwrap();
        assert!(
            space
                .transfer()
                .unwrap()
                .grow(space.allocation_unit())
                .is_err()
        );
        assert!(incoming.grow(MAX_TRANSFER_FILE + 1).is_err());

        let floor = ORDINARY_FLOOR;
        let ordinary = space
            .reserve(measured - MAX_TRANSFER_TOTAL - floor)
            .unwrap();
        assert!(space.reserve(space.allocation_unit()).is_err());
        let scratch = space.scratch(12 * MIB).await.unwrap();
        let covered = space.covered(WAL_METADATA_BYTES).unwrap();
        // Scratch and covered work progress while bulk is full. Protocol
        // still has enough protected headroom for a vote in the next round.
        let vote = space.protocol(WAL_METADATA_BYTES).unwrap();

        // Simulate blocks from an interrupted or unlinked-open allocation.
        // Canceling a virtual reservation cannot credit those physical blocks.
        let ordinary_bytes = ordinary.bytes;
        space.set_available(measured - space.allocation_unit());
        drop(ordinary);
        drop(scratch);
        drop(covered);
        drop(vote);
        assert!(space.reserve(ordinary_bytes).is_err());
        space.set_available(measured);
        assert!(space.reserve(ordinary_bytes).is_ok());
    }

    #[test]
    fn concurrent_tickets_share_the_suffix_limit_and_finish_exactly_once() {
        let root = tempfile::tempdir().unwrap();
        let space = Space::new(root.path().to_owned()).unwrap();
        let scope = StreamId(4);
        let slots = Arc::new(AtomicUsize::new(0));
        let ticket = Uuid::new_v4();
        let first = space
            .ordinary_slot(scope, ticket, 2, 4096, || slots.load(Ordering::Relaxed))
            .unwrap();
        let other = space.clone();
        let occupied = slots.clone();
        let second = std::thread::spawn(move || {
            other.ordinary_slot(scope, Uuid::new_v4(), 2, 4096, || {
                occupied.load(Ordering::Relaxed)
            })
        })
        .join()
        .unwrap()
        .unwrap();
        assert!(matches!(
            space.ordinary_slot(scope, Uuid::new_v4(), 2, 4096, || 0),
            Err(Admission::FullSuffix)
        ));
        std::thread::scope(|threads| {
            threads.spawn(move || drop(first));
            threads
                .spawn(|| space.settle(&[(scope, ticket)], || slots.store(1, Ordering::Relaxed)));
        });
        space.settle(&[(scope, ticket)], || {});
        assert_eq!(space.0.state.lock().pending, 4096);
        assert!(matches!(
            space.ordinary_slot(scope, Uuid::new_v4(), 2, 4096, || 1),
            Err(Admission::FullSuffix)
        ));
        drop(second);
        assert_eq!(space.0.state.lock().pending, 0);
        assert!(
            space
                .ordinary_slot(scope, Uuid::new_v4(), 2, 4096, || 1)
                .is_ok()
        );
    }
}
