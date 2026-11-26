use std::{
    collections::{BTreeMap, VecDeque},
    io,
    sync::Arc,
};

use parking_lot::Mutex;
use tokio_util::sync::CancellationToken;
use uuid::Uuid;

use super::NodeId;

#[cfg(test)]
use crate::stream::consensus::decisions::{
    CONTROL_PER_SENDER, MAX_CONTROL_WORK, RECEIVER_BYTES, RECEIVER_FRAMES, SENDER_FRAMES,
};
use crate::stream::consensus::decisions::{
    admits_body, admits_control, body_charge, meter_admit, meter_release,
};

#[cfg(test)]
const MIB: usize = 1024 * 1024;
const IDLE_CONTROL_SOCKETS: usize = 64;

#[cfg(test)]
fn busy() -> io::Error {
    io::Error::new(io::ErrorKind::WouldBlock, "replication receiver is busy")
}

/// Replication bytes and messages in flight at one receiver, in total and
/// per sender. A frame here is one peer message, so a sender's share is the
/// same whether its messages arrive on one connection or many.
#[derive(Default)]
pub(super) struct ReplicationIngress {
    load: Mutex<Load>,
    freed: tokio::sync::Notify,
}

#[derive(Default)]
struct Load {
    total: Meter,
    senders: BTreeMap<NodeId, Meter>,
}

#[derive(Default)]
struct Meter {
    frames: usize,
    bytes: usize,
}

pub(super) struct Charge {
    ingress: Arc<ReplicationIngress>,
    sender: NodeId,
    bytes: usize,
}

impl Load {
    fn admit(&mut self, sender: NodeId, bytes: usize) -> bool {
        let (sender_frames, sender_bytes) = self
            .senders
            .get(&sender)
            .map_or((0, 0), |from| (from.frames, from.bytes));
        if !admits_body(
            self.total.frames,
            self.total.bytes,
            sender_frames,
            sender_bytes,
            bytes,
        ) {
            return false;
        }
        (self.total.frames, self.total.bytes) =
            meter_admit(self.total.frames, self.total.bytes, bytes);
        let from = self.senders.entry(sender).or_default();
        (from.frames, from.bytes) = meter_admit(from.frames, from.bytes, bytes);
        true
    }

    fn release(&mut self, sender: NodeId, bytes: usize) {
        let Load { total, senders } = self;
        let from = senders.get_mut(&sender).unwrap();
        for meter in [total, &mut *from] {
            (meter.frames, meter.bytes) = meter_release(meter.frames, meter.bytes, bytes);
        }
        if from.frames == 0 {
            senders.remove(&sender);
        }
    }
}

impl ReplicationIngress {
    /// Admits one message of `size` encoded bytes, or refuses it at once.
    #[cfg(test)]
    pub fn body(self: &Arc<Self>, sender: NodeId, size: usize) -> io::Result<Charge> {
        // Includes the encoded body, decoding and pieces shared with Raft,
        // and one encoded extent buffer during WAL preparation.
        let bytes = body_charge(size);
        if !self.load.lock().admit(sender, bytes) {
            return Err(busy());
        }
        Ok(self.charge(sender, bytes))
    }

    /// Admits a batch frame of `size` bytes before its body is read, as one
    /// frame, waiting while the sender or the receiver is full. The wait
    /// stalls only this sender's connection.
    pub async fn read(self: &Arc<Self>, sender: NodeId, size: usize) -> Charge {
        let bytes = body_charge(size);
        loop {
            let freed = self.freed.notified();
            tokio::pin!(freed);
            freed.as_mut().enable();
            if self.load.lock().admit(sender, bytes) {
                return self.charge(sender, bytes);
            }
            freed.await;
        }
    }

    /// Exchanges the charge of a read batch for one charge per message, in
    /// order, under one lock. Messages past the budgets get `None` and are
    /// answered busy.
    pub fn split(self: &Arc<Self>, read: Charge, sizes: &[usize]) -> Vec<Option<Charge>> {
        let mut load = self.load.lock();
        load.release(read.sender, read.bytes);
        let sender = read.sender;
        std::mem::forget(read);
        let charges = sizes
            .iter()
            .map(|size| {
                let bytes = body_charge(*size);
                load.admit(sender, bytes)
                    .then(|| self.charge(sender, bytes))
            })
            .collect();
        drop(load);
        self.freed.notify_waiters();
        charges
    }

    fn charge(self: &Arc<Self>, sender: NodeId, bytes: usize) -> Charge {
        Charge {
            ingress: self.clone(),
            sender,
            bytes,
        }
    }

    #[cfg(test)]
    pub fn frames(&self, sender: Option<NodeId>) -> usize {
        let load = self.load.lock();
        match sender {
            Some(sender) => load.senders.get(&sender).map_or(0, |meter| meter.frames),
            None => load.total.frames,
        }
    }
}

impl Drop for Charge {
    fn drop(&mut self) {
        self.ingress.load.lock().release(self.sender, self.bytes);
        self.ingress.freed.notify_waiters();
    }
}

#[derive(Default)]
pub(super) struct Control {
    idle: Mutex<VecDeque<(Uuid, CancellationToken)>>,
    work: Mutex<(usize, BTreeMap<NodeId, usize>)>,
    freed: tokio::sync::Notify,
}

/// How long a control frame over its sender's share waits for a slot before
/// the keeper refuses it. Many streams between the same keepers send their
/// heartbeats together; a short wait absorbs that burst instead of resetting
/// the connections.
const CONTROL_ADMISSION_WAIT: std::time::Duration = std::time::Duration::from_millis(100);

/// Control requests refused by `Control::admit`, across all keepers in a test
/// process.
#[cfg(test)]
pub(super) static CONTROL_REFUSED: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

pub(super) struct IdleControlGuard<'a> {
    idle: &'a Control,
    id: Uuid,
    pub cancelled: CancellationToken,
}

pub(super) struct ControlWork {
    control: Arc<Control>,
    sender: NodeId,
}

impl Control {
    pub fn wait_for_header(&self) -> IdleControlGuard<'_> {
        let mut idle = self.idle.lock();
        if idle.len() == IDLE_CONTROL_SOCKETS {
            let (_, evicted) = idle.pop_front().unwrap();
            evicted.cancel();
        }
        let id = Uuid::new_v4();
        let cancelled = CancellationToken::new();
        idle.push_back((id, cancelled.clone()));
        IdleControlGuard {
            idle: self,
            id,
            cancelled,
        }
    }

    /// Admits one control message, waiting up to `CONTROL_ADMISSION_WAIT`
    /// for a slot under the same limits.
    pub async fn admit_waiting(self: &Arc<Self>, sender: NodeId) -> io::Result<ControlWork> {
        let deadline = tokio::time::Instant::now() + CONTROL_ADMISSION_WAIT;
        loop {
            let freed = self.freed.notified();
            tokio::pin!(freed);
            freed.as_mut().enable();
            match self.admit(sender) {
                Ok(work) => return Ok(work),
                Err(refused) => {
                    if tokio::time::timeout_at(deadline, freed).await.is_err() {
                        return Err(refused);
                    }
                }
            }
        }
    }

    pub fn admit(self: &Arc<Self>, sender: NodeId) -> io::Result<ControlWork> {
        let mut work = self.work.lock();
        let from = work.1.get(&sender).copied().unwrap_or(0);
        if !admits_control(work.0, from) {
            #[cfg(test)]
            CONTROL_REFUSED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            return Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                "control work is full",
            ));
        }
        work.0 = meter_admit(work.0, 0, 0).0;
        work.1.insert(sender, meter_admit(from, 0, 0).0);
        Ok(ControlWork {
            control: self.clone(),
            sender,
        })
    }
}

impl Drop for IdleControlGuard<'_> {
    fn drop(&mut self) {
        self.idle.idle.lock().retain(|(id, _)| *id != self.id);
    }
}

impl Drop for ControlWork {
    fn drop(&mut self) {
        let mut work = self.control.work.lock();
        work.0 = meter_release(work.0, 0, 0).0;
        let count = work.1.get_mut(&self.sender).unwrap();
        *count = meter_release(*count, 0, 0).0;
        if *count == 0 {
            work.1.remove(&self.sender);
        }
        drop(work);
        self.control.freed.notify_waiters();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stream::consensus::decisions::SENDER_BYTES;

    fn empty(ingress: &ReplicationIngress) -> bool {
        let load = ingress.load.lock();
        load.senders.is_empty() && load.total.frames == 0 && load.total.bytes == 0
    }

    #[test]
    fn one_sender_cannot_spend_the_shares_of_others_and_release_is_exact() {
        let ingress = Arc::new(ReplicationIngress::default());
        // Each message is charged at four times its size plus 64 KiB, so a
        // sender's full message count fits inside its byte share.
        let message = 64 * 1024;
        assert!(SENDER_FRAMES * (4 * message + 64 * 1024) <= SENDER_BYTES);
        let held = (0..SENDER_FRAMES)
            .map(|_| ingress.body(1, message).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            ingress.body(1, 1).err().unwrap().kind(),
            io::ErrorKind::WouldBlock
        );
        // A sender under its message count still cannot pass its byte share.
        let large = ingress.body(2, 20 * MIB).unwrap();
        assert!(ingress.body(2, 5 * MIB).is_err());
        assert!(
            ingress.body(3, 30 * MIB).is_err(),
            "one message above a sender share"
        );
        // The others still have every slot one sender cannot take.
        let others = (0..RECEIVER_FRAMES - SENDER_FRAMES - 2)
            .map(|index| ingress.body(3 + (index % 2) as NodeId, 1024).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(ingress.frames(None), RECEIVER_FRAMES - 1);
        let last = ingress.body(99, 1024).unwrap();
        assert!(ingress.body(100, 1024).is_err(), "receiver frame limit");
        drop(last);
        let entered = ingress.body(100, 1024).unwrap();
        drop((held, large, others, entered));
        assert!(empty(&ingress));
    }

    #[test]
    fn receiver_bytes_bound_concurrent_senders() {
        let ingress = Arc::new(ReplicationIngress::default());
        let per_frame = 18 * MIB;
        let charged = per_frame * 4 + 64 * 1024;
        let fit = RECEIVER_BYTES / charged;
        let held = (0..fit as NodeId)
            .map(|sender| ingress.body(sender, per_frame).unwrap())
            .collect::<Vec<_>>();
        assert!(ingress.body(fit as NodeId, per_frame).is_err());
        assert!(ingress.load.lock().total.bytes <= RECEIVER_BYTES);
        drop(held);
        assert!(ingress.body(fit as NodeId, per_frame).is_ok());
    }

    #[tokio::test]
    async fn a_batch_read_waits_for_its_sender_and_splits_into_exact_message_charges() {
        let ingress = Arc::new(ReplicationIngress::default());
        let read = ingress.read(1, 18 * MIB).await;
        assert_eq!(ingress.frames(Some(1)), 1);
        // Messages past the sender's share are answered busy.
        let charges = ingress.split(read, &[1024; SENDER_FRAMES + 1]);
        assert!(charges[..SENDER_FRAMES].iter().all(Option::is_some));
        assert!(charges[SENDER_FRAMES].is_none());
        assert_eq!(ingress.frames(Some(1)), SENDER_FRAMES);
        assert_eq!(
            ingress.load.lock().total.bytes,
            SENDER_FRAMES * (4 * 1024 + 64 * 1024)
        );
        drop(charges);
        assert!(empty(&ingress));

        // A read past the sender's bytes waits for its own messages to
        // finish, and a read from another sender does not.
        let held = ingress.body(2, 20 * MIB).unwrap();
        let waiting = tokio::spawn({
            let ingress = ingress.clone();
            async move { ingress.read(2, 18 * MIB).await }
        });
        tokio::time::sleep(std::time::Duration::from_millis(50)).await;
        assert!(!waiting.is_finished());
        let other = ingress.read(3, 18 * MIB).await;
        drop(held);
        let read = waiting.await.unwrap();
        drop((read, other));
        assert!(empty(&ingress));
    }

    #[test]
    fn control_work_is_capped_per_sender_and_idle_waits_are_evicted_oldest_first() {
        let control = Arc::new(Control::default());
        let first = (0..CONTROL_PER_SENDER)
            .map(|_| control.admit(1).unwrap())
            .collect::<Vec<_>>();
        assert!(control.admit(1).is_err());
        let rest = (2..)
            .take(MAX_CONTROL_WORK - CONTROL_PER_SENDER)
            .map(|sender| control.admit(sender).unwrap())
            .collect::<Vec<_>>();
        assert!(control.admit(500).is_err(), "aggregate control work");
        drop(first);
        assert!(control.admit(1).is_ok());
        drop(rest);
        assert_eq!(control.work.lock().0, 0);
        assert!(control.work.lock().1.is_empty());

        let waiting = (0..IDLE_CONTROL_SOCKETS)
            .map(|_| control.wait_for_header())
            .collect::<Vec<_>>();
        assert!(waiting.iter().all(|idle| !idle.cancelled.is_cancelled()));
        let newest = control.wait_for_header();
        assert!(waiting[0].cancelled.is_cancelled());
        assert!(
            waiting[1..]
                .iter()
                .all(|idle| !idle.cancelled.is_cancelled())
        );
        assert!(!newest.cancelled.is_cancelled());
        drop(waiting);
        drop(newest);
        assert!(control.idle.lock().is_empty());
    }
}
