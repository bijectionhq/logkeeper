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
use crate::stream::consensus::decisions::{admits_body, admits_control, body_charge};

#[cfg(test)]
const MIB: usize = 1024 * 1024;
const RECEIVER_SOCKETS: usize = 32;
const SENDER_SOCKETS: usize = 4;
const IDLE_CONTROL_SOCKETS: usize = 64;

fn busy() -> io::Error {
    io::Error::new(io::ErrorKind::WouldBlock, "replication receiver is busy")
}

#[derive(Default)]
pub(super) struct ReplicationIngress(Mutex<Load>);

#[derive(Default)]
struct Load {
    total: Meter,
    senders: BTreeMap<NodeId, Meter>,
}

#[derive(Default)]
struct Meter {
    sockets: usize,
    frames: usize,
    bytes: usize,
}

pub(super) struct Charge {
    ingress: Arc<ReplicationIngress>,
    sender: NodeId,
    frame_bytes: Option<usize>,
}

impl ReplicationIngress {
    pub fn socket(self: &Arc<Self>, sender: NodeId) -> io::Result<Charge> {
        let mut load = self.0.lock();
        if load.total.sockets >= RECEIVER_SOCKETS
            || load
                .senders
                .get(&sender)
                .is_some_and(|from| from.sockets >= SENDER_SOCKETS)
        {
            return Err(busy());
        }
        load.total.sockets += 1;
        load.senders.entry(sender).or_default().sockets += 1;
        Ok(Charge {
            ingress: self.clone(),
            sender,
            frame_bytes: None,
        })
    }

    pub fn body(self: &Arc<Self>, sender: NodeId, size: usize) -> io::Result<Charge> {
        // Includes the encoded body, decoding and pieces shared with Raft,
        // and one encoded extent buffer during WAL preparation.
        let bytes = body_charge(size);
        let mut load = self.0.lock();
        let (sender_frames, sender_bytes) = load
            .senders
            .get(&sender)
            .map_or((0, 0), |from| (from.frames, from.bytes));
        if !admits_body(
            load.total.frames,
            load.total.bytes,
            sender_frames,
            sender_bytes,
            bytes,
        ) {
            return Err(busy());
        }
        load.total.frames += 1;
        load.total.bytes += bytes;
        let from = load.senders.entry(sender).or_default();
        from.frames += 1;
        from.bytes += bytes;
        Ok(Charge {
            ingress: self.clone(),
            sender,
            frame_bytes: Some(bytes),
        })
    }

    #[cfg(test)]
    pub fn frames(&self, sender: Option<NodeId>) -> usize {
        let load = self.0.lock();
        match sender {
            Some(sender) => load.senders.get(&sender).map_or(0, |meter| meter.frames),
            None => load.total.frames,
        }
    }
}

impl Drop for Charge {
    fn drop(&mut self) {
        let mut load = self.ingress.0.lock();
        let Load { total, senders } = &mut *load;
        let sender = senders.get_mut(&self.sender).unwrap();
        for meter in [total, &mut *sender] {
            if let Some(bytes) = self.frame_bytes {
                meter.frames -= 1;
                meter.bytes -= bytes;
            } else {
                meter.sockets -= 1;
            }
        }
        if sender.sockets == 0 && sender.frames == 0 {
            senders.remove(&self.sender);
        }
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

pub(super) struct ControlWork<'a> {
    control: &'a Control,
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

    /// Admits one control frame, waiting up to `CONTROL_ADMISSION_WAIT` for
    /// a slot under the same limits.
    pub async fn admit_waiting(&self, sender: NodeId) -> io::Result<ControlWork<'_>> {
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

    pub fn admit(&self, sender: NodeId) -> io::Result<ControlWork<'_>> {
        let mut work = self.work.lock();
        if !admits_control(work.0, work.1.get(&sender).copied().unwrap_or(0)) {
            #[cfg(test)]
            CONTROL_REFUSED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            return Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                "control work is full",
            ));
        }
        work.0 += 1;
        *work.1.entry(sender).or_default() += 1;
        Ok(ControlWork {
            control: self,
            sender,
        })
    }
}

impl Drop for IdleControlGuard<'_> {
    fn drop(&mut self) {
        self.idle.idle.lock().retain(|(id, _)| *id != self.id);
    }
}

impl Drop for ControlWork<'_> {
    fn drop(&mut self) {
        let mut work = self.control.work.lock();
        work.0 -= 1;
        let count = work.1.get_mut(&self.sender).unwrap();
        *count -= 1;
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

    #[test]
    fn one_sender_cannot_spend_the_shares_of_others_and_release_is_exact() {
        let ingress = Arc::new(ReplicationIngress::default());
        // Each frame is charged at four times its size plus 64 KiB.
        let frame = 5 * MIB;
        let held = (0..SENDER_FRAMES)
            .map(|_| ingress.body(1, frame).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            ingress.body(1, 1).err().unwrap().kind(),
            io::ErrorKind::WouldBlock
        );
        // A sender under its frame count still cannot pass its byte share.
        let large = ingress.body(2, 20 * MIB).unwrap();
        assert!(ingress.body(2, 5 * MIB).is_err());
        assert!(
            ingress.body(3, 30 * MIB).is_err(),
            "one frame above a sender share"
        );
        let others = (3..=(RECEIVER_FRAMES - SENDER_FRAMES))
            .map(|sender| ingress.body(sender as NodeId, 1024).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(ingress.frames(None), RECEIVER_FRAMES - 1);
        let last = ingress.body(99, 1024).unwrap();
        assert!(ingress.body(100, 1024).is_err(), "receiver frame limit");
        drop(last);
        let entered = ingress.body(100, 1024).unwrap();
        drop((held, large, others, entered));
        assert_eq!(ingress.frames(None), 0);
        assert!(ingress.0.lock().senders.is_empty());
        assert_eq!(ingress.0.lock().total.bytes, 0);

        let sockets = (0..SENDER_SOCKETS)
            .map(|_| ingress.socket(7).unwrap())
            .collect::<Vec<_>>();
        assert!(ingress.socket(7).is_err());
        let body = ingress.body(7, 1024).unwrap();
        drop(sockets);
        assert_eq!(ingress.frames(Some(7)), 1);
        drop(body);
        assert!(ingress.0.lock().senders.is_empty());
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
        assert!(ingress.0.lock().total.bytes <= RECEIVER_BYTES);
        drop(held);
        assert!(ingress.body(fit as NodeId, per_frame).is_ok());
    }

    #[test]
    fn control_work_is_capped_per_sender_and_idle_waits_are_evicted_oldest_first() {
        let control = Control::default();
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
