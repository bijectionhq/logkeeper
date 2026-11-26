//! Deterministic PRNG and per-lane network fault injector for consensus tests.

use std::{
    collections::{BTreeMap, HashSet},
    sync::Arc,
    time::Duration,
};

use parking_lot::Mutex;
use uuid::Uuid;

use super::super::network::{Lane, RpcFault, TransportFilter};

/// SplitMix64 PRNG so every seed produces a reproducible workload and fault sequence.
#[derive(Clone, Debug)]
pub(super) struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(seed ^ 0x9e37_79b9_7f4a_7c15)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    pub fn range(&mut self, upper: usize) -> usize {
        if upper <= 1 {
            0
        } else {
            (self.next_u64() as usize) % upper
        }
    }

    pub fn range_u64(&mut self, low: u64, high_exclusive: u64) -> u64 {
        if high_exclusive <= low {
            low
        } else {
            low + (self.next_u64() % (high_exclusive - low))
        }
    }

    pub fn chance(&mut self, num: u32, den: u32) -> bool {
        if num == 0 || den == 0 {
            return false;
        }
        if num >= den {
            return true;
        }
        (self.next_u64() % u64::from(den)) < u64::from(num)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum LaneKey {
    Application,
    Control,
    Replication,
    Bulk,
}

impl From<Lane> for LaneKey {
    fn from(lane: Lane) -> Self {
        match lane {
            Lane::Application => Self::Application,
            Lane::Control => Self::Control,
            Lane::Replication => Self::Replication,
            Lane::Bulk => Self::Bulk,
        }
    }
}

impl LaneKey {
    pub const PEER: [Self; 3] = [Self::Control, Self::Replication, Self::Bulk];

    fn idx(self) -> usize {
        match self {
            Self::Application => 0,
            Self::Control => 1,
            Self::Replication => 2,
            Self::Bulk => 3,
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub(super) struct LaneFaults {
    /// Percentage [0..=100] of requests dropped before delivery.
    pub drop_pct: u32,
    /// Percentage [0..=100] of requests delivered whose reply is then dropped.
    pub drop_reply_pct: u32,
    /// Percentage [0..=100] of idempotent peer requests duplicated.
    pub duplicate_pct: u32,
    /// Maximum random delay in milliseconds injected before delivery.
    pub max_delay_ms: u64,
}

pub(super) type Coverage = BTreeMap<&'static str, usize>;

struct State {
    rng: Rng,
    /// Directed blocked links `(from, to, lane)`.
    blocked: HashSet<(Uuid, Uuid, LaneKey)>,
    /// Per-lane probabilistic faults.
    lanes: [LaneFaults; 4],
    /// Event coverage counts for verifying fault diversity.
    coverage: Coverage,
}

/// Shared network fault controller wired into every keeper and client `Rpc`.
#[derive(Clone)]
pub(super) struct FaultNetwork {
    inner: Arc<Mutex<State>>,
}

impl FaultNetwork {
    pub fn new(seed: u64) -> Self {
        Self {
            inner: Arc::new(Mutex::new(State {
                rng: Rng::new(seed ^ 0x517c_c1b7_2722_0a95),
                blocked: HashSet::new(),
                lanes: [LaneFaults::default(); 4],
                coverage: BTreeMap::new(),
            })),
        }
    }

    pub fn filter(&self) -> TransportFilter {
        let inner = self.inner.clone();
        Arc::new(move |from, to, lane| {
            let key = LaneKey::from(lane);
            let mut state = inner.lock();
            if state.blocked.contains(&(from, to, key)) {
                state.hit(match key {
                    LaneKey::Application => "partition:application",
                    LaneKey::Control => "partition:control",
                    LaneKey::Replication => "partition:replication",
                    LaneKey::Bulk => "partition:bulk",
                });
                return RpcFault::Drop(Duration::ZERO);
            }
            let cfg = state.lanes[key.idx()];
            if cfg.drop_pct > 0 && state.rng.chance(cfg.drop_pct, 100) {
                state.hit("rpc:drop");
                return RpcFault::Drop(Duration::ZERO);
            }
            if cfg.drop_reply_pct > 0 && state.rng.chance(cfg.drop_reply_pct, 100) {
                state.hit("rpc:drop_reply");
                return RpcFault::DropReply(Duration::ZERO);
            }
            if cfg.duplicate_pct > 0
                && !matches!(key, LaneKey::Application)
                && state.rng.chance(cfg.duplicate_pct, 100)
            {
                let delay = Duration::from_millis(state.rng.range_u64(1, 25));
                state.hit("rpc:duplicate");
                return RpcFault::Duplicate(delay);
            }
            if cfg.max_delay_ms > 0 && state.rng.chance(1, 2) {
                let delay = Duration::from_millis(state.rng.range_u64(1, cfg.max_delay_ms + 1));
                state.hit("rpc:delay");
                return RpcFault::Delay(delay);
            }
            RpcFault::Allow
        })
    }

    /// Blocks traffic symmetrically between `left` and `right` on `lanes`.
    pub fn partition_symmetric(&self, left: &[Uuid], right: &[Uuid], lanes: &[LaneKey]) {
        let mut state = self.inner.lock();
        for &a in left {
            for &b in right {
                if a == b {
                    continue;
                }
                for &lane in lanes {
                    state.blocked.insert((a, b, lane));
                    state.blocked.insert((b, a, lane));
                }
            }
        }
        state.hit("fault:partition_symmetric");
    }

    /// Blocks directed traffic `from -> to` on `lanes`, leaving `to -> from` intact.
    pub fn partition_asymmetric(&self, from: Uuid, to: Uuid, lanes: &[LaneKey]) {
        let mut state = self.inner.lock();
        for &lane in lanes {
            state.blocked.insert((from, to, lane));
        }
        state.hit("fault:partition_asymmetric");
    }

    /// Installs probabilistic drop/delay/reply-drop/duplicate settings on `lane`.
    pub fn set_lane_faults(&self, lane: LaneKey, faults: LaneFaults) {
        let mut state = self.inner.lock();
        state.lanes[lane.idx()] = faults;
    }

    /// Clears all partitions and probabilistic network faults.
    pub fn heal_all(&self) {
        let mut state = self.inner.lock();
        state.blocked.clear();
        state.lanes = [LaneFaults::default(); 4];
    }

    pub fn hit(&self, event: &'static str) {
        self.inner.lock().hit(event);
    }

    pub fn coverage(&self) -> Coverage {
        self.inner.lock().coverage.clone()
    }
}

impl State {
    fn hit(&mut self, event: &'static str) {
        *self.coverage.entry(event).or_default() += 1;
    }
}
