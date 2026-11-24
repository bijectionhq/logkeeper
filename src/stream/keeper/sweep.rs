//! Drive replacement for each nominated idle stream.

use crate::stream::{
    proposer::{driver, sweep::Replacement},
    wire::{Epoch, KeeperId, StreamId, Transport},
};

pub use crate::stream::proposer::sweep::{Sweep, SweepError};

/// Sweep each nominated idle stream independently. The learner completes only
/// after both surviving members have installed the new ensemble.
pub async fn sweep_idle(
    transport: &dyn Transport,
    plans: impl IntoIterator<Item = Sweep>,
) -> Vec<(StreamId, Result<(), SweepError>)> {
    let mut outcomes = Vec::new();
    for plan in plans {
        let operation = Replacement::new(plan, transport.identity().clone());
        outcomes.push((plan.stream, driver::run(transport, operation, None).await));
    }
    outcomes
}

impl Sweep {
    /// Keep the plan to retry this proposal after an uncertain result.
    pub fn new(
        stream: StreamId,
        ensemble: [KeeperId; 3],
        survivors: [KeeperId; 2],
        learner: KeeperId,
        epoch: Epoch,
    ) -> Self {
        Self {
            stream,
            ensemble,
            survivors,
            learner,
            epoch,
            proposal: uuid::Uuid::new_v4().as_u128(),
        }
    }
}
