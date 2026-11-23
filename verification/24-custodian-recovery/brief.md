# Study 24 · Physical custodian recovery

## Question

Which committed custody state must a physical custodian recover after restart or voter replacement, and can an already authorized provider operation continue while its coordinator is down?

## Sources

Use [quorum membership](../12-quorum-membership/report.md), [independent physical borrows](../14-read-custody/report.md), [checkpoint recovery](../16-checkpoint-reconstruction/report.md), [registration recovery](../20-registration-recovery/report.md), [custody channels](../21-custody-channel-lifecycle/report.md), and [issuer handoff](../23-custody-authority-handoff/report.md).
RTDB Multi at `fc6da3a4a3` binds journal identity to durable media and votes to distinct verified journals.
Its hosted retirement rules bind erasure to an exact physical version and inventory evidence.
This study applies the existing ordered journal contract to the custodian's own metadata.

## Model and properties

TLC models three active voters across three zones, one replacement, one AZ loss, one restart, one outstanding acquisition and one scoped physical borrow.
It records exact-image coverage, distinct channel issuance and refusal state, and an independent provider delete and observation.
Check metadata recovery, refusal after an acknowledged cancellation, preservation of live grants and borrows, and durable authorization before provider effects.
Check restart when a current recovery quorum is available and completion of a fenced disposition when provider and quorum access stabilize.

Lean composes exact recovery majorities, certified base and tail replay, channel lifecycle decisions, and physical version retirement.
The logical state can be materialized as a committed image or recovered by replay from a certified checkpoint.

## Comparison

Compare complete-image recovery with projections that forget grants, borrows, issued handles, spent serials, the receiver floor, or the deletion fence.
Check negative controls for incomplete new membership, an unfenced old membership, cancellation that fails to fence an empty grant slot, and external deletion dispatched before a committed fence.
Exercise a stale acquire after compaction and restart, a provider delete that lands during coordinator downtime, and replacement with a live grant and physical borrow.

The model assumes the previous journal consensus and identity boundary, authentic provider evidence and immutable scoped version keys.
It abstracts media framing and codec implementation, leader election, concurrent provider requests across versions, and real storage API behavior.

## Reproduction

Use Python 3.13, TLC 2.19 with Java 21.0.13+9, and Lean 4.35.0.
Run `python3 verification/24-custodian-recovery/run.py` from the checkout with paths as in the [verification index](../README.md).
The study-local ignored results directory holds the exact commands, traces and proof diagnostics.
See the [report](report.md) for outcomes and limits.
