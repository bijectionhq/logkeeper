# Study 11 · Placement ownership and writer identity

## Question

Can a replica group hand off a stream while the RTDB directory is down, without changing the stream's authorized writer or carrying a superseded grant forward?

## Sources and comparisons

Use S03, S07, L02 and P07 from the [requirements](../requirements.md), plus the [portable handoff](../02-handoff/report.md), [destination reservation](../06-generations/report.md), and [reference kernel](../07-reference/Kernel.lean).
RTDB supplies writer epochs in its `LogService` contract and expects installed holders to keep working during directory outages under `StaticStability`.

Compare requiring a new directory grant after every source seal with carrying the current RTDB holder and writer epoch from the seal.
In the carrying design, activation changes the placement only.
A holder replacement is an independent fence at the current owner and requires a higher authenticated writer epoch.

## Bounded model

One stream moves once from one group to another.
Before seal, the source can replace its current holder with a higher epoch.
The original move preparation can therefore contain a stale observation.
Directory loss is permanent for the remainder of an execution.
Append requests can be staged and delivered after a writer change or move.
A commit checks holder, writer epoch, placement and expected LSN at the authority.
Histories of up to two and three records use two distinct payloads.

Check writer binding at activation, exact cut preservation, and append admission.
Use weak fairness for seal, activation, and any grant issue that stays enabled.
Test eventual completion after durable preparation and witness an append during directory loss after the source holder has changed.

## General refinement

Model group-local serving rows, durable destination slots and authentic seal delivery.
A certificate is created by a local source seal and installs at the exact target with its matching live nonce.
The install consumes that nonce.
Old authentic certificates may be delivered at any time.
Concrete group-local appends and other stream actions use the reference kernel when they already have local authority.

The refinement relation connects every world to a logical stream state and a proof-only pending certificate.
It requires retired certificates to have spent nonces.
Prove that a concrete step stutters or takes an actual step of the imported Lean kernel.
Derive finite trace refinement, single serving ownership, monotone observed history, valid replay and retention bounds at any serving group, and terminal retirement.
Construct a two-step handoff from a prepared destination and prove that prior placement credentials cannot append.

The Lean model abstracts durable quorum operations, cryptographic attestations, target installation of the exact snapshot, and preparation and cancellation authorization.
It includes arbitrary groups and repeated moves over all finite traces.
Its certificate list describes possible authentic deliveries and imposes no runtime lookup.
The timeout and pending-quota rules remain separate.

## Rules

Use the pinned TLC runner for both candidates at both bounds, with weakening controls before baselines.
Use Lean 4.35.0 and build the existing kernel and reservation modules from their current sources.
Require that leaving the source writable or changing the holder during activation fail specifically at the forward simulation proof.
See the [report](report.md) for the outcomes.
