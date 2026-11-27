# Logkeeper Lean interface

Use `Logkeeper.Protocol` for typed data and decision cuts, durable chosen
prefixes, exact append receipts, and trim charges from the chosen application
interval. The quorum module incorporates the reference, quorum membership, and
durable prefix studies. A concrete caller supplies the durable voter trace and
relates the ledger to the real prepare and accept exchanges. The transfer theorem connects independent cohorts by the exact predecessor image decoded at installation. The byte-level refinement of the signed repair package is a separate obligation.

`held_record_survives_trim_and_transfer` combines quorum prefix agreement and
live-hold trim safety. A held application index still names the original
append after the verified logical transfer, including when the successor
orders control entries between appends. The concrete image decoder and
installer must supply the selected histories and the original live hold.

This package has source-level model obligations. A journal installation must
still discharge codec, provider, authentication and crash durability premises.
Pin dependants to the exact Logkeeper revision and the same Lean toolchain.

`Logkeeper.SelectionFence` starts each acknowledged promise or vote with
two durable images and models later complete writes, detectable slot tears,
and restart. It applies Studies 25 and 26's valid-image selection rule and
Study 106's exact sealed basis rule to ranked recovery majorities.
The theorem ranges over arbitrary journal histories, finite local traces,
strict majorities and finite repair chains. The reachability witness uses
three voters, two writes and one selected-slot tear.
The model assumes checked images, authenticated correct coordinators,
and exact repair and compaction bases. It abstracts disk barriers, wire
signatures and encoding to their inspected implementations.

The selection reference also gives the exact selector, the two-sync reply
gate and rotation evidence from distinct members of a strict configured
majority. Each attestation names the selected index and both physical
descriptors of the same ballot and prefix. The production correspondences
are in [mirrored voter media](../verus/mirrored_voter_media/README.md)
and [rotation slot evidence](../verus/rotation_slot_evidence/README.md).

Run `python3 run_selection_fence.py` from this directory to build the package,
check the theorem axioms and run the five negative controls. Set `LAKE_BIN`
if Lake is outside the path.

`Logkeeper.OrderedAdmission` defines the local debit, suffix pin, receipt
expiry and fingerprint decisions used by the
[ordered admission production laws](../verus/ordered_admission/README.md).
Run `python3 run_ordered_admission.py` from this directory to check its
theorems, axiom lists and negative controls. The script also accepts `LAKE_BIN`.

`Logkeeper.Kernel.Ordered` projects an installed reducer trace to writer
authority and full logical history. The model uses an archived prefix to
interpret a compacted image and the previous writer to interpret vacancy.
`Logkeeper.Protocol.Ordered` projects the retained receipt book and relates
exact mutation retry to `same_chosen_append`.

Run `python3 run_ordered_reducer.py` for the ordered-model theorem and mutation
checks, including axiom audits for `Logkeeper.OrderedBudgets` and
`Logkeeper.OrderedGuards`. Run
`python3 run_ordered_correspondence.py --verus /path/to/verus` to
compare the Lean decisions with the Verus specs on the shared cases.

`Logkeeper.Codec` specifies the ordered decision header, canonical Boolean
markers and declared length bounds. `Logkeeper.CompactImage` specifies the
snapshot generation, hold receipt, lease, fence and object reference checks.
`Logkeeper.VoterSlotHeader` and `Logkeeper.VoterTransport` specify fixed voter
media and transport fields. Run `python3 run_codec.py` from this directory to
audit these four modules and run their nine negative controls. The Verus correspondence is recorded
in the [ordered codec](../verus/ordered_codec/README.md) and
[compact image](../verus/compact_image/README.md) proof areas and in the
[voter header](../verus/voter_slot_header/README.md) and
[voter transport](../verus/voter_transport/README.md) proof areas.

`Logkeeper.PrefixTrace` checks recorded ordered group choices, recovery and
cohort transfer against the prefix agreement reference. Run
`python3 run_prefix_traces.py` to record and validate the native test traces,
including stale-accept and substituted-base controls.

`Logkeeper.DisposalLease` and `Logkeeper.ErasureCommit` specify the serving
lease, disposal and exact rotation guards. `Logkeeper.LeaseReducer` adds
the independent protected-basis read lease rule and the preservation theorem
for each enrollment projection along the chosen trace. The production links
are recorded in the [ordered lease reducer area](../verus/ordered_lease_reducer/README.md).
Run `python3 run_ordered_lease_rotation.py` for the theorem and mutation checks.

`Logkeeper.Premises.BarrierKeys` and `SignatureScope` give the reference
for [ordered receipt signatures and repair keys](../verus/receipt_signatures/README.md).
The package build checks the arbitrary-chain retention theorem, the exact
signature and repair laws, and their reachability and negative witnesses.

`Logkeeper.Reducer` composes the writer-image, budget, erasure authority,
object withdrawal, lease, hold and receipt references for a chosen command.
`Step` separates rejection of the decision coordinates from the application
of the request at a chosen position. Run `python3 run_reducer_refinement.py`
for the invariant, projection and reachability proofs and their controls.
The [ordered reducer area](../verus/ordered_reducer/README.md) records which
state updates are checked against production and the remaining adapter work.

## Keeper-hosted leader journal

[Leader journal model](leader-journal.md) specifies the proposed keeper-hosted
consensus design and its proof boundary. The package checks the model alongside
the shipped stream journal, whose proposer and publication protocol has its
own refinement and trace checker.

## Consensus keeper additions

`Logkeeper.ConsensusAdditions` proves what the keeper-hosted consensus
streams add on top of Raft, as state-machine theorems over any number of
steps. OpenRaft's election, log matching and commit rules are trusted and
enter as step guards or hypotheses.

| Module | Result |
| --- | --- |
| [RecoveryFence](Logkeeper/ConsensusAdditions/RecoveryFence.lean) | The recovery term `max + 2^32` outranks the survivor's history and any lost voter that ran fewer than `2^32` elections it never saw. The survivor refuses every lost voter (`excludes_sender`), so lost voters never learn the recovery term and recovered replicas never hold a lost-suffix entry. While at most one lost voter runs, it cannot gather a quorum, so every commit and every read behind a quorum barrier observes only the recovered history. Two witnesses state the residual risks: both lost voters returning together form the old quorum and serve the lost suffix, and one returning voter answering from its own applied state without a barrier serves it too. The seal step refuses every seal while the recovery fence stands. |
| [Parking](Logkeeper/ConsensusAdditions/Parking.lean) | Under log matching, a follower that accepts a park holds exactly the leader's applied log, and so every committed entry. Accepting, parking, the busy answer and reopening keep each replica's vote, log and applied index, so any interleaving of them preserves the committed log. |
| [RetireOnProof](Logkeeper/ConsensusAdditions/RetireOnProof.lean) | A copy retired on a certified proof is outside the proof's configuration and its joint target, so removing it leaves every quorum of that configuration a quorum. A proof of another revision retires nothing, nor does a request for a copy staged again under a new generation. |
| [CatalogClaim](Logkeeper/ConsensusAdditions/CatalogClaim.lean) | A stream's genesis is its first committed claim, every claim reply names it, replicas holding prefixes of the committed log agree on it, and a checkpoint followed by its suffix reaches the same catalog. |
| [EpochLease](Logkeeper/ConsensusAdditions/EpochLease.lean) | The endgame's lease model replaces both of `RecoveryFence`'s assumptions. With clocks that drift by at most `D` over the horizon (derived from a clock-rate bound by `rate_bounds_error`), a margin `M ≥ D`, and a recovery transaction that fences every old voter outside the new membership whatever `--lost` names, every gated action of a lost voter precedes every gated action of a recovered member (`lease_precedes_wait`). Then, with both lost voters running at any term and a lost leader free to overwrite the survivor before the wait-out ends, no reader observes a history the recovery did not keep after a read of the recovered history (`no_mixed_history`), and no lost voter campaigns, leads or serves after the first recovered action (`lost_voters_deposed`). Controls: serving without the wait-out mixes histories, `M < D` lets a lease outlast the wait-out, and fencing only the keepers `--lost` names lets an unnamed lost voter renew after the commit. |
| [OffloadPrefix](Logkeeper/ConsensusAdditions/OffloadPrefix.lean) | Uploads that read only applied entries keep objects contiguous from the lineage's floor and equal to the committed records in `[floor, offloaded_through)`, with `offloaded_through ≤ commit` and monotonic per lineage; every object holds the committed records at its LSNs. Restoring from the object store plus a survivor through `known = max offloaded_through survivorCommit` yields exactly the committed log through `known`, keeps every uploaded record, and loses exactly the committed records past `known`. A witness shows why the restore point is the known-committed index and not the survivor's head: a survivor can hold an uncommitted record at an LSN at or below its head where the committed log holds another. |

Run `python3 run_consensus_additions.py` from this directory to build the
package, check the 47 theorems' axioms and run the sixteen negative controls.
The local decisions these theorems rely on are checked against the shipped
Rust in the [consensus admission area](../verus/consensus_admission/README.md).
The bounded TLA+ model of the same additions is on the `protocol-model`
branch; the [verification README](../README.md#consensus-keeper-additions)
compares the tools.
