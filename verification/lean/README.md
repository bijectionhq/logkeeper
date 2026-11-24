# Logkeeper Lean interface

Use `Logkeeper.Protocol` for typed data and decision cuts, durable chosen
prefixes, exact append receipts, and trim charges from the chosen application
interval. The quorum module incorporates the reference, quorum membership, and
durable prefix studies. A concrete caller supplies the durable voter trace and
relates the ledger to the real prepare and accept exchanges. The transfer theorem connects independent cohorts by the exact predecessor image decoded at installation. The byte-level refinement of the signed repair package is a separate obligation.

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
