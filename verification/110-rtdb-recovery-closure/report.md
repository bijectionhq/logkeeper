# Study 110 · Derive an RTDB recovery closure and retain its custody proof

2026-11-23

## Verdict

The recovery obligation is the set of reads and later references made by typed replay from the selected base through the chosen suffix.
The checkpoint inventory alone is not enough.
An inline suffix can also read storage.
A matching `BlockUploaded` frame loads the adopted root and its table blocks, then adds the upload's tries to the live catalog.
`TriesAdded` and `ArtefactsAdded` add references that serving and later compaction read.
An oversized proxy fetches its external payload after term admission and before the stale or hold decision.
Its decoded continuation can be any non-oversized body, including a matching upload.

The certificate therefore enumerates the base closure and, for each retained frame, the outer payload of an oversized proxy together with the dependencies of its decoded body.
Each dependency binds the exact containing physical version, so relocating it requires custody of the new version.
Packed members share one carrier and one failure domain.
A root adopted in the tail is bound by digest and exact version, in the same way as the base root.
The chosen publication retains its exact receipt set.
A later majority recovers that set from either crash-selectable image without the previous publisher.

This is a typed model proof over a transcription of the decoded RTDB representation.
It is not a proof of the production protobuf decoder, loader or provider.

## General proofs

Lean 4.35.0 checked 25 theorems with standard axioms only.

`checkpoint_enumeration_matches_every_typed_base_read` and `body_enumeration_matches_each_driver_branch` show that the enumeration equals independently stated reads for the base and for each `ReplicaBody` branch.
The upload branch is conditioned on matching storage version and epoch and on an index above the base root.
`chosen_suffix_enumeration_keeps_payloads_and_decoded_bodies` joins the outer payload with the decoded body for every retained frame.

`every_replay_read_is_in_the_typed_tail_enumeration` is the operational result.
`Step` follows the driver's pending, hold, cut, adopt and add branches.
Steps that read or reference storage carry RTDB's exact guards, and skipping, holding and fencing are left unrestricted.
For every reachable state, each demanded key is in the enumeration.
The result therefore covers every hold order and every staleness outcome that the driver can take.

Three constructive witnesses show that the earlier payload-only enumeration was unsound:

- `an_inline_upload_reads_its_adopted_catalog_and_table_block` reaches an adopted table block and trie file that no payload key names.
- `an_oversized_upload_reads_its_payload_and_its_decoded_catalog` reaches both the outer payload and the decoded root closure.
- `a_stale_decoded_body_still_needs_its_external_payload` reaches a fetched payload whose decoded body contributes nothing.

The theorems carried from the earlier draft are unchanged:

- They bind custody to the containing physical version.
- They refine AZ placement into the per-failure provider contract.
- They compose ranked membership with either crash selector, so that a later majority reads the exact published receipts.

## Controls

| Weakened design | Result |
| --- | --- |
| Enumerate the outer envelope only | `chosen_suffix_enumeration_keeps_payloads_and_decoded_bodies` fails. |
| Name the adopted root without its catalog closure | `body_enumeration_matches_each_driver_branch` fails. |
| Ignore `TriesAdded` | `body_enumeration_matches_each_driver_branch` fails. |
| Treat an inline upload as storage-free | `body_enumeration_matches_each_driver_branch` fails. |
| Drop the containing generation from a grant | `a_grant_binds_the_containing_physical_generation` fails. |

Each weakening control requires a failed check whose errors lie only inside the named declaration.
The witnesses above refute the weakened enumerations constructively and do not depend on the enumeration proofs.

## Bounded comparison

TLC 2.19 compares the derived closure against weaker certificates over two root choices and one relocation or publisher replacement.

| Weakened design | Result |
| --- | --- |
| Use the checkpoint inventory without the suffix | Serve with a missing oversized payload in two transitions. |
| Exclude retained L0 or artefacts | Serve with a missing dependency in two transitions. |
| Check only the visible selector | Serve without the older selector's dependency in two transitions. |
| Enumerate payloads only with an inline upload | Serve without the adopted catalog in two transitions. |
| Enumerate payloads only with an oversized upload | Serve without the decoded adopted catalog in two transitions. |
| Keep a logical-path hold after relocation | Serve the relocated version without custody in three transitions. |
| Accept a legacy root alone | Admit a substituted table body in three transitions. |
| Count two members of one pack as two domains | Claim independent domains in two transitions. |
| Carry only the publication position through voter replacement | Temporal stall. |
| Open from a cut without the receipts | Restore without exact receipts in four transitions. |
| Require the previous publisher | Temporal stall with the previous publisher offline. |

The exact certificate passes in every scenario, including both upload scenarios.
Recovery with the old publisher offline satisfies eventual restoration in seven states.
Both selector witnesses are reachable.

## Amendments and acceptance

[A446–A452](../amendments.md#study-110--2026-11-23) derive the closure from typed replay, bind adopted roots and carriers, and retain the receipt set in the chosen publication.
P227 exercises an inline upload in the suffix.
P228 exercises oversized frames that decode to a matching upload and to a stale body.
P229 combines relocation, publisher and voter replacement, and recovery from either selector.

## Integration counterpart

The parallel Codex thread "Assess formal specs for Bijection" (session `01a20800-a077-79d2-a639-af565be32247`) owns the RTDB Multi side of this contract in its Bijection worktree.
Its design note `llm-wiki/wiki/rtdb-journal-recovery-design.md` (commit `97b7bb3`) agrees that a replay-built image must preserve the continuation of a pending block and the grant-scoped objects that retained records reference.
It cites RTDB `8af2d6e` and `3b605d6`, which are newer than this study's pin.

The interface this study requires from that side:

1. A typed extraction of each retained frame's decoded body and admission verdict. This is the `Body` projection plus the term witness.
2. A digest and exact physical version for each root adopted in the tail, and for every oversized payload.
3. A refusal or authenticated inventory evidence for any upload or payload that lacks a digest, before portable publication.
4. The receipt set carried in the chosen publication decision rather than in a directory record.

## Residue

The model abstracts the protobuf decoder, canonical keys, the admission witness, cryptographic checks and the provider.
These remain premises.
Deletions (`TriesDeleted`, `ArtefactsRemoved`) and the source-position and cutoff staleness of additions are over-approximated: the certificate may keep objects that replay would not read.
Pruning them needs a verified replay decision.
`ResolvedTx`, `NoOp` and boundaries are modeled as storage-free.
A transaction's database operation is an effect, not a storage read, and its audit is open.
The model does not cover a native image materialized at a cut inside a pending block.
The production Rust at the counterpart revision still needs the actual wire, decoder and storage refinement.
Peak capacity across custodians and durable receipt recovery at the media boundary remain open.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean \
  python3 verification/110-rtdb-recovery-closure/run.py
```

[run.py](run.py) saves case configurations, counterexamples, commands and proof diagnostics under .results/.
