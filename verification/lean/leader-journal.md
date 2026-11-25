# Keeper-hosted leader journal proof

Run `lake build Logkeeper` in this directory with the pinned Lean toolchain.
The package checks the proposed model alongside the shipped journal models.
Its principal theorems print their axiom dependencies.

| Module | Result |
| --- | --- |
| [Consensus](Logkeeper/LeaderJournal/Consensus.lean) | Induction over reachable traces derives exact prefix agreement from term-scoped replication, durable quorum support and an up-to-date election. A chosen config entry follows the stable-to-joint-to-stable rule. Learners must contain the proposed prefix before joint configuration is issued. |
| [Application](Logkeeper/LeaderJournal/Application.lean) | The same reducer decides live and replayed commands. Conditional seal fences the previous writer. Identical retained retry is idempotent and conflicting retry preserves the history. The floor is monotone and deletion is terminal. |
| [Journal](Logkeeper/LeaderJournal.lean) | A leader's applied append reply names exact bytes in every later committed history. Every elected leader's durable log contains those bytes. A fresh head reply uses an applied view at a cut captured within the invocation, and covers any earlier acknowledged append while live. Local pages return exact bytes from one committed cut. |
| [Recovery](Logkeeper/LeaderJournal/Recovery.lean) | A successful election suffices to construct the replication, current-term commit, application and fresh head response. On a settled roster an online quorum of eligible candidates suffices to construct the election. |
| [Media](Logkeeper/LeaderJournal/Media.lean) | Preparing, syncing, selecting, restarting and reclaiming an abstract snapshot preserve the exact durable replica log, term and vote. Snapshot and suffix replay produce the same applied state. |
| [Bootstrap](Logkeeper/LeaderJournal/Bootstrap.lean) | An atomic put-if-absent binds one stream ID to one immutable genesis across competing create proposals. |
| [Witness](Logkeeper/LeaderJournal/Witness.lean) | The writer gets its append reply, the leader dies, and both survivors still have applied head zero. Their election and recovery produce a fresh head of one and the exact bytes. A second trace moves to a disjoint roster, retires the old leader and recovers the same head under the new roster. |

## What the model checks

`Step.commit` requires durable evidence for the exact issued cut, a
current-term last entry and the quorum of the effective configuration at
that cut. Reachability proves that each commit extends the earlier committed
history. The election rule compares the candidate's durable log against
its voting quorum. An intersecting replica and the rank invariant force
the candidate to carry the old committed history. Each configuration change
is a consensus entry, and the next configuration's durable quorum becomes
the basis for later elections.

`AppendReply` uses the reducer's result for the actual applied command.
It requires application through that command on the replying leader.
Other keepers can still be unaware of commitment. For a fresh head,
`HeadRead` records capture and same-term, same-configuration confirmation
inside the invocation. The reply reads from the returned keeper's applied
log through the captured index. The proof equates that result with the
committed state at capture.

The consensus core describes one logical stream. The media gates compose
independent cores on the same keeper. Each consensus log uses natural
indices, and the reducer's full history and the snapshot's included log are
ghost reference histories. A physical snapshot represents an included index
with its term, configuration, fence, floor, head, tombstone and the retained
bytes. Logical deletion and trim leave records in the ghost history for the
agreement proof.

## Source-review extensions and Rust contract

The deployed adapter uses the checked interfaces below to enter the
consensus model. The prior core and its two execution witnesses still
check in the same package.

| Boundary | Rust requirement | Lean theorem |
| --- | --- | --- |
| Media and enrollment | Separate explicit install, checked reopen and serving. Authorize install against a registry of keeper incarnations and burn the identity before using it. Missing, incomplete, wrong-incarnation or unverifiable media supplies no restart proof. Reopen a stream only with matching scope, durable term/vote and the exact logical log. A replacement runs under a fresh identity and catches up as a learner before the joint entry can make it a voter. | [`installed_identity_never_unused`, `untrusted_replica_restart_refused`](Logkeeper/LeaderJournal/Installation.lean), [`same_term_vote_reply_unique`, `trusted_restart_refines`, `joint_issue_requires_exact_learner_cut`](Logkeeper/LeaderJournal/ReplicaGate.lean) |
| Placement | Check the initial and proposed settled rosters before activation. Each roster has three distinct authenticated keeper incarnations in three distinct declared domains. Reuse the roster for append. Scope acknowledgments to an effective configuration and count each voter identity once. | [`ack_pair_spans_domains`, `Trace.configuration_valid`, `deployed_quorum_after_domain_loss`](Logkeeper/LeaderJournal/Placement.lean) |
| Peer admission | Give votes, heartbeats, read confirmations and required durable protocol work a reserved permit that app and bulk work cannot spend. Keep the permit through durable completion, or release it on cancellation or failure. Protect the actual pipeline bottlenecks, including any shared queue or worker that must run to complete the control operation. | [`saturated_load_still_admits_peer_control`, `app_and_bulk_do_not_spend_control`, `saturated_budget_allows_recovery_schedule`](Logkeeper/LeaderJournal/PeerBudget.lean) |
| Catalog | Use a trusted linearizable CAS for immutable genesis. Treat missing catalog state as unknown. Stage exact old/new contacts before issuing a joint entry and bind retained staging evidence to the stream and source configuration revision. Journal entries supply voting membership. Known authenticated contacts can keep initialized streams running while lookup is down. A committed joint change derives its final roster from the log. | [`unavailable_rejects_create_and_staging`, `cached_staging_was_published`, `stale_staging_cannot_authorize_joint`, `initialized_stream_recovers_without_catalog`, `committed_joint_finishes_without_catalog`, `pending_final_recovers_without_catalog`](Logkeeper/LeaderJournal/Bootstrap.lean) |
| Corruption | Gate voting, durable acknowledgments, read confirmations and application replies on a healthy scoped incarnation. Quarantine a replica if its snapshot is unreadable and the shared identity/WAL remain trustworthy. Clear quarantine after an exact verified restore with term/vote continuity. Unverifiable shared identity or WAL disables every dependent stream on that incarnation. | [`quarantine_refines`, `quarantine_preserves_other_group`, `corrupt_shared_refines`, `cannot_vote_or_ack_without_response`, `exact_repair_refines`](Logkeeper/LeaderJournal/ReplicaGate.lean) |

The media bridge starts each deployed stream with a closed admission mask
and ties each enabled core replica to the exact durable log in its checked
image. The joint-issue bridge combines published staging evidence, roster
validation, and an exact cut on every newcomer. Physical quarantine and disable refine core
disconnection. Verified restart and repair refine reconnection. A
validated durable copy can update a learner's log without granting
voting authority. The commit and election bridges require checked
replies. A reply genuinely emitted before a fault can remain evidence
for its original term, configuration and cut.

In the current model, same-incarnation snapshot repair restores the
exact trusted logical log for that replica, including its durable
term and vote. An ordinary consensus catch-up can then bring it forward.
Repair that substitutes an independently certified newer snapshot
while replacing a divergent local tail needs a further offline-install
refinement. Missing hard state or a log with unsubstantiated provenance
requires a fresh incarnation under the modeled policy.

A domain-loss quorum is conditional on every otherwise surviving voter
being eligible and reachable. In a joint configuration the claim holds
for both rosters. Distinct declared domains represent physical
independence only under the deployment's placement premise. Protocol
eligibility, actual scheduling, authenticated transport delivery and
durable service are the additional premises for recovery progress. The
admission model proves that spare control capacity stays usable under
app/bulk saturation. It assigns no latency or scheduling bound.

Bootstrap and creation require live trusted catalog access. Pre-joint
discovery staging also needs that access until staging evidence has
been obtained. With staged evidence retained, a caller can issue the
matching joint entry even after losing catalog access. Fresh clients
without usable contacts can still need discovery. The catalog is
advisory for routing after genesis. Its route hints can lag membership or
be unavailable, and never authorize a voter.

### Failure cuts to exercise in Rust

1. Interrupt install before media publication. Repeat with a wiped
   established directory, substituted identity, truncated log and
   missing term or vote. A restart can serve only after validation.
   An established identity cannot run the fresh-install path again.
2. Crash after durably recording a vote and before sending its reply.
   Retry under the same term after restart. A different candidate cannot
   acquire that vote. Enroll replacement media as a new learner and
   attempt promotion with a same-length but different log.
3. Try genesis and successor rosters with duplicate identities or two
   declared replicas in one domain. For each domain of a valid joint
   deployment, remove it and verify quorum in each remaining roster
   when the other voters are eligible.
4. Saturate app and bulk admission and delay bulk I/O. Exercise vote,
   heartbeat, read confirmation and their required durable operations.
   Check cancellation and error paths for permit release.
5. Disconnect the catalog before genesis CAS, after staging publication
   with its reply lost, after retaining the receipt, after joint commit,
   and after persisting part of the final entry. Try a stale stage and a
   stale route. An empty restored catalog cannot prove an old ID absent.
6. Corrupt one stream snapshot while a second stream shares the keeper.
   Exercise the reply gate on both streams, then try an exact and a
   mismatched repair. Repeat with an unreadable shared WAL or identity
   and check that every affected stream fails closed.

## Reclamation and routing follow-up

The checked ownership, volume admission and routing extensions and their Rust fault cuts are in [the reclamation handoff](reclamation-handoff.md).

## Follower replication admission

The checked receiving-side byte limits, disk-ticket lifetime and bounded durable rotation are in [the replication admission handoff](replication-admission-handoff.md).

## Implementation refinement boundary

The operational abstraction has completed, term-ordered elections and
same-term durable prefix writes. It binds votes to the durable logs sampled
at election. A read confirmation is an abstract quorum response to that
round. A transport-level refinement must derive those events from individual
votes, durable promises, delayed or duplicate packets, candidate-local
configuration changes, and nonce-bound read replies. In particular a
partitioned old leader can still reach some keepers in the implementation.
The model discards old-term effects at its authoritative transition boundary.

The bootstrap proof assumes a linearizable catalog CAS and an enrollment
registry that binds each keeper incarnation to a unique identity and records
prior enrollment independently of its disks. The media proof uses abstract sync and manifest
publication barriers. Byte-level recovery, live extent references,
transport authorization, quotas, and compiled Rust correspondence are
separate obligations. The progress theorem is constructive from an
available election under stable scheduling. It supplies neither a network
fairness theorem nor a wall-clock recovery bound.
