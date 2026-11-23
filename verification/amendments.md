# Logkeeper design amendment ledger

## Study 01 · 2026-11-22

Both candidate baselines use the rules below.
The deliberate weakenings produced the counterexamples.
Each entry makes an endgame rule explicit at its decision point.
The [study report](01-commit/report.md) gives the exact control, invariant, bound, and shortest trace.

| ID | Evidence | Required design wording |
| --- | --- | --- |
| A01 | `ignore_position` violates `DenseHistory`. | Check the expected next LSN at the authority's commit decision. |
| A02 | `ignore_fence` violates `Fenced`. | A staged payload carries its original writer epoch. Recheck it at commit. |
| A03 | `fence_omits_tail` violates `ExactFenceCut`. | Return the entire committed prefix preceding the fence, including the last committed append. |
| A04 | `single_vote` and `publish_before_data` violate `Recoverable`. | Order becomes authoritative only after its exact payload can survive the stated failure envelope. |
| A05 | `reply_before_commit` violates `ReceiptMatchesCommit`. | Durable staging alone grants no successful append receipt. |
| A06 | `retry_by_lsn` violates `ReceiptMatchesCommit`. | Reconcile an occupied LSN against the exact request, including its payload, before returning a success receipt. |
| A07 | `barrier_by_held` violates `ExactBarrier`. | Derive fresh read cuts from the committed prefix. A staged payload contributes nothing until committed. |

These entries establish concrete dependence in the bounded model for the weakenings exercised here.
Independence for the full kernel remains open.

### Study corrections

The initial runner used a flag unsupported by the pinned TLC release and a sentinel TLC could not compare to a record.
The runner now uses that release's `-deadlock` spelling and typed sentinel records.
The first three-LSN run exceeded 60 seconds while retaining unnecessary acceptance history in safety states.
Safety runs now observe each receipt and barrier at emission, while witness runs separately track acceptance history.
The final run applies the same protocol transitions and repeats every control and witness.

## Study 02 · 2026-11-22

[Study 02 compares two activation protocols](02-handoff/report.md).
A candidate itself failed a progress requirement here.
The amendments replace directory-dependent activation with a portable, source-authorized handoff.

| ID | Evidence | Required design wording |
| --- | --- | --- |
| A08 | Directory activation strands a sealed and installed stream on directory loss. | Commit the successor instruction at the source before sealing. Once authorized, carry the seal and exact cut to the target and activate under its own quorum. Update directory routes independently. |
| A09 | Activating an isolated target without seal evidence allows both groups to commit different records at the same LSN. | Takeover requires verifiable prior-owner fencing or an intersecting authoritative reconfiguration. Lack of contact and an unverified precopy confer no authority. |
| A10 | Installing a stale precopy loses a committed record. | Verify the exact sealed prefix and install it durably before enabling the target. |
| A11 | Reopening the source on timeout after target activation creates two writers. | The source seal is irreversible for this placement generation. Abort only while the source owns an unsealed generation. A later return to that group is another authorized handoff. |
| A12 | Progress fails when the scheduler may stutter forever. | State the availability envelope explicitly. Require both group quorums, eventual connectivity for evidence that has yet to arrive, and fair scheduling. Once the target installs the evidence, directory and link availability drop from the activation premise. |

Lean proofs establish source-fence and exact-prefix invariants in the one-move abstract reference machine and the indistinguishability limit on isolated takeover.
A full refinement of the certificate and reconfiguration protocol remains open.

## Study 03 · 2026-11-22

| ID | Evidence | Required design wording |
| --- | --- | --- |
| A13 | An uploaded but unpublished checkpoint permits an unreconstructable trim in the weakened model. | Only a published, stream-bound checkpoint certificate can authorize trim. |
| A14 | Either stale admission check can admit an unreadable cursor. | Serialize logical replay admission and trim in the same stream authority. Preliminary checks guide the caller. The final decisions read the same authoritative floor and admitted holds. |
| A15 | Separate controls and Lean proofs expose finite retention and progress conflicts. | Bound both checkpoint recovery work and retained work. Hold exact cursors for a bounded service contract, and put longer exact history behind a separate product contract. Reserve resources for checkpoint and fencing progress. |

The [retention study](03-retention/report.md) gives the exact models, traces, bounds, and general cardinality theorems.

## Study 04 · 2026-11-22

| ID | Evidence | Required design wording |
| --- | --- | --- |
| A16 | Unrecorded delivery survives an apparently complete erasure operation. | Reserve and durably record each custody location before admitting transmission or storage. |
| A17 | Delayed delivery repopulates a deleted destination after an absence-only acknowledgment or forgotten fence. | Fence writes at each location before acknowledging disposition. Keep or replace the fence with equally strong authorization for every subsequent write. |
| A18 | A majority leaves a custody location unaccounted for. | A terminal closure commits through the serving quorum. An erasure completion receipt requires a verified disposition for every custody location. Unreachable locations may leave completion pending. |

The [retirement study](04-retirement/report.md) records the fault traces and general Lean safety proofs under trusted write gates and disposition evidence.

## Study 05 · 2026-11-22

| ID | Evidence | Required design wording |
| --- | --- | --- |
| A19 | A late seal or a stale-source receipt allows writes after acknowledged retirement. | Source seal and source retirement serialize on the same authority. A retired source cannot seal. After seal, only the active successor can commit terminal retirement. |
| A20 | The new authority can falsely report erasure if installation discards source custody. | A handoff installs outstanding custody obligations alongside the exact committed cut. Locations from staging and earlier placements remain until disposition is verified. |

The [composition study](05-lifecycle/report.md) checks both outcomes of the retirement race.

## Study 06 · 2026-11-22

| ID | Evidence | Required design wording |
| --- | --- | --- |
| A21 | Accepting an equal generation or losing the durable generation floor lets a sealed predecessor reopen. | Establish destination-side replay protection even when its historical stream state is reclaimed. |
| A22 | Reused nonces and omitted target binding let the same seal open more than one group. | Bind the seal to a fresh reservation minted by the exact destination quorum, and atomically consume that reservation on activation. A missing reservation refuses installation. |
| A23 | Expiring a prepared reservation after the source seal strands the agreed successor. | A sealed move's reservation is durable until completion. Cancellation needs evidence that the source can no longer seal against that reservation. |

[Repeated-move comparison and nonce proofs](06-generations/report.md).
The logical slices of A01, A02, A07, A10, A13, and A14 and terminal closure were also checked in the [consolidated logical reference model](07-reference/report.md), within the stated abstraction.

## Study 08 · 2026-11-22

| ID | Evidence | Required design wording |
| --- | --- | --- |
| A24 | Protecting only the replay range lets the object reaper remove an active snapshot's base. | Return an admitted snapshot only after pinning its checkpoint objects and its exact journal replay range. Either acquisition can fail and unwind. |
| A25 | A destination that installs the floor without the hold can trim a range still admitted at its source. | Freeze and install the floor, replay grants, and required bytes together. A destination owns the same protections after activation. |
| A26 | Releasing protection on expiry before draining can destroy an admitted read's basis. | Expiry first fences new reads. Release physical protection only after admitted reads drain or have been effectively fenced. |

[Snapshot-basis composition checks](08-replay-handoff/report.md).

## Study 09 · 2026-11-22

| ID | Evidence | Required design wording |
| --- | --- | --- |
| A27 | A fully shared admission budget distinguishes two runs with the same foreground request and different background occupancy. | Scope record contents and authorization to the stream. Treat aggregate contention and timing as explicit observations unless an isolated service contract is supplied. |
| A28 | Lending all durable headroom prevents a guaranteed arrival from fitting. | Preserve guaranteed reservations against irreversible borrowing. Borrowing revocable service time or unused conditional capacity needs its own scheduling contract. |

[Contents and capacity proofs](09-isolation/report.md).

## Study 10 · 2026-11-22

| ID | Evidence | Required design wording |
| --- | --- | --- |
| A29 | Issuing both an abort and a seal for one reservation invalidates the activation obligation. | Serialize abort and seal at the source for the exact reservation. Abort wins only before seal. A sealed attempt ends by installing its successor. |
| A30 | A stale abort or an isolated timeout can discard the only activation slot. | The destination reclaims only the slot named by verifiable source abort evidence. If neither an abort receipt nor a seal can be obtained, keep the slot pending. |

[Reservation cancellation safety and progress](10-cancel-move/report.md).

## Study 11 · 2026-11-22

| ID | Evidence | Required design wording |
| --- | --- | --- |
| A31 | Requiring a new grant after seal strands an already authorized move under directory loss, even with a healthy target. | Separate placement activation from RTDB writer election. Carry the installed holder and writer epoch through the sealed cut. A later holder change uses the ordinary higher-epoch fence at the current owner. |
| A32 | Carrying the preparation's grant can resurrect the old holder. Substituting a holder under the same epoch also violates the writer contract. | The seal carries the holder and writer epoch committed at that same decision. Installation may change only the placement. |
| A33 | Ignoring holder, placement, or expected LSN admits requests for the wrong authority or position. | Check the holder-bound grant, its epoch and current placement generation, and the expected LSN at authoritative commit. A past-placement request can reconcile its exact retained receipt without authorizing a new append. |

[Writer handoff comparison and Lean trace refinement](11-authority-refinement/report.md).

## Study 12 · 2026-11-22

| ID | Evidence | Required design wording |
| --- | --- | --- |
| A34 | Direct membership replacement admits stale decisions and can bypass an acknowledged cut even when voter lists overlap. | Order the membership change and durably fence an old majority. A late receipt may reconcile a known old committed decision. It cannot create a new old-only decision. |
| A35 | Metadata, equal length, or a reused address can falsely attest a replacement copy. | Count verified durable identities in each configuration. A readiness proof must cover the exact retained bytes or independently durable references for that cut. |
| A36 | Premature reclamation can remove the only surviving eligible copy before adoption. | Keep the old membership's retained cut recoverable through the transition. Reclaim removed copies after the new membership has durably adopted a verified cut. |
| A37 | A new-only vote in joint phase can leave an old-side recovery majority without the record. | A joint commit satisfies both old and new majority conditions. A deliberate sealed alternative pauses appends until adoption. |

[Membership comparisons and journal trace proof](12-quorum-membership/report.md).

## Study 13 · 2026-11-22

| ID | Evidence | Required design wording |
| --- | --- | --- |
| A38 | A valid receipt from retired target membership can activate an unrecoverable cut. | Validate the exact image against the target quorum at the activation decision, or show that a registered durable obligation preserved its coverage through every membership change. |
| A39 | Reclaiming a certified copy can make a same-revision receipt stale. | Keep the attested data protected through activation. Disposing of staged data must revoke its readiness first. |
| A40 | Releasing the source after preparation can remove the last copy when the target changes membership during an AZ outage. | Release source custody only after the target durably activates the exact recoverable cut. Keep earlier custody records until their disposition is verified. |

[Target activation durability and composed refinement](13-install-durability/report.md).

## Study 14 · 2026-11-22

| ID | Evidence | Required design wording |
| --- | --- | --- |
| A41 | A cached extent lookup survives publication and reclamation of an old file. | Revalidate the index and exact present bytes while acquiring the physical borrow. A lookup is only a hint until the protected acquisition commits. |
| A42 | A valid logical replay hold does not keep a retired physical extent needed by an admitted read alive. | Protect exact physical inputs independently. Each borrower remains attached to its original extent and site through compaction and moves until completion or effective stop. |
| A43 | A delayed borrow after close, a timeout treated as a stop, and a new success after confirmed cancellation violate the I/O boundary. | Fence new admission before dropping the logical hold. A timed-out operation retains its physical custody until completion or verified fencing. A fenced operation can no longer produce a new success. |

[Read custody comparison and proofs](14-read-custody/report.md).
For exact pinned I/O the logical hold can release first, with physical custody maintained independently.
An operation that can still acquire additional dependencies remains on the drain-first contract.

## Study 15 · 2026-11-22

| ID | Evidence | Required design wording |
| --- | --- | --- |
| A44 | A delayed prepared envelope reopens a closed permit, and closing by range drops another reader's hold. | Admit only a current reservation for the exact non-reused ID and LSN. Close consumes that exact ID, including a still-pending reservation. |
| A45 | Checking the newest permit allows trim past an earlier holding permit. | Trim serializes against the full set of current holds and preserves each required range. |
| A46 | Losing issuance state resurrects a spent permit. Losing a prepared reservation strands a valid delayed admission. | Move the issuance high-water mark, prepared reservations, active holds, and floor with the ordered cut. |

[Multiple permit and composed replay proof](15-replay-permits/report.md).

## Study 16 · 2026-11-22

| ID | Counterexample | Rule |
| --- | --- | --- |
| A47 | A parent receipt and the child's initial cut can have the same number. The numeric-only gate publishes the foreign receipt. | Bind each certificate to the stream incarnation. Reissue a child certificate at child genesis for inherited state, with child decoding and custody. |
| A48 | Different ordered prefixes can yield the same state. A durable manifest can open to the wrong state or require the wrong decoder. An incomplete manifest can leave required bytes uncovered. | Certify exact committed prefix, precise continuation state, supported format, and durable closure of every dependency. Every change to the published boundary must carry this evidence. |
| A49 | A selected root can be ahead of a captured read. Using the current head or omitting the tail returns the wrong cut. | Select a certified image at or before the captured cut. Replay exactly from the certified exclusive start to the captured upper cut. Protect the read's entire basis. |

[Checkpoint controls and general reconstruction proof](16-checkpoint-reconstruction/report.md).

## Study 17 · 2026-11-22

These amendments describe the conditional exact historical feed contract.

| ID | Counterexample | Rule |
| --- | --- | --- |
| A50 | Two event orders yield the same checkpoint state and event count. A generic decoder cannot recover both. | Require an exact event projection for historical resume. A state reconstruction certificate alone cannot authorize it. |
| A51 | Publishing across a gap or trimming under checkpoint coverage alone exposes missing history. | Publish contiguous exact event coverage and require it before trim within the promised history window. Lagging coverage consumes finite journal headroom. |
| A52 | Trim races a planned join and silently drops an event. An overlapping join can duplicate an event when the archive grows. | Capture an upper cut, revalidate the current floor at suffix admission, and join adjacent half-open ranges. If trim crossed the planned join before admission, replan using the new archive coverage. |

[Exact-feed counterexamples and composition proof](17-exact-feed/report.md).

## Study 18 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A53 | Freezing a cut before reservation lets the latest checkpoint permanently overtake it even with a healthy link and fair service. Substituting the live head later can change the result. | For an ordinary latest read, select the current certified root and committed head in one ordered decision that reserves the recovery basis. Keep that exact upper cut. |
| A54 | Publication before custody leaves a current root unbacked. An old receipt can republish a prepared root while an earlier disposal permit is in flight. | Publish from a live registered custody identity. Order disposal authorization against adoption and reservations. A disposal-fenced identity cannot be adopted or issued again. |
| A55 | After newer publication, reaping the older reserved root or trimming past an active nonempty suffix can strand the read. A separately protected root-only read can finish even after the floor passes its cut. | Hold the exact root and only the nonempty WAL suffix for the reservation. Transfer both obligations with the cut, and release once the reader has no further acquisition rights and any unfinished I/O has independent custody. |
| A56 | A reserved suffix can reach finite retention capacity while checkpoints keep advancing. Fairness alone cannot complete a read with permanently inaccessible inputs. | Budget read slots and retention. State stable access and fair service as progress premises. Apply backpressure at the retention bound until safe release. |

[Snapshot admission comparison and proofs](18-snapshot-admission/report.md).

## Study 19 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A57 | A partial receipt bundle publishes a root missing a dependency. Releasing from a live root immediately breaks its closure. | Bind each root to its full immutable graph of exact physical versions. Register every reachable dependency before root admission. A ready checkpoint keeps the shared registration until its logical publication and holds have released it. |
| A58 | A scan observes no references, then a new reference arrives before disposal. Reversing these steps lets a delayed acquisition attach to a version already being erased if the gate is unchecked. | Order exact-version reference admission and disposal authorization at the same custodian. Close the version gate once no references or physical borrows remain. Treat scans as hints. |
| A59 | A release for a not-yet-delivered registration is followed by the delayed acquisition. The supposedly released interest reappears. | Settle the exact root-version reference as terminal even if the acquisition has never arrived. Delayed admission cannot reuse that identity. |
| A60 | Releasing the final root reference can leave an admitted physical read. Deletion by provider key can remove another version still in use. | Retain independent physical borrows and delete only the fenced exact physical version. |
| A61 | Erasing the only version still required by a live fork conflicts with continuous fork recovery. A replacement root can instead become live before the shared reference is withdrawn. | Scope deployment erasure to its custody and authority. Preserve a surviving fork's admitted data by installing verified independent coverage before releasing and erasing the source copy. |

[Shared-root custody, version fencing and composed snapshot proof](19-shared-object-custody/report.md).

## Study 20 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A62 | A crash between acquisition and receipt loses the record needed to clean up the grant. Forgetting a closed plan after a floor acknowledgment can also leave a grant untracked. An old grant can publish after the source closes unless publication checks the terminal decision. | Record the complete immutable per-custodian intent before sending. On recovery, replay it or order terminal close against publication and release every planned interest, including an ambiguous grant. Preserve the plan until closure settles. |
| A63 | A cutoff based only on a declared intent can cross an unacquired live preparation. Dropping a closed marker without enforcing the floor admits a delayed acquisition. | Install the receiver floor only through permanently closed or durably acknowledged exact interests. Reject new admissions at or below it. Compact terminal markers only under an installed floor. |
| A64 | A terminal-only cutoff stalls behind a long-lived old root. Forgetting the live grant at the new floor destroys a published dependency. | Preserve all live grants through cutoff advancement. An exact existing retry, and the release of that same grant, remain available below the floor. |
| A65 | Crediting an offered floor can exceed receiver capacity. Unbounded issuance defeats the terminal-marker bound while the receiver is delayed. | Keep a finite per-channel serial window measured from the receiver's durably acknowledged floor. |
| A66 | Advancing retry credit can retain every old pin and admit more physical custody than capacity. Requiring foreground capacity for releases strands closed pins even when the link works. | Meter actual custody independently of serial credit. Retain cleanup resources when ordinary admission is full, and state authority and custodian access as progress premises. |

[Interrupted recovery and cutoff comparison](20-registration-recovery/report.md).

## Study 21 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A67 | Closing and reopening a route under the same handle restores a retired admission capability. | Mint a new handle at the custodian under a durable, non-reused nonce. Bind it to the exact custodian incarnation, issuer and route. |
| A68 | Drain-first rollover cannot proceed while an old published root keeps a live grant. Dropping its grant on close breaks publication coverage. | Close the channel's admission gate and reclaim its control row. Preserve installed grants with their exact identities and separate lifetime. |
| A69 | Using the current route or serial alone lets old messages register a new grant, close a successor, advance its floor, or release its live pin. | Scope every acquisition, close, floor receipt and release to the exact channel or grant identity. The route identifies a current slot and carries no authority by itself. |
| A70 | Requiring the old channel for release leaves an authorized withdrawal stuck after close even with healthy connectivity. | Keep exact reconciliation and release available at the physical custodian. For a retired handle, an authoritative observation of an absent grant is stable. |

[Channel lifecycle comparison and general proofs](21-custody-channel-lifecycle/report.md).

## Study 22 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A71 | Matching carrier bytes may hide a wrong member index, and raw byte equality rejects valid repacking. Observed content can agree while a dependency is missing. | Verify the decoded contents of every declared logical member, using its exact physical-version binding and checked range. |
| A72 | A valid copy can be applied under another referrer, an advanced catalog revision, or a replacement physical destination. | Bind the capture and installed manifests to the exact source root, stream, cut and revision and the exact destination incarnation and root version. Recheck them at publication. |
| A73 | Reclaiming or substituting the verified target between attestation and publication leaves an authentic proof with no valid readable target. | Register the exact target dependencies as a live obligation before verification can authorize publication. Carry those obligations until the published root owns them or the attempt safely closes. |
| A74 | Checking only the moved root or only outstanding physical I/O misses other referrers and readers still allowed to discover dependencies. Draining everything before publication prevents safe overlap. | Switch the current basis after verified target readiness. Preserve all old referrer, snapshot and borrow obligations until their own releases. Authorize exact source disposal after they are settled. |
| A75 | Requiring the source link for publishing a ready target strands an otherwise eligible transfer. Losing the source link after publication can still block disposal. | Publish from the durable current target and authenticated capture under the referrer's authority. Keep source erasure pending until the exact source provides disposition evidence. |

[Residence transfer comparison and proofs](22-residence-transfer/report.md).

## Study 23 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A76 | A snapshot of observed grants omits an acquisition that can still arrive. A pre-copy can miss an intent committed just before seal. | Transfer the final sealed issuer book, including every unresolved exact plan and terminal decision. Use the existing one-use authority handoff. |
| A77 | Omitting a cancellation restores a preparation that the prior authority already closed. A late source cancellation can also diverge from the sealed cut. | Order cancellation with publication and seal. The predecessor stops deciding at seal, and the successor inherits its committed terminal decisions. |
| A78 | Rerouting an old acquisition using the new placement creates an unplanned physical interest. | Reconcile and release the exact inherited keys at their original custodians. Independent new work uses fresh scoped keys. |
| A79 | An absence observation can precede a delayed acquisition and orphan its eventual grant if the issuer forgets the plan. | Keep the exact intent until the matching physical interest is settled under a durable fence. An authoritative absence is stable after its own handle is retired. |
| A80 | Waiting for the source issuer blocks installation after the complete seal is staged. The old physical custodian can separately remain inaccessible. | Install the staged exact issuer book even when the old issuer is unreachable. Continue independent work within budget and retain inaccessible pins and plans until exact settlement. |

[Issuer handoff comparison and proofs](23-custody-authority-handoff/report.md).

## Study 24 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A81 | A replacement voter set may have only one copy of the current custodian image. A switch without an old fence lets an old quorum decide. | Use the existing quorum coverage and old-majority fence for the complete committed custodian state as well as the stream journal. |
| A82 | Losing the issuance counter, spent marker or floor across restart admits a previously retired handle or closed request. | Recover the exact channel state and remembered refusals at the current committed cut. |
| A83 | Recovery that forgets a grant or an admitted borrow can lose a live dependency and erase bytes still in use. | Include exact grants and borrow obligations in durable custody state and restore them before serving. |
| A84 | The earlier typed channel model required a present grant for release even though a closed request can still be in flight. Acknowledging an absent cancellation without installing its fence admits that request later. | Admit an authenticated exact release for an empty slot or a matching binding. Persist the refusal before acknowledging and preserve it through recovery. |
| A85 | Early provider dispatch can erase a live grant. Forgetting an existing deletion fence reopens a version with an erase in flight. | Before dispatch, commit exact-version authorization that survives recovery. An idempotent provider effect may complete independently. Commit disposition only on exact absence evidence. |

[Custodian recovery comparison and proofs](24-custodian-recovery/report.md).

## Study 25 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A86 | A local vote survives only if the exact bytes and the name by which recovery reads them both survive. Each barrier alone permits a lost vote in four transitions. | Vote once the written prefix and its recoverable binding are durable. Count that evidence only under the corresponding persistent voter identity. |
| A87 | Skipping a torn frame creates a gap. Inferring commitment from surviving bytes can expose a write that never reached a quorum decision. | Decode contiguous exact records from a validated base. Expose the certified commit prefix and reconcile other surviving candidates through the ordered authority. |
| A88 | An early selector can choose an incomplete replacement. Early predecessor reclamation can remove the generation still selected after a crash. | Ensure complete replacement durability before publication. Keep the predecessor recovery path until the selector is durable, and retain every extent still protected by physical custody. |
| A89 | A captured full image alone omits intervening writes. Routing an acknowledgment only to the new generation during selector uncertainty can strand it. Head matching disqualifies the captured candidate once the head advances. | Keep a shared exact ordered suffix reachable from every selector that crash recovery may choose. Replace the fixed base independently of appends and retain the suffix through the durable switch. |

[Journal media crash comparison and proofs](25-media-crash-consistency/report.md).

## Study 26 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A90 | A warm opener can see a replacement before the namespace barrier. Deleting the predecessor then allows a subsequent power loss to select a missing base. An exact warm reopen can vote on the shared tail and recover it through the predecessor. | Let a verified opener serve under the replica lease. Keep both crash paths protected until the exact selector has durable evidence. Apply the same reclaim guard in recovery and normal operation. |
| A91 | A second unbarriered publication introduces a third valid crash result. Tracking only the oldest and newest lets the reaper remove the remaining outcome. | Allow one unresolved selector switch per journal. Resolve and durably establish its outcome before publishing another replacement. |
| A92 | A prepared image may outlive its predecessor. Its older cut can require suffix extents the current base has already allowed the reaper to remove. | Bind cheap publication to the exact validated predecessor. An adapter that reuses a stale preparation must revalidate the current exact closure before installing it. |
| A93 | A restarted replica can delete a prior base that an independently live operation still needs. Draining every old borrow before each publication also prevents independent reclamation of later unused generations. | Reclaim only exact extents outside both crash dependencies and live physical custody. Carry live custody through recovery or establish an effective stop before releasing it. |

The initial acceptance assertions for repeated rotation admitted traces that staged an intermediate base without installing it.
The corrected guards require that intermediate base to become durable.
The double-loss witness records a distinct selected generation at each power loss.
See the [rotation comparison and trace proofs](26-journal-rotation/report.md).

## Study 27 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A94 | A longer older minority tail can diverge from a chosen newer prefix. A shorter report within the same accepted ballot can omit a chosen extension. | Take the greatest accepted ballot in the prepare quorum, then the longest complete prefix within it. Preserve the exact immutable proposal chain for each ballot. |
| A95 | A voter that forgets a promise can accept an older vote after its later prepare report. A completed old quorum then contradicts the new ballot's inherited prefix. | Commit the promise before returning its exact snapshot. Every future local vote consults the durable floor, including after restart. |
| A96 | A promise stamped as an accepted ballot can give an empty or incomplete acceptance precedence over a chosen prefix. | Report the ballot that durably accepted the complete exact prefix. A newer promise or incomplete transfer cannot advance that accepted rank. |
| A97 | Matching bytes reach different replicas in different ballots while no ballot has a quorum for those bytes. A future ballot can choose different bytes. | Form a receipt from exact prefix votes at one ballot within its certified voting configuration. Delivering an earlier valid receipt remains safe. |

[Fixed-group agreement comparison and proofs](27-prefix-consensus/report.md).

## Study 28 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A98 | Choosing an append command and immediately acknowledging it can report success before it has a successful ordered result. A delayed reply for an earlier successful decision remains valid after retirement. | Authorize a success reply using the exact chosen command and its result at that group position. Derive the result by applying the chosen prefix in order. |
| A99 | A fence can be ordered before an append that passed submit-time authorization. Choosing an append with the wrong expected LSN can also produce a different stream effect if that guard is bypassed. | Recheck the installed writer grant and exact stream position against the ordered application state. A refused command leaves that state intact. |
| A100 | A completed read marker can precede the invocation which mistakenly reuses it. Matching a writer or route leaves that ambiguity. | Bind a fresh read response to its exact invocation and applied cut. The ordered reference uses that invocation's marker. Retry the same invocation under the same identity. |
| A101 | A freshly invoked read at a lagging replica can return a cut below one already acknowledged to the caller. Replaying an old marker after a new write can do the same. | Establish a read cut inside the invocation interval and through all prior effective commits. The ordered reference path uses the marker's exact result, including when the eventual reply follows a later commit. |

[Ordered application comparison and proofs](28-ordered-application/report.md).

## Study 29 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A102 | A cached quorum response can predate a choice already in force when the read begins. Ignoring a voter's higher promise also allows a positive round after a quorum fences it. | Count distinct authenticated replies for the exact invocation, fresh round and ready replica scope. Positive voters enforce their durable promise in that scope. |
| A103 | A replica can lag a chosen command even while the current ballot is valid. An unready successor can omit a prior ballot's chosen prefix. | Activate the exact inherited basis on a durable quorum before collecting read observations. Use the maximum reported accepted position as the floor for the reply. |
| A104 | A minority sample can be uncommitted. Its position can later contain different chosen bytes. | Serve an exact certified applied snapshot covering the sampled position. The sampled bytes need independent certification before they can be served. A separately validated current snapshot can satisfy the same floor. |
| A105 | Position 1 can be a valid logical command cut while a durable batch changes the physical frontier directly from 0 to 2. | State the logical boundary interpretation explicitly. For an exact physical frontier, the checked alternative uses a previously certified cut that matches the maximum from the same fresh round. |

[Read-index comparison and proofs](29-read-index/report.md).

## Study 30 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A106 | Distinct durable voters can send authentic replies in different configurations. Counting those replies together can form evidence with no quorum in its declared scope. | Keep every round bound to its original invocation and exact certified voter scope. Validate the original quorum before carrying its immutable floor. |
| A107 | One constituent majority intersects every joint write. A fence on the successor constituent alone can miss a joint reader that uses only the predecessor side and returns a stale cut. | Fence every still-eligible old read quorum. Allowing either side requires durable fences on both at finalization. Dual and successor-only reads close under a successor-majority fence, with the successor's installation obligations still in force. |
| A108 | A current applied snapshot can lag a write chosen before the invocation. An exact sampled position can also become unusable after checkpoint publication or discard of a minority tail. | Reserve an exact authorized applied snapshot covering the verified floor, including a newer snapshot in the same lineage. Start a fresh round when the original floor or scope evidence cannot be satisfied. |
| A109 | Successor adoption can forget an admitted hold, and later collection can remove a root still in use. | Carry the exact reservation through membership installation and retain its root and any nonempty suffix until effective release. A round alone conveys an ordering bound. |

[Reconfiguration and read reservation comparison](30-reconfigured-reads/report.md).

## Study 31 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A110 | A reader follows a cached gate observation after its window is sealed and released. Retaining the root alone also lets checkpoint compaction remove a still-needed suffix extent. | Register the complete physical basis before serving. Validate the exact open gate and endpoint session atomically with a local borrow. Share the registration across independent invocation-bound reads. |
| A111 | A restarted process has an empty local table while an older operation can still complete. Reusing the old gate admits a new session and treating timeout or restart as a stop permits premature release. | Bind the gate to a non-reused endpoint session. Keep installed custody until the original operations finish or an effective fence stops the exact session. Preserve that fence through later recovery. |
| A112 | Counting only open gates omits an unresolved sealed holding and exceeds a one-window quota. An unprotected staged window can also lose needed bytes before it opens. | Charge staged, open and sealed holdings until exact release. With independent headroom, prepare the successor's complete basis and atomically switch local admission while keeping outstanding old borrows protected. |
| A113 | A retirement command leaves the data LSN unchanged. An equal data position lets a postterminal invocation use a stale live snapshot. | Use the ordered group position to compare the original invocation's floor with a certified applied view. Require that its applied authority is live. |
| A114 | A call's preterminal floor can match an older live view after terminal closure. Fencing only the visible open gates can leave a prepared one free to activate. Fencing every gate before closure blocks quorum terminal progress while one is unreachable. | Separate terminal closure from physical settlement. Use the live cut within the invocation interval for overlapping calls. A stronger physical admission deadline needs every open and prepared gate fenced before the receipt, or an admission rule that intersects retirement. |

[Standing snapshot custody comparison and proofs](31-standing-custody/report.md).

## Study 32 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A115 | An old write can reach its quorum before any coordinator learns its choice. Copying only the learned head allows the successor to choose different bytes at that position. | Recover the greatest exact accepted prefix by ballot and logical position from scoped durable reports. Account for pending quorum evidence independently of receipt delivery. |
| A116 | A report without a fence or a fence lost on restart can miss later votes. A successor-only majority can miss a stable predecessor write quorum. Even a valid fence can leave an outstanding old vote able to complete evidence already covered by the recovered image. | Permanently fence the actual predecessor scope on an intersecting quorum and capture its accepted state atomically. Reconcile late predecessor quorum evidence within the inherited prefix. A deadline forbidding any late quorum completion has a stronger availability dependency. |
| A117 | An intermediate scope with no new writes can drop its inherited basis. A target can also report the right length while holding the wrong bytes. | Carry the exact previously installed basis across empty recovery and require the successor's own quorum to have its exact recoverable image before activation. |
| A118 | Two disjoint joint closure quorums can each block every write quorum and authorize different successors. On one fixed constituency, irrevocable local intent votes can split among contenders and stall. | Choose one successor intent through the ordered authority. Bind recovery and durable scope fences to its exact identity. |
| A119 | Freezing the first recovered candidate before its bytes are independently durable can strand a transition if the only accessible copy of a longer unchosen suffix is lost. | Keep the scope fence and target intent fixed. Before activation is chosen, allow a fresh ranked recovery over the surviving predecessor quorum. Preserve its inherited and chosen history. |
| A120 | Two valid staged cuts for the same intent can both activate and then disagree on the next command. | Choose one exact successor installation after quorum recovery evidence. Resolve lost activation replies through the same decision and settle unchosen staging separately. |

[Configuration closure comparison and proofs](32-configuration-closure/report.md).

## Study 33 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A121 | Two target ballots can choose different images when recovery ignores an accepted report. Staging quorum receipts can appear before any activation vote. | Use one exact target slot, recover the greatest accepted value from its durable prepare quorum, and publish only from a chosen and applied installation. Reconcile lost responses against the same slot. |
| A122 | Metadata-only votes can choose an image that no surviving endpoint can load. A cached readiness receipt can outlive its local staged copy. | Bind every accept to exact durable local bytes or pre-existing independently durable custody under the stated fault budget. Validate current custody when accepting. |
| A123 | A newer promise can precede acceptance or even selection. Releasing the older binding at promise time can strand the next prepare with a valid accepted value and missing bytes. | Preserve the exact latest accepted binding across prepare and restart. Release it after a durable replacement and settlement of any independent holds. |
| A124 | A prepared term can refer to a donor that fails before the value materializes. Retrying that term can stay blocked even with a reachable quorum. | Open a fresh higher ballot and collect exact reports from the current quorum. If an earlier choice exists, retain it. If the fresh quorum reports no accepted value, another authorized image is eligible. |
| A125 | After one AZ loss, the two survivors may hold different unchosen images. The lower-rank voter cannot stage the greater accepted image at a one-image limit while its current binding remains live. | Reserve recovery capacity for the current exact binding and a replacement together until the durable vote switches them. Charge actual physical footprint and release old obligations independently. |

[Activation slot comparison and proofs](33-activation-slot/report.md).

## Study 34 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A126 | A target's learned view can omit an activation already chosen by its old voters. Resetting a separate pending slot at membership installation can also authorize a different image. | Recover the exact ranked command prefix when the target orders activation in its existing journal. A separately carried slot must transfer its exact accepted binding and reconcile it under the new family. |
| A127 | Replacing voters can strand the adopted image, and an authentic old receipt can enable votes or serving without current evidence. | Install the recovered image and its live bindings under a current recoverable quorum. Enable serving only with current exact activation evidence or its verified ordered inheritance. |
| A128 | Checking an older chosen command against the receiver's current physical revision changes its outcome. Ignoring the revision check also accepts a stale envelope ordered later. | Decide under the logical revision at the command's ordered position. Certify current physical coverage separately when a new family prepares to serve. |
| A129 | Readiness can outlive its discarded grant. A membership replacement can also forget a spent attempt fence. | Require the exact live ordered grant. Preserve its disposal fence through replay and replacement until certified compaction excludes every delayed use. |
| A130 | An existing target can remain unable to replace a voter while waiting for an unrelated source image, even though both membership quorums are reachable. | Let the target repair its existing ordered state independently of reservations with no recovered data dependency. Use the fixed-family slot for authorized bootstrap without an existing serving journal. |

[Pending activation comparison and proofs](34-pending-activation/report.md).

## Study 35 · 2026-11-22

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A131 | A missing row can reopen after marker compaction or loss of the cutoff at voter replacement. Advancing over an unresolved allocation can also close a valid in-flight attempt. | Advance the installed cutoff only over resolved exact rows, carry it through voter replacement, and interpret absent rows at or below it as spent. |
| A132 | Compaction can erase a selected image's live ready grant. Requiring every crossed row to be spent also ties issuance to closing a still-valid grant. | Keep exact ready rows while advancing the cutoff through ready or spent attempts. Remove only individual terminal markers behind the cutoff. |
| A133 | Removing a logical terminal marker can erase the sole cleanup obligation for a still-held physical pin. | Retain exact charged cleanup independently and settle it by its original physical holder and binding. |
| A134 | A proposed cutoff can overstate available issued credit. Advancing an installed cutoff can also leave its old physical pins in place. | Issue from installed credit and meter every physical pin separately through actual settlement. |

[Attempt compaction comparison and proofs](35-attempt-compaction/report.md).

## Study 36 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A135 | Guessing completion closes an unresolved intent. Old terminal evidence or a seal can act on a new occupant if routed by slot. Losing the issuance fence lets a closed handle reopen. | Order closure against the exact live non-reused handle and its source abort or installed activation. Preserve issuance across target replacement and check the same scope on installation. |
| A136 | Draining before closure keeps an admission row occupied behind an unrelated provider or result-path outage. | Close admission from exact local evidence and carry serving custody, physical plans, and unacknowledged results independently. |
| A137 | Removing a receipt at closure, onward movement, voter replacement, or initial send leaves the source unable to reconcile a chosen installation. | Persist the exact installation result until the source acknowledges its durable exact record. Keep it retrievable by its original scope while it exists. |
| A138 | Dropping a plan at closure forgets a possible copy. Guarding cleanup by the current slot strands the old plan. Releasing an empty slot without a fence lets queued creation take effect without custody. | Charge the immutable copy plan before dispatch. Settle it with the original custodian independently of admission and fence the exact copy key before releasing its charge. |
| A139 | An unacknowledged earlier result can fill the result budget while a second irrevocably sealed move has a ready image and nowhere to record installation. | Reserve result capacity before granting authority to seal. Release it on exact abort or acknowledgment of the source's durable result. |

[Activation retirement comparison and proofs](36-intent-retirement/report.md).

## Study 37 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A140 | A partial, stale, or rekeyed image loses or resurrects an obligation. An acknowledgment applied after capture also diverges from the installed image. The install can drop existing charges. | Freeze the book under the authority seal. Install its exact unresolved bindings, original physical keys, refusal fences and charges. Discharge only on exact durable evidence at the current open owner. |
| A141 | Publishing staged ownership exposes a target without an installed cut. An old announcement can later send fresh lookup back to a stopped endpoint. A cached stale address can synthesize terminal absence. | Resolve a stable home through one monotone binding published only from a certified install. A stale or unreachable endpoint supplies no terminal answer for an unresolved obligation. |
| A142 | Shutting down before publishing leaves only a dead route. Keeping every forwarding endpoint up until settlement can hold all predecessors indefinitely behind a counterpart outage. | Require independent discoverability at a published successor before planned predecessor shutdown. Carry obligations forward without waiting for their counterparties. |
| A143 | After loss of all independently reachable result or discovery evidence, different legitimate installation results can yield the same observations. A permanent locator outage before publication can also prevent safe shutdown. | State the discovery and endpoint premises for reconciliation and planned shutdown. A cached route helps while its certified owner remains available. |
| A144 | A move can overtake each fresh lookup forever, including when discovery always works and delivery is weakly fair. | Require enough stability to deliver an authorized exchange, or a mechanism that establishes the equivalent delivery progress condition. |

[Obligation home comparison and proofs](37-obligation-home/report.md).

## Study 38 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A145 | Restoring external fields from a staged target image erases an installation result the source recorded after staging or a fence the original custodian completed after staging. | Transfer only the target's exact cut. Keep source result intake and original custodian fences under their own durable authorities. |
| A146 | A sealed target can report successful acknowledgment or cleanup and the successor can then resurrect the discharged obligation. Applying to an obsolete revision crosses the write fence. Treating a stale address as terminal strands valid evidence. | Apply exact durable evidence as a command of the current open target. Preserve the evidence for retry after refreshing the route. |
| A147 | Replaying an exact source result can recreate an obligation the target already discharged. | Treat duplicate delivery of the exact durable result as a no-op at the source. It cannot add a new target obligation. |

[Activation composition comparison and proofs](38-activation-composition/report.md).

## Study 39 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A148 | Recovering the learned position drops a chosen but unapplied acknowledgment or cleanup. | Recover the exact ranked sealed command prefix, including hidden choices, and install exact coverage on the current quorum. |
| A149 | Looking up current evidence during replay can turn a refusal into success. Treating a disconnected counterpart as missing evidence can undo a success, and requiring a fresh answer can stop recovery. | Replay from the certified basis with each request and its original validated ordered attachment. A later fact is input to a new command. |
| A150 | An empty original slot can still receive queued creation, and a foreign receipt can clear a different obligation. | Match the complete original registration key and binding. Require a committed exact refusal fence backed by durable issuance and the current receiver control state. |
| A151 | Closing an acquired registration can leave physical bytes behind after the target releases its charge. | Require verified exact absence or durable custody covering all remaining bytes and work before discharging the target plan. Use absence for erasure completion. |

[Certified activation replay comparison and proofs](39-certified-activation-replay/report.md).

## Study 40 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A152 | Treating a producer close, timeout, or sibling completion as effective stop can certify absence while an old write can still land. A provider that checks only at admission can do the same. | Freeze new issuance and verify exact provider-side closure before accepting absence. The version fence or exact one-use completion must exclude effect execution at the provider. |
| A153 | Replaying an old completed write can recreate a deleted version. Restart can also reopen provider-fenced or consumed tickets. | Atomically consume each ticket with its materialization. Preserve the provider fence and one-use decisions through recovery. |
| A154 | Waiting for all tickets can block erasure when one upload never finishes, even while provider control is reachable. A full provider outage can block physical erasure altogether. | Use a verified effective version fence for progress independent of a stalled upload. State provider reachability as a premise for physical disposition. |
| A155 | Tracking visible bytes alone omits authorized writes still in flight. Releasing before takeover, or forgetting takeover at restart, can leave physical work uncharged. | Durably reserve the complete possible footprint and take over issued physical tickets before releasing the target charge. Keep the receiving charge until stable absence. |
| A156 | Requiring erasure first prevents target charge release during a provider outage. Claiming release without erasure or room for takeover loses the physical charge. Omitting receiving release strands its charge after erasure. | Allow an exact durable custody receipt to authorize target release independently of erasure. Preserve the current charge until one disposition is proved. Reclaim both charges after stable absence under fair service. |

[Provider I/O closure comparison and proofs](40-provider-io-closure/report.md).

## Study 41 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A157 | If absence authorizes an old capability, deletion and late delivery can recreate bytes. Retaining each completed marker avoids the replay but grows with all historical writes. | Require an exact positive live row at the effect boundary. Consume it with the effect and reclaim its admission memory without a completed marker. |
| A158 | A separately allocated ticket can be certified closed before delayed registration. A future serial has the same risk. Restoring an old issuance value permits identity reuse. | Allocate the live row and advance the durable issuance watermark together. Certify closure only within the exact durably issued range, and preserve issuance across restart. |
| A159 | Reclaiming before stable absence loses the disposition proof. Route-only delivery or reset namespace issuance lets an old ticket act on the next occupant of a reused address. | Reclaim the old book after stable absence. Keep a non-reused namespace watermark for the address and require the exact current namespace at delivery. |
| A160 | Distinct payloads can leave the same compacted book. | Use issued absence to prove stable refusal. Keep independent exact result evidence for any result still owed. |

[Provider ticket compaction comparison and proofs](41-provider-ticket-compaction/report.md).

## Study 42 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A161 | The learned image can be smaller than the highest accepted recoverable cut. A newly accepted vote can exceed a reservation sized only at prepare time. | Admit every eligible source vote under the durable footprint envelope. Reserve for that envelope, including the initial basis, before sealing. |
| A162 | Staging without final residency, charging the installation a second time, or lending committed workspace can block a sealed move even though the target has a quorum. | Reserve final residency and workspace before seal. Protect the credits through restart and apply them once to the exact image. |
| A163 | A single full-image workspace cannot hold an incumbent and a disjoint replacement at once. Erasing the incumbent for space loses required physical backing. | Reserve the peak coexistence footprint and keep the incumbent protected until exact installation switches the binding. |
| A164 | Installing a different recovered cut loses accepted state. Exact bytes from an unrelated family supply no authorization. | Bind promotion to the exact recovered prefix and the installed quorum of the authorized target. |
| A165 | Publication or timeout can drop an old physical charge prematurely. An inaccessible custodian can keep a properly charged copy outstanding after installation. | Keep obsolete copies charged through verified disposition and make already funded installation independent of old cleanup. |

[Recovery capacity comparison and proofs](42-recovery-capacity/report.md).

## Study 43 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A166 | Aggregate spare capacity accepts a request that overfills its required zone in one transition. | Check capacity pointwise at each physical pool and charge ordinary usage, prepared holds, committed reservations, and retained physical copies. |
| A167 | A partial vector can authorize seal, a timeout or restart can remove committed credit, and charging promotion again can strand a sealed move at capacity. | Bind seal authority to the complete exact durable vector. Preserve the commitment until promotion and use the reserved capacity for that promotion. |
| A168 | Two moves holding disjoint pools and waiting for each other's pool can stutter forever. | Reserve the vector atomically or acquire its preparatory holds in one strict order across the resource pools. |
| A169 | Restart and reclamation without an exact local fence allow a delayed prepare to recreate a canceled hold. | Recover the exact pre-seal abort decision and close admission durably at each affected pool, including initially empty pools, before reusing the capacity. |
| A170 | Promotion that discards the old charge and release against a different move's disposition both lose accounting for live bytes. | Keep obsolete physical bytes charged to their actual pools and release them only against exact matching disposition. |

[Concurrent recovery capacity comparison and proofs](43-concurrent-capacity/report.md).

## Study 44 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A171 | A move holds a unit at one pool and cannot acquire another. A ledger that counts only fully committed vectors offers the already held unit to ordinary work. Adding a committed debit without removing the provisional debit counts the same unit twice. | Count prepared debits in ordinary admission. Bind the complete exact vector to the seal by reclassifying the existing debit. |

[Provisional capacity visibility and conservation proofs](44-prepared-capacity/report.md).

## Study 45 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A172 | A staged copy can miss a later live hold, and an occupancy-only image can lose the floor or a separate undischarged refusal. Requiring the old owner's reply after seal can strand installation. | Install the exact closed pool cut with all live debits, the effective limit, channel issue and refusal state. Use its durable coverage to install independently of predecessor connectivity. |
| A173 | Permanent per-cancel records exceed the issuance window. Granting credit from an offered floor exceeds the receiver's installed debt bound. | Compact certified local closure with the channel floor. Issue new credit only against a durable acknowledgment of installed floor. Keep all outstanding live debits independently. |
| A174 | Accepting a delayed operation at the old controller can allocate capacity after its authority has moved. | Scope the effect to current ownership while preserving the request's immutable physical pool and reservation key across rerouting. |
| A175 | Shrinking below ordinary use plus live holds makes the pool overdrawn in a single decision. | Commit a lower planned limit only after checking full charged occupancy. Carry that limit in ownership transfer. |

[Capacity authority transfer and cancellation compaction](45-pool-authority/report.md).

## Study 46 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A176 | An external pool coordinator irrevocably binds a full vector. The source can then retire before sealing, leaving the vector without a possible legal install or release. | Commit the vector as part of the source's ordered seal against abort and retirement. Keep preparation provisional and charged until that decision. |
| A177 | One pool's receipt or a prior attempt's full vector can appear sufficient to seal while the current attempt lacks funding. | Validate every required receipt against the exact current intent, pool and amount. Preserve its backing until exact abort. |
| A178 | Retirement that drops an outstanding prepare leaves its holds without an abort. Treating later retirement as abort can revoke a valid seal. | If retirement wins before seal, record the exact pending move's abort with terminal closure. Once seal wins, route retirement to the installed successor and preserve the past seal. |
| A179 | A funded seal can stay pending while the source is unreachable if installation requires another source reply. | Install from the already certified exact sealed cut and its protected capacity. Resolve later source-visible results separately. |

[Source-ordered funded seal comparison and refinement](46-funded-source-seal/report.md).

## Study 47 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A180 | Dropping an exact result before its participants settle loses their evidence. A foreign acknowledgment can appear to settle the wrong result. | Reserve the row at issuance. Clear its debt only with durable evidence for the exact outcome and participant. Reclaim it after all its own debts settle. |
| A181 | Prefix compaction strands a fully settled later row behind an unavailable participant on an older attempt. | Reclaim sparse settled rows independently. Preserve still-owed exact rows and account for their full quota. |
| A182 | A lost issuance value makes an authentic old identity look unissued. Absence interpreted as abort can contradict an earlier seal. | Preserve durable non-reused issuance and return only closure from authenticated absence. Retain any separately owed exact response. |
| A183 | Copying the learner loses an unlearned choice or restores a compacted row. A counterpart lookup can strand already chosen recovery during outage. | Recover the exact ranked prefix and replay the original ordered decisions and settlement evidence from the certified base. |

[Source outcome recovery and sparse compaction comparison](47-source-outcomes/report.md).

## Study 48 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A184 | A queued write can still land after logical abort or local admission closure. Refunding the old reservation at either point undercharges physical work. | To settle an abort, close its exact admission key and prove stable absence or transfer the full debit to durable local custody. |
| A185 | Moving the debit to another failure domain leaves the original pool unaccounted. Waiting for erasure strands source result credit during provider outage even if local custody can take over. | Preserve the charge at the physical pool. Distinguish returning the source result slot from returning pool capacity. |
| A186 | An already endorsed custody debit can disappear on local controller replacement, stranding writes after the source has evidence to compact. | Carry exact admitted writes, refusals and charged custody across pool ownership until local disposition. |
| A187 | Receipt delivery before install, evidence for another decision at the same placement, and evidence for another cut can all discharge the wrong target obligation. | Acknowledge only authenticated exact decision and cut evidence backed by the installed target quorum. |

[Source decision, pooled custody, and result settlement composition](48-settlement-composition/report.md).

## Study 49 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A188 | Replaying only a seal's authority change leaves its result planned while the writer is already fenced. | Apply the stream transition and exact reserved result together at the same source command position. |
| A189 | Recovery that reads live evidence can lose an earlier acknowledgment or upgrade a prior refusal. Requiring a participant response can block recovery completely. | Order the exact evidence attachment with the request and replay its original admission and outcome. |
| A190 | Installing the learner's view can lose an ordered command and its result, including controller decisions the learner has yet to apply. | Replay the ranked prefix or tail from a certified joint checkpoint of the stream and result book. |
| A191 | Installation using only the unchanged data LSN accepts evidence for a different position in the command history. | Bind the exact move's install proof to its ordered seal in the certified lineage and its exact inherited history. |

[Unified source command replay and ranked recovery](49-unified-source-history/report.md).

## Study 50 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A192 | The newer visible cut can omit a suffix still needed by the previous durable selector. A borrower can still need an evidence object after all journal cuts pass it. | Check all crash-selectable suffixes, physical borrows, and outstanding claims before reclaiming an evidence object. |
| A193 | A checkpoint can lose an exact result or leave no evidence it can attest. Trimming its original record then strands an outstanding participant. | Keep the exact result and its admissible reissue evidence in the certified image, or retain an independently charged original or equivalent object. |
| A194 | Two legally ordered aborts at different positions can leave equal joint states. | Give a new state attestation its own certified cut. Retain the original position and response evidence while an original reply is owed. |
| A195 | The result row count only bounds bytes given a ceiling on each encoded row. Concurrent selectable images can each carry all live results. | Cap encoded headers and rows and reserve the combined control space for both selectable images. Charge retained evidence and physical dependencies separately. |

[Joint checkpoint and evidence reclamation](50-joint-checkpoint/report.md).

## Study 51 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A196 | Individually readable control, data and evidence can describe different states at the same data frontier. | Authenticate their complete immutable names in one envelope. A control-only cut can reuse an unchanged data root by naming it in its new envelope. |
| A197 | Checking a numeric frontier or position can admit an earlier cut or foreign lineage. | Select the expected lineage, format, ordered position, prefix commitment, and data frontier together. |
| A198 | Accepting trailing bytes gives the same decoded header more than one byte representation. | Parse one canonical domain-tagged message and authenticate those exact bytes. |
| A199 | A manifest can appear registered while a required descendant is missing, or a descendant can be reclaimed after a pin. | Require exact manifest coverage and durable custody of every needed dependency through all protected uses. |

[Canonical checkpoint envelope and verified component opening](51-checkpoint-envelope/report.md).

## Study 52 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A200 | Billing each logical use against the physical limit can prevent sharing at capacity. Deduplicating by content can omit the debit of a distinct copy. | Debit each immutable physical allocation once at its actual pool, and account separately for each logical use. Precharge a separate copy or repack before writing it. |
| A201 | Releasing a reference can strand present bytes or an independent old borrow. An absence receipt for another copy can return the wrong credit. | Retain the charge through surviving references, borrows and possible writes. Return it only on exact stable absence for its original physical version. |
| A202 | Controller recovery that drops its debit book can leave an existing allocation uncharged. | Preserve exact scoped debits and their logical and provider obligations through controller replacement. |

[Concurrent physical extent accounting and shared custody](52-shared-extent-accounting/report.md).

## Study 53 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A203 | A foreign image can join the placement under an unbound receipt. Counting two pools in one AZ reports protection with only one surviving failure domain. | Bind exact installed physical coverage to the current recovery input. Count coverage after each permitted AZ removal. |
| A204 | Refunding on loss omits possible old bytes. Waiting for the old custodian leaves a ready replacement unable to complete evacuation. | Order placement withdrawal independently from exact physical disposition. Preserve the old charge and borrows through faults and withdrawal. |
| A205 | A full destination can overallocate if admission spends capacity from the offline original pool. | Precharge eligible capacity at each destination's actual physical pool. |
| A206 | Withdrawing while there is only one remaining domain turns a planned action into a reduction of the fault envelope. | Verify protected coverage of the resulting placement before planned withdrawal. |

[Physical pool evacuation and independent disposition](53-pool-evacuation/report.md).

## Study 54 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A207 | Installing a voter family with two voters in one AZ can lose the journal majority while every separately placed object remains readable. | For each permitted fault, verify the current distinct voter majority and exact physical input coverage under the same failure. Use the exact installed basis to bind every selectable recovery plan. |
| A208 | A visible checkpoint can supersede an old attachment before a crash stops selecting the old view. | Preserve the complete stable and visible recovery paths until durable selector resolution. |
| A209 | Covering the named checkpoint components while skipping suffix attachments can permit immediate removal of a required replay input. | Include the typed envelope and components, all their required descendants, and the exact suffix attachments in each selectable plan. |
| A210 | An old verifier observation can certify a newly installed voter family if authority scope is unchecked. | Compare the original certification request with the current exact family and ordered prefix before evaluating the current recovery inputs. |

[Joint recovery cut across selectors and fault domains](54-joint-recovery-protection/report.md).

## Study 55 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A211 | Refunding an incarnation on fault leaves outstanding custody without its row. Counting only online pools can admit more unresolved scopes than the inventory can hold. | Precharge a durable slot for every incarnation and retain it through outage and withdrawal. |
| A212 | A returned pool can be reopened using a matching book in another namespace, a proof from before a more recent loss, or a stale physical book. | Validate authentic evidence against the exact registered scope, current access epoch and current recovered book. |
| A213 | Timeout can remove the row without closing its original physical obligations. Reusing an absent issued identity could make delayed evidence relevant again. | Forget only after exact terminal namespace closure and cleared custody. Register new storage under fresh durable issuance. |
| A214 | Conditioning retirement on room for new scopes can deadlock at full inventory even after terminal evidence is available. | Keep verified retirement and return validation available at the limit. Allocate a fresh scope only when there is room. |

[Bounded pool incarnation inventory and exact return validation](55-pool-incarnations/report.md).

## Study 56 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A215 | Wrapping an exhausted issuer can reissue a previously settled scope. | Refuse fresh registrations at the ceiling and leave exact settlement and already admitted operations available. |
| A216 | Saturating the access epoch while allowing return lets a receipt from before the latest fault authorize reopening. | At the last epoch, a fault makes the original incarnation terminal for serving and preserves all original charges. |
| A217 | Selecting a valid older checkpoint and using its watermark directly permits reissuing an already chosen scope. | Restore the exact certified ordered suffix and all current issuance and phase fields before admission. |
| A218 | Bounding row count alone leaves the representation and simultaneous image cost unspecified. A terminal row can decode as a usable epoch if its phase is lost. | Use fixed-width canonical ordered rows, an explicit terminal phase, and a byte reservation for both selectable bodies. |

[Finite counter exhaustion, exact recovery and inventory encoding](56-finite-inventory/report.md).

## Study 57 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A219 | A single vote can expose a registration receipt for a decision the authority has yet to choose. | Confirm the exact chosen command and its ordered application before publishing the result. |
| A220 | The last learner can be behind a chosen issuance. A single accept can be ahead of the chosen head. | Resume at the exact installed cutoff from ranked recovery, preserving earlier choices and requiring certified installation for selected candidates. |
| A221 | New external evidence can change an earlier refusal if replay consults the current counterpart. | Apply original evidence and the original rule version at each ordered position. Order new evidence separately. |
| A222 | Publishing a newer base can leave an older base selectable while more inventory decisions are already chosen. | Open the certified inventory and custody state of the actual selected base and read the exact suffix through the installed cutoff. |

[Ordered incarnation decisions and ranked media recovery](57-ordered-inventory-recovery/report.md).

## Study 58 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A223 | A write checked before dispatch can land after an effective fence. | Check and consume the positive exact permission at the same durable operation that materializes the guarded payload. |
| A224 | A create-on-absence write can recreate cleared data. A repeated comparison value can let the same request write to a replacement. | Retain a compact guard for a provisioned slot and require a non-reused scoped generation for its next allocation. |
| A225 | Restoring a stale guard can reopen provider effects after the authority recorded closure. | Preserve the authoritative guard and generation through provider recovery. |
| A226 | Clearing the current payload can leave a queued stage or a retained version consuming storage. | Require separate exact stable absence for all auxiliary work before declaring disposition or returning its charge. |

[Atomic storage effects and guarded slot reuse](58-storage-effect-boundary/report.md).

## Study 59 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A227 | An old create checked before dispatch can recreate a guard after acknowledged namespace closure. An address-only check can accept the old create during fresh provisioning. | Authorize creation at the durable effect boundary for the exact current funded namespace and planned address. |
| A228 | An empty observation can certify closure while a delayed create still has authority. Waiting for every create reply can prevent closure indefinitely. | Fence the nonempty namespace before draining. An authoritative exactly empty bank can close and exclude delayed creation in one durable decision. |
| A229 | Allowing fresh child grants after sealing can add physical work while retirement is draining existing custody. | Close new child admission at the parent and keep the original charges and effect fences for work already granted. |
| A230 | Clearing the planned guards alone can leave outstanding auxiliary work. Forgetting prior generation history at the root can admit delayed requests after reuse. | Verify exact auxiliary closure as part of terminal evidence and retain the non-reused root watermark across settlement and recovery. |

[Durable provisioning root and scoped namespace retirement](59-namespace-closure/report.md).

## Study 60 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A231 | A retirement receipt can escape before the command bytes or their recovery address are durable. A power loss can then restore the open namespace. | Back the exact applied retirement with both recoverable bytes and a durable locator before publishing its result. |
| A232 | Opening the selected base before suffix replay can reopen a scope with a valid published retirement receipt. | Restore each selected root through the full authenticated chosen cutoff before new admission. |
| A233 | An intact frame may survive beyond the authorized prefix. Applying it can change provider authority without a chosen decision. | Validate and stop at the exact certified cut. |
| A234 | A retirement can be durably chosen before its original process applies it or sends its result. | Recover the original transition and its scope from the chosen suffix and publish a result only after applying it. |

[Durable root receipts and exact journal recovery](60-durable-provisioning-root/report.md).

## Study 61 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A235 | A second completion for a finished read can consume another live read's hold on the same version. | Allocate a non-reused exact read identity and consume its live entry once, using authenticated evidence of completion or effective stop. |
| A236 | A root reference can remain live after the deployment's ordered retirement. | Close fresh deployment-scoped read admission at retirement and prevent new references under the retired authority. Carry each previously granted hold through its own settlement. |
| A237 | Waiting for every borrower of a shared version can leave retirement pending forever after all custody owned by the retiring deployment has settled. Detaching a private version can also leave its bytes intact. | Resolve the retired deployment's own references and borrows. Certify disposition of each original physical version in its exact erasure scope. Independent custody outside that scope remains valid. |
| A238 | Refunding on stream close returns physical credit while the private version still occupies the pool. | Keep the original debit through logical closure until exact physical disposition. Return that capacity to the shared pool for ordinary admission. |

[Regional retirement, exact borrows, and independent capacity reuse](61-regional-retirement/report.md).

## Study 62 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A239 | A free-space quote can be spent twice after a competing grant. | Durably precharge the full exact window against current pool occupancy before publishing its authority. |
| A240 | An ordinary ordered append without a paid window can grow stream history. A paid window still has usable capacity when the pool is otherwise full. | Bind every successful append to its stream's exact prepaid window. Consume its existing debit locally. |
| A241 | Two successful appends can own the same range if each checks only its length. | Check the exact current byte cursor, consume a positive fitting range in the ordered append, and advance both LSN and cursor on success. Keep the window watermark across pruning. |
| A242 | Returning the debit of a live window allows new work to compete with already granted journal space. | Protect the exact allocation while the source owns it. After source release keep the debit until original physical disposition. |
| A243 | Replay can lose a prior success when current free capacity changes or is unavailable. | Recover the certified window basis and use the original ordered frame and its attachment for the decision. |

[Precharged journal windows and independent replay](62-funded-appends/report.md).

## Study 63 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A244 | Staging a competing record by logical offset can overwrite bytes behind an earlier vote. | Bind exact candidate bytes to an independently funded physical version before writing. Atomically install the accepted rank and the exact version's recovery binding. |
| A245 | A vote can name bytes missing after a crash, or bytes that survive at an address recovery cannot find. | Prove both byte persistence and recoverable locator persistence before installing a vote that relies on them. |
| A246 | A stage can remain physically live after its debit disappears. A newer vote can also leave an older independently pinned copy in use. | Keep every live stage and exact protected copy charged until its own effect path is closed and the original bytes are stably absent. |
| A247 | A delayed request can write original bytes into a reused physical address. | Check the non-reused scoped generation at materialization and preserve the issued watermark after discard. |
| A248 | One copy cannot replace an accepted copy that must remain recoverable during staging. An independent older pin can require an additional copy during replacement. | Charge the sum of all distinct physical versions that coexist. Deduplicate only shared immutable physical ranges. |

[Staged vote isolation and its physical capacity bound](63-staged-votes/report.md).

## Study 64 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A249 | Another staged frame at the chosen position can carry a different request. | Resolve the original exact frame from the scoped ranked certificate and bind the funded append to that request at its original ordered position. |
| A250 | A frame from another lineage can have the right position and plausible local inputs. | Validate the exact lineage at the frame and selected checkpoint boundaries. |
| A251 | A window installation can change replay authority without changing the logical data LSN. Replaying an earlier suffix with the newest window state changes historical outcomes. | Order installation and pruning with source commands. Open the selected checkpoint's exact source and window book at a common certified ordered position. |
| A252 | Intact physical frames can extend past the chosen cutoff. | Validate the required suffix in order and apply only through the exact installed cutoff. |

[Chosen frame authentication and funded checkpoint replay](64-chosen-append-recovery/report.md).

## Study 65 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A253 | A partial vector can seal before the remaining pool has funded its work. | Derive every pool component from the complete set of exact paid extents and bind the vector at the ordered source seal. |
| A254 | An equal amount in the right pool can belong to another move or physical extent. | Use exact stream, move, allocation, and role identity for every owned component and the installed window. |
| A255 | Purchasing the prepared window again excludes an otherwise valid installation at full capacity. | Assign the already charged window to the destination without changing its physical debit. |
| A256 | Returning the predecessor's debit on installation can strand a reader still using the predecessor. | Keep original charges and custody independent of installation until exact settlement and physical disposition. |
| A257 | A replacement can publish its recovered image as a new empty append window and overwrite the image from offset zero. | Fund the fresh window independently of the recovered image extents and require their exact physical roles to be disjoint. |

[Exact prepared vector and destination window funding](65-funded-window-move/report.md).

## Study 66 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A258 | A bare replayed activation can expose the destination writer with the predecessor window. | Install the exact replacement writer and the funded window at the same chosen position. Refuse activation through the ordinary source command path. |
| A259 | A workspace claim can legitimately settle before an earlier source checkpoint replays the installation. | Apply the historical activation using its original authenticated funding and installation evidence. |
| A260 | Restoring older source custody state can revive a pool settlement that already completed. | Recover pool state from its own authority. Intake of an authenticated installation result is scoped to its exact live claim and does not alter its physical charge. |
| A261 | A source checkpoint can carry an older cursor for another stream sharing the ledger. | Restore only the window rows and cursor owned by the recovered stream. Preserve each independent stream's current rows. |
| A262 | Historical activation can remain valid after the destination loses current physical eligibility. | Verify current exact backing and physical scope at fresh service admission. |

[Atomic funded activation and independent recovery authorities](66-move-recovery/report.md).

## Study 67 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A263 | A healthy append window or the visible checkpoint alone can conceal a missing stable-selector or activation input. | Gate fresh admission on the current window and exact coverage of every selectable basis and suffix. |
| A264 | An earlier observation can be valid for a different installed scope. | Bind admission to the current lineage, installed prefix and voter family, selectable checkpoint identities, and the current validated custody revision. |
| A265 | Asking the two survivors of a three-voter group to tolerate another AZ loss blocks all fresh work during the existing single outage. | Use one shared current AZ failure case for the voter quorum and all recovery inputs in degraded mode. |
| A266 | Clearing the observed outage before restored coverage can advertise healthy protection that the current placement cannot provide. | Renew the full fault allowance only after verifying all healthy single-failure cases against current eligible custody and voters. |
| A267 | Historical control validity and immutable input coverage can survive while the serving window's actual AZ is unavailable. | Require the exact window to be eligible and outside the current failed domain at fresh admission. |

[Complete fresh admission and the remaining AZ fault allowance](67-full-admission/report.md).

## Study 68 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A268 | Hoping one log bound implies the other permits excess debt under the opposite configuration. A certified checkpoint and a live replay hold can also constrain trim independently. | Keep the recovery and retained bounds separately enforced. Preserve both the certified checkpoint floor and each active replay hold in the trim decision. |

[Logical projection, acceptance traces, and constructive guard countermodels](68-core-reference/report.md).

## Study 69 · 2026-11-23

| ID | Counterexample or witness | Rule |
| --- | --- | --- |
| A269 | A checkpoint can retain the committed application state while losing the request identity for a still-retained append. | Preserve the exact retained receipt in the authenticated selected basis or its chosen suffix until logical trim. |
| A270 | An occupied LSN or equal payload can match a different grant, request, or lineage. | Reconcile under current read authority against the complete original logical binding and ordered result. |
| A271 | Routing reconciliation through append can extend history for an already committed request. | Resolve retained outcomes by read-only lookup at the certified cut. |
| A272 | Archived receipt rows can remain readable after logical trim. | Apply the current retained floor before consulting any stale receipt and report that floor to the authenticated caller. |

[Exact retained receipt lookup and successor replay](69-retained-receipts/report.md).

## Study 70 · 2026-11-23

[Distributed preparation and ordered seal](70-distributed-preparation/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A273 | Plan → one pool prepares → the source seals. One of two required debits is absent. | Derive the seal's admissible vector from every exact locally funded pool receipt under the same ordered intent. |
| A274 | Plan → prepare → timeout or pool restart. The debit disappears while the delivered receipt can still be used. | Keep the prepared debit in original durable custody through restart and coordinator replacement. Reuse the original receipt for exact retries. |
| A275 | Plan → abort → local fence → pool restart. Losing the fence reopens the exact canceled scope. | Recover the effective fence independently of any outstanding hold. Settle delayed pre-fence preparations under the same ordered abort. |
| A276 | A coordinator stops after a partial prepare and the source never orders a result, even if both pools later respond. | State decision progress conditional on reachable ordered authority and fair recovery. An unavailable coordinator never delegates the terminal choice to a pool. |

## Study 71 · 2026-11-23

[Late preparation and exact terminal closure](71-delayed-pool-prepare/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A277 | Abort → delayed prepare → attempted seal. The prepared grant can exist physically after the source has decided. | Admit a verified historical plan only at its open original local gate, atomically charge its debit, and require fresh source readiness for the seal. |
| A278 | An empty pool can acknowledge a source abort before it closes admission. Takeover can later remove an acknowledged local fence. | Require durable exact scope closure before acknowledgment, including on the empty path. Carry that closure through takeover and floor advancement. |
| A279 | Closing a preparation can leave an already issued provider effect. Returning the charge on the fence exposes unbacked physical work. | Keep the exact charge through every remaining effect. Acknowledgment can transfer responsibility to the original charged custodian. Refund requires stable absence. |
| A280 | A provider can otherwise issue a fresh ticket after preparation closes while the old debit is still charged. | Couple issuance of each new provider ticket to the live exact local grant. Let completion of previously issued tickets run under retained custody. |
| A281 | Compaction removes the individual spent marker. If preparation ignores the installed floor, the old scope can acquire capacity again. | Use the recovered scope-checked floor as durable refusal for absent older grants. Guard physical reuse with a fresh non-reused identity. |

## Study 72 · 2026-11-23

[Pool-local physical identities and joint recovery](72-pool-local-issuance/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A282 | A newer preparation can have capacity and stay blocked by an older undelivered plan's preassigned physical serial. | Issue stable logical custody keys in source plans. Allocate physical versions in the original pool's local order when the grant first succeeds. Bind the realized exact receipt vector to the ordered source decision. |
| A283 | Two independently issued local serials can be equal. A bare serial conflates their physical custody. | Use the original physical pool incarnation and its local serial as the immutable physical identity. Bind the version to its exact logical scope, immutable footprint, and role. |
| A284 | A pool takeover that independently restores the gate, allocator, or debit component can resurrect an old scope or discard its backing. | Recover the complete joint pool state through one installed ranked history and validate the exact joint cut before fresh admission. Preserve the original debit until stable disposition. |

## Study 73 · 2026-11-23

[Exact realized source seal](73-realized-source-seal/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A285 | A receipt for a different scope at the same pool and price satisfies a pointwise sum. | Retain the exact ordered plan and match each authenticated receipt to its original scope, role, and footprint. Require distinct physical extents. |
| A286 | The original lookup route can change between seal and install. Re-resolution can produce a different vector. | Choose the realized vector in the seal record and carry its original binding into every eligible replay and installation. |
| A287 | An eligible replacement can receive local serial 1 after the previous window used 9. Physical order disables window activation. | Order logical windows by source lineage and activation position. Bind each to its exact physical extent independently of that order. |
| A288 | Disposal of another pool's extent at the same local serial can refund the wrong recovery row. | Match the full original physical identity, custody key, immutable binding and installed move anchor for each refund. |
| A289 | A recovery cleanup action without a role check can return the serving append allocation. | Authorize recovery cleanup for the original recovery roles only and preserve the append window's paid extent through its independent lifecycle. |

## Study 74 · 2026-11-23

[Realized checkpoint and complete settlement](74-realized-checkpoint/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A290 | Settling one of two original scopes at one pool can clear the whole participant prematurely. | Use one acknowledgment per pool only after its original authority certifies closure and exact disposition or retained paid custody for every recovery scope in the original vector. |
| A291 | A newer control body can omit or substitute a still-owed physical envelope field. | Authenticate the bounded canonical realized body at its exact source slot and cut, and recover the original vector with its full scope and role bindings. |
| A292 | The new visible selector can precede the durable selector. Frame retirement then breaks old-basis recovery. | Keep every selectable suffix's exact frames and manifest evidence until both selectors release the dependency or have equivalent certified evidence. |
| A293 | Compacting a completed move can also drop the live append allocation. | Store the current logical window and its exact paid physical identity independently of the settled move record. |
| A294 | A bound on source rows alone allows unbounded realized-body parsing and custody. | Apply the configured extent and byte ceiling to each encoded body before field parsing and reserve space for both selectable control bases. |

## Study 75 · 2026-11-23

[Joint realized source replay](75-joint-realized-replay/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A295 | A checkpoint with the correct source prefix can omit the still-live realized vector or independent window binding. | Certify the entire augmented source image, including exact plan and realized slots, window bindings, and retained append results, at the chosen cut. |
| A296 | A physical frame can contain a different exact allocation with the same ordinal and pointwise funding projection. | Rank and match the complete original frame and attachments, then replay only the chosen suffix. |
| A297 | A current route can resolve to evidence different from the original seal receipt or become unreachable. | Interpret historical commands only under their original authenticated evidence and exact selected prefix. |
| A298 | All participants can acknowledge after target durability but before the source applies activation. Early compaction can leave the source sealed with no vector to activate. | Keep the realized record until the source's own ordered handoff releases it and all original participants settle. |

## Study 76 · 2026-11-23

[Stable journal writer replacement](76-stable-writer-handoff/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A299 | An eligible replacement can needlessly stall while fresh physical allocation, directory publication, or the old worker is unavailable. Its installed journal and window still have room. | Replace the writer through the existing group, preserve its exact paid windows and custody, and require durable placement migration only when the storage authority changes. |
| A300 | An unverified candidate can otherwise submit a higher epoch, or the authorized new worker can serve before seeing the last old commit. | Require exact eligible nomination, validate the current old holder in the ordered source, and require RTDB to apply the returned certified cutoff before serving. |
| A301 | The target can hold an installed journal and remain blocked by the RTDB directory path for selecting the holder or publishing recovery coverage. | Put effective eligibility, writer grant, and certified checkpoint publication in the installed journal. Derive routing hints independently and scope outage progress to enrolled deployments with a usable route. |
| A302 | A generic checkpoint command can otherwise apply the numeric cut without supplying its exact recovery evidence. | Use an authenticated checkpoint publication command and reject the raw effect at the source entry point. |

## Architecture reopening · 2026-11-23

[Common histories and executable comparison](architecture-reopening/comparison.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A303 | An independent regional witness can prevent a reachable paid group from granting a replacement and answering a fresh barrier. Requiring fresh placement for worker recovery has the same unnecessary dependency under allocator loss. | Keep the installed group authoritative for existing funded foreground work. Replace workers via grants and voters via intersecting membership under the same group. Use the funded transfer protocol for a true change of group. |
| A304 | A single vector reservation can block fresh admission when its coordinator is unavailable. Returning to that coordinator or the source after exact installation can strand eligible activation under either admission architecture. | Keep ordered local debits as the reference for separate pools and use atomic operations inside the actual accounting owner. Let a certified installed target activate without its old route or the admission coordinator. Compare a new vector owner only with enforceable spending rights and the same physical charges. |
| A305 | A materialization fence and an exact drain both prevent new bytes after verified disposition. Only the effect fence in the checked comparison can close a permanently undelivered write without observing its terminal completion. | Require proof of stable closure and physical disposition at each exact original scope. Use the effect fence when liveness includes permanently delayed delivery. Allow exact drain when terminal evidence already covers all outstanding work. |

## Study 77 · 2026-11-23

[Ordered worker eligibility](77-ordered-worker-eligibility/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A306 | A signature can remain valid after withdrawal. Matching a worker ID lets old nominations and withdrawals affect its new enrollment. | Order the roster with grants and bind each nomination and withdrawal to the exact live enrollment. Preserve unaffected workers' bindings through other edits. |
| A307 | Removing eligibility can leave an installed holder able to append. Fencing it without a vacant authority can require a replacement merely to retire. | Withdraw the live grant atomically with enrollment. Preserve its epoch and placement anchor in a fenced vacancy. Allow a higher eligible grant or authenticated administrative retirement from that vacancy. |
| A308 | Requiring a new serial for withdrawal can leave a writer active at identity exhaustion. | Limit fresh enrollment against the durable issuance watermark. Bind withdrawal to the row's existing serial and allow settlement and retirement at the ceiling. Include the live rows and watermark in the certified control image. |

## Study 78 · 2026-11-23

[Sealed worker roster](78-sealed-worker-roster/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A309 | A withdrawal changes legitimate writers without advancing the data frontier. An exact-data mount can reopen a withdrawn worker from a stale roster. | Bind the canonical current roster to the chosen source seal alongside the realized storage and funding record. Require durable target import evidence for the same sealed body. |
| A310 | Matching live rows alone permits an older issuance watermark and reuse of a withdrawn enrollment. Substituting a local cache or recontacting the source after verified installation creates a stale grant or unnecessary outage dependency. | Encode the roster and issuance watermark together. Install that exact value at activation from retained evidence. Keep the source frozen after seal and open checkpoint rosters from their exact named control sections. |
| A311 | Every retained seal and selectable control image can carry a full roster. Unbounded or noncanonical representations would evade physical accounting or make equivalent proof checks ambiguous. | Use fixed-width canonical fields with representable identities, unique ordered enrollment rows and a fixed row limit. Reserve the proved section bound for the current roster and each seal slot in each selectable image. |

## Study 79 · 2026-11-23

[RTDB failover on an installed Logkeeper group](79-rtdb-failover/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A312 | A usable route may still name the wrong lineage or placement, and physically staged bytes at the right position can have the wrong request. | Authenticate the installed route, recover the exact certified suffix, and reconcile against the retained original request binding before serving. |
| A313 | A previous genuine barrier can satisfy writer and data readiness checks. Even exact invocation equality permits it if the issuer recycles that identity. | Bind the applied result to the exact non-reused invocation, writer, lineage and ordered position. Require protected materialization and use a fresh issuer scope if issuance state is lost. |
| A314 | Requiring the directory or a fresh allocator in the same-placement path stalls a funded replacement or its first append. | Use the authenticated group-local grant and carry the original physical extent, cursor, and paid window through result reconciliation and the read marker. Refuse fresh work when required exact coverage is missing. |

## Study 80 · 2026-11-23

[Applied barrier receipt](80-applied-barrier-receipt/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A315 | A chosen marker can be refused at application. A later append can change the head before a positive result is emitted. | Issue a positive barrier receipt from the exact chosen marker's successful applied result and retain its original ordered position and cut. |
| A316 | A signed response can carry the correct invocation while an unchecked cut, position, or journal scope is substituted. | Encode one canonical bounded receipt for all scoped fields. Verify the entire received body under the exact journal's result-signing authority. |
| A317 | Requiring a live issuing source at delivery strands a valid receipt after source loss even with protected data and usable verification evidence. | Verify already-issued receipts locally using scoped retained evidence. Preserve an already admitted read's original scope and cut through later ordered changes. |

## Study 81 · 2026-11-23

[Recoverable read admission](81-recoverable-read-admission/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A318 | An exact snapshot pin carries insufficient evidence to recreate a chosen marker outcome after the issuer fails and the original suffix is compacted. A remembered answer with no protected basis can become unreadable. | Order the original marker result and the exact snapshot reservation together. Recover the pair in the authenticated control image and use the paired row to reissue without the compacted marker. |
| A319 | A caller can lose the first permit together with the first result. A duplicate request can consume a second paid slot even when the original read is fully recoverable. | Recover by authenticated original invocation. Maintain one live row per invocation and reuse it without another charge. |
| A320 | A tentative marker followed by terminal retirement cannot authorize a new protected attempt. A delayed old permit can alias recycled capacity if matching stops at the slot. | Allow a fresh retry while live after reconciliation shows no admission. Keep the exact previously admitted result across retirement. Release its basis and row through exact completion or effective stop, and bind later use to a non-reused permit serial. |
| A321 | Reserving recovery forever for each tentative or completed marker conflicts with finite read debt. | Charge one bounded canonical row for each protected admitted invocation and its hold. Stop fresh admission at the slot or serial bound while preserving exact release and reissue. |

## Study 82 · 2026-11-23

[Protected read checkpoint and handoff recovery](82-joint-read-recovery/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A322 | Two states with the same data frontier can have different active reads. Independently loading results and holds can reopen a closed read or bind it to a different basis. | Authenticate the bounded result rows and hold table together at the exact ordered checkpoint or seal. Refuse malformed occupied slots and verify the row-to-hold binding before use. |
| A323 | A valid read table does not by itself preserve the actual old roots and suffixes. | Derive the required physical dependencies from the restored live bases and check the named manifest's retention before opening or activating. |
| A324 | An acknowledgment from a sealed predecessor can conflict with the unchanged read state the target must inherit. A target can also replay an obsolete cached row after it closes that row. | Freeze the sealed logical book. Order logical close at the installed successor against its current restored state. Carry exact physical stop evidence independently. |
| A325 | Recontacting the old route after exact installation can block eligible service. Putting a full image into its own protected read attachment creates a circular reference. | Bind a read-only attachment to the chosen seal. Let the funded target open it locally and reissue with the original hold and invocation. |

## Study 83 · 2026-11-23

[Ordered read replay](83-ordered-read-replay/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A326 | The correct projected journal command and ordinal can correspond to different read evidence, and a bare read marker cannot establish protected admission. | Choose and recover full protected operations in the journal's frame family. Derive positive results from the joint decision that records the row and hold. Select only the exact full suffix through the chosen cutoff. |
| A327 | Replaying only the data side can omit a chosen close. Releasing by slot can consume an unrelated later hold. | Update the result and hold together in the chosen release. Release only against the exact permit serial and authenticated completion or effective stop. |
| A328 | Recertifying already ordered evidence through a live endpoint can strand recovery of an otherwise covered suffix. Requiring the stop proof to predict its successor's release ordinal makes the endpoints depend on one another. | Replay immutable evidence under its original rules. Bind physical completion or stop to the exact original permit. The chosen logical command assigns its own ordinal. |
| A329 | A historical certificate can remain valid when current backing or serving authority is unavailable. | Serve only after ordered recovery and a separate current authority and custody check. Retain the distinction between historical validation and current entitlement. |

## Study 84 · 2026-11-23

[Read invocation floor](84-read-invocation-floor/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A330 | Reclaiming an exact result and hold can remove the last per-invocation evidence. A delayed request can admit again after the cut has changed. Exact arbitrarily ordered deduplication must distinguish every possible spent subset. | Keep a fixed-width consumed floor for the current writer grant. Consume exactly the next nonce with the chosen protected admission. Keep the floor through close, compaction, and ranked replay. |
| A331 | A largest-seen watermark can silently discard an unresolved lower nonce. Enforcing exact next without a way to resolve a missing request can stall later requests. | Permit the installed writer to order an authenticated abandonment for the exact next nonce. Preserve the existing read book and charge only control progress. |
| A332 | Rotating or wrapping nonce space without an authority fence can reuse a spent identity. Applying the new scope check to retries would lose a live protected predecessor result. | Reset the floor on a strictly newer scoped writer grant and stop at fixed-width exhaustion. Fresh admission validates the exact active grant. Reissue by authenticated original invocation against the retained row. |
| A333 | Adding the floor only to live memory or selecting it separately from its journal and read book allows rollback after crash. | Include the canonical floor with the exact authenticated combined control at its ordered checkpoint. Replay admissions and abandonments through the same chosen cutoff. |

## Study 85 · 2026-11-23

[Ranked named recovery](85-ranked-named-recovery/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A334 | The last learned prefix can omit a chosen close, and the longest durable report can belong to an older ballot. Requiring every predecessor voter can stall an eligible recovery. | Derive the cutoff from the highest ranked exact durable report of an intersecting fenced quorum. Carry every earlier choice even when the learner died. |
| A335 | The same ordered position and data frontier can name a rival control body. A correct cutoff alone supplies insufficient local bytes. | Bind the named checkpoint to its certified exact historical prefix and original typed image. Open its authenticated contents and verify the complete local suffix through the ranked cutoff before staging. |
| A336 | A fenced quorum identifies a recovery candidate ahead of target installation. Requiring target installation before staging creates a cycle. Multiple reconstruction attempts can yield different eligible candidates. | Stage first. Choose one exact durable image and history in the existing successor installation slot, then publish from the staged result and that choice. |
| A337 | A retained installation can be authentic after the successor is replaced, after it has made further progress in the same revision, or without a live target quorum. | At initial publication compare the expected lineage, exclusive successor revision and exact current ordered frontier. Require a live target quorum with exact seed recovery through the latest accepted witness. Reconcile an old installation separately from activating it. |

## Study 86 · 2026-11-23

[Atomic recovery publication](86-atomic-recovery-publication/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A338 | A valid preliminary comparison can go stale before publication. Restarts and reusable addresses allow equal frontiers under different scopes. | Capture the local publication session before staging. Compare the entire current lineage, revision, exact ordered frontier and session while filling the empty slot at the effect itself. |
| A339 | A second bootstrap can replace a live book. Separately updating the local frontier and image admits an inconsistent observation. | Give bootstrap only the empty-slot transition. Apply the chosen suffix under its exact journal scope and update the live image together with its ordered frontier. |
| A340 | A remote quorum can become unreachable after the last response and before a local publication. An attached image or a historical installed certificate cannot authorize fresh work. | Keep the authoritative install at the existing quorum decision. Treat local publication as materialization. Require each fresh use to have its own current ordered authorization and exact protection at admission. |
| A341 | Rechecking a live quorum at delivery can strand an already admitted exact result. Ignoring an effective stop can expose inputs after the permit becomes unusable. | Continue with the original scoped physical borrow and exact result while that borrow holds. Seal the admission token against construction and changes outside its guard. |

## Study 87 · 2026-11-23

[Ordered reply admission](87-ordered-reply-admission/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A342 | A fresh quorum probe can cover a prior ordered close and can also race with a close after observing a still-live result. A data frontier alone omits these control changes. | Use the command frontier for freshness. Order recovered reply authorization with closure in the existing installed journal. |
| A343 | Slot reuse and a sealed source can both leave plausible cached result evidence. A legitimate old caller may have lost its permit. | Look up the original invocation and check the exact current live row, permit serial, basis and installed logical owner at application. |
| A344 | An overtaken frame cannot keep its intended order. Making physical reservation predict the winning ordinal forces needless repricing and another trip to the provider. | Bind the physical proof to the exact original operation and basis. Keep the ordered position in the frame header. Permit reframing the same paid operation while its exact basis remains live. |
| A345 | Ready metadata, or an old positive read result alone, cannot supply physical permission. Requiring the current journal at completion can strand a chosen result whose own borrow remains held. | Authorize the reply token only from the exact chosen successful frame and paid proof. Complete against that same independent borrow. Reissue existing protected retired results under their original paid backing. |

## Study 88 · 2026-11-23

[Retained delivery evidence](88-retained-delivery/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A346 | An authorized delivery can stay live after its original read closes and its slot is reused. Coupling their records erases a paid result. | Make authorization and its independent delivery record one ordered transition. Preserve the original result, permit, basis and physical operation while that delivery remains outstanding. |
| A347 | A live slot can be overwritten at capacity, and a cleared slot can reopen an old identity after the last row is removed. | Use a separately funded finite delivery book with a non-reused issuance floor. Bind the paid proof to its exact delivery key independently of the global frame position. |
| A348 | The visible checkpoint can contain the record while the older crash-selectable path still needs the original frame. Pinning that frame forever blocks replay compaction. | Include the canonical delivery book in each named checkpoint and validate independent physical dependencies. Reclaim the old frame when every selectable path covers the result and no replay or borrower still uses the frame. |
| A349 | A result row can remain valid while its physical operation stops. Settlement of another physical binding can race slot reuse. | Require the exact still-held original borrow at completion. Authenticate exact original-custodian settlement before clearing the named slot and keep the issuance floor. |
| A350 | A finite count of entries supplies no byte bound if a row can store an unbounded proof or payload. | Keep the canonical fixed-width row and counter in the control image. Charge each selectable and retained seal copy and its physical custody separately. |

## Study 89 · 2026-11-23

[Sealed delivery handoff](89-sealed-delivery-handoff/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A351 | The same data LSN can have a different read or delivery state, and the correct ordinal alone can label a split control image. | Admit the prospective seal with one authenticated attachment whose decoded read book, writer nonce floor and delivery book match the actual applied seal. The seal binds that exact attachment at its ordered position. |
| A352 | Logical read closure can hide a still-outstanding physical delivery, and source recontact can strand a fully mounted move. | Require the named manifest to cover the dependencies of both books. Apply the existing target installation once the exact cut and its dependencies are durably available locally. |
| A353 | Placement replacement can reopen an exhausted physical identity or lose the original custodian if it resets counters or rebinds entries. | Preserve the complete delivery book and its lineage-wide issuance floor across placement changes. Preserve each row's original physical binding and carry the separate writer-scoped floor through the normal grant transition. |
| A354 | A sealed predecessor can acknowledge clearing a row that the successor must still restore from the frozen cut. | Apply ordered clears at the installed owner using authenticated terminal evidence for the original physical borrow. Keep original paid custody while the dependency remains unresolved. |

## Study 90 · 2026-11-23

[Terminal delivery witness](90-terminal-delivery-witness/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A355 | A provider can stop a delivery during the sealed interval and leave a fully prepared target waiting forever for a delivery-only extent or provider response. | Allow exact, independently durable original-custodian terminal evidence to realize a stopped delivery's recovery obligation. Authenticate it against the sealed lineage, delivery key and original physical binding. |
| A356 | An extent may serve several independent needs after one delivery stops. | Require continuing coverage for base replay, installation and protected reads, and require exact terminal evidence for every dependent delivery before substituting for an unavailable delivery-only extent. |
| A357 | An unchosen clear at mount changes the authenticated book, and converting the receipt into physical permission can revive a stopped effect. | Recover the same sealed book and counter under either realization. Finish only under the original live borrow. Apply the exact stop in the installed owner's ordered settlement. |
| A358 | A valid proof in memory can allow activation followed by unrecoverable selector loss. | Stage authentic terminal evidence durably for each admitting realization before it can replace extent coverage. Charge the witness while any selectable path still needs it. |
| A359 | A receipt in the visible target can coexist with an older selectable base that still requires the extent. | Authorize disposal only when every selectable basis and suffix has a verified post-disposal realization, with its dependencies and receipts available. Keep physical disposal under the original provider fence. |

## Study 91 · 2026-11-23

[Receipt selection and reclamation](91-receipt-selectors/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A360 | A replacement can point to an exact receipt with an unstable name or to a stable name with foreign bytes. | Before publication verify durable exact bytes and durable discovery for every named receipt on the newly selectable path. |
| A361 | Ordered settlement clears its row while an older selectable basis can still need its exact proof to replay. | Put the exact bounded evidence in the chosen settlement frame by default. Keep that frame while any selectable journal suffix uses it. |
| A362 | Choosing a new visible root does not retire the old crash root or revoke a live borrower. | Permit removal of a separate receipt only after all selectable paths and independent pins release its original name. |
| A363 | Permanently keeping terminal receipts prevents bounded replay storage even after all consumers release them. | Make protection follow exact selectable dependencies and pins. Schedule independent collection when both sets release the evidence. |

## Study 92 · 2026-11-23

[Fresh observation and exact recovery](92-read-contracts/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A364 | A new latest observation and an exact reissue can legitimately require different results after the same lost reply and subsequent advance. | Expose their different semantics at the caller boundary. Use fresh invocation evidence for latest-only observations. Recover a protected original only by its exact identity, and serve named bases only under their retained authorization. |
| A365 | A data-only floor can hide prior retirement. A valid earlier probe can outlive its scope or local process gate. | Check the ordered applied frontier, installed scope and exact local gate and session when acquiring a standing borrow. Keep the full basis protected independently while that borrow lives. |
| A366 | Resampling fresh after recovery cannot distinguish absent receipts for two different original answers. | A caller that needs exact ambiguous-result recovery supplies an identity known before the decision. Retain distinguishing evidence for the promised window and refuse when exact authority or evidence is missing. |
| A367 | A probe that saw a live exact row can race an ordered close, and recontact at completion can strand an already admitted borrow. | Keep ordered exact reissue against logical close. Complete admitted work under its own still-held exact borrow without recontacting the authorizer. |

## Study 93 · 2026-11-23

[Atomic capture and first use](93-atomic-read-capture/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A368 | Preparing against one exact candidate basis can lose to a newer checkpoint on every attempt. | Keep split capture with protection of the chosen basis. Fuse first use only when prepaid custody can cover the exact applied basis without preselecting that basis or ordinal. |
| A369 | If the provider can revoke a delegated unused charge independently, the group can choose an operation whose protection already disappeared. | The installed authority orders assignment against the exact unused fence. Keep the provider charge until authenticated evidence permits the corresponding physical settlement. |
| A370 | Successful read capture can otherwise escape a failed first-use decision. | Publish both exact entries in one fused command. On failure leave the read nonce and both books unchanged apart from normal ordered refusal. |
| A371 | Tying unused settlement to the original writer can strand funds after ordinary worker replacement. | Let the installed owner fence an exact unused key under authenticated original credit evidence. Preserve the issuance frontier through replay and refuse reuse or unused return after assignment. |
| A372 | Recontact at result completion can strand work that already owns independent backing. | Keep first delivery under ordinary exact held-borrow completion and settlement. The open command and subsequent release retain their separate evidence requirements. |

## Study 94 · 2026-11-23

[Standing read credit](94-standing-read-credit/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A373 | A per-request delivery serial allocated during physical preparation can leave a gap when the old provider disappears without portable settlement evidence. | Delegate a bounded physical serial range to the installed window. Assign the next logical delivery serial and its exact physical borrow together at journal choice. |
| A374 | An original provider can miss a chosen assignment before its window is retired. A successor may still have independent funding. | Freeze the exact chosen delivery book at the window's retirement cut and keep original custody until each outstanding exact assignment settles. Install the successor against its own paid window. |
| A375 | A funded receipt surviving retirement can be replayed after an intervening window, resetting the old physical issuance cursor. | Carry a durable lineage window watermark and require a strictly newer authenticated generation. Maintain globally disjoint immutable ranges under the original pool allocator. |
| A376 | Old pins and replacement coverage can overlap at full physical capacity. | Account for both charges. Wait for actual headroom or retain a separately funded path, and never spend the still-held original extent twice. |
| A377 | Optional first-use coverage may lag ordinary head and checkpoint publication. | Keep optional fusion outside ordinary write and checkpoint admission. Refuse an uncovered fused basis and use a separately funded path when available. |

## Study 95 · 2026-11-23

[Standing credit recovery](95-standing-read-recovery/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A378 | Closing the last delivery leaves spent physical identities. A crash can select a checkpoint before a later chosen spend. | Bind the installed generation, archived grant name and spent cursor to each exact checkpoint. Reconstruct all chosen standing decisions through the selected cutoff before new use. |
| A379 | The last physical serial can fit its field even though the fully spent cursor cannot be persisted. | Bound the reserved count so its exhausted cursor fits. Persist exhaustion exactly and refuse new use once the range is spent. |
| A380 | Treating optional live funding as a historical replay requirement can block ordinary recovery. Treating archived evidence as live authority can admit unfunded work. | Use durable historical proof to recover. Require current exact coverage before submitting a new fused frame. Bind that live admission to the exact application state. |
| A381 | A recovered grant with the correct lineage and counter may still belong to another placement. | Reopen current standing credit only under its exact historical placement and installed generation. |
| A382 | Transferring an active original grant can reopen its provider range. Resetting the generation on activation permits the same reuse through reinstallation. | Bind the exact frozen original grant and cursor alongside the delivery book at seal. Activate with the inherited watermark and no live standing grant. Keep original custody settlement independent. |

## Study 96 · 2026-11-23

[Standing provider settlement](96-standing-provider-settlement/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A383 | Provider silence can hide a chosen original operation. | Install the authenticated exact frozen set at the original provider and preserve existing operation states. A still-unused original assignment may enter under that exact set and its original paid charge. |
| A384 | A late effect can resume if delivery authorization checks the seal or receipt while overlooking terminal provider state. | At the effect boundary require the exact live allocation, compatible frozen row, and still-running operation. Keep authenticated terminal states for the lifetime of the live allocation. |
| A385 | Logical drain proves no more effects can be admitted but does not prove physical absence or authorize a different scope's refund. | Return the original charge through guarded pool refund only after exact frozen drain and the original physical closure and stable absence. Do not require spare allocation headroom. |
| A386 | An issued ID without a live row can be an already retired original. Keeping a permanent admission tombstone per window can exhaust bounded metadata. | Require positive membership in the exact original physical ledger. Retain the durable provider issuance frontier and forget the retired enforcement row after refund. |
| A387 | A delayed conflicting freeze could otherwise re-enable an old effect or lose an outstanding original borrow. | Once installed, preserve the exact frozen book for that window across retries. Keep externally needed receipt and recovery evidence under its independent retention rules. |

## Study 97 · 2026-11-23

[Settlement workspace](97-settlement-workspace/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A388 | An older job can hold shared control workspace while waiting for an unreachable counterpart. Fair local execution then leaves an unrelated ready refund stranded. | Keep remote waits in the prepaid exact obligation. Use shared owner-local publication workspace only when the exact evidence is locally verifiable. Schedule ready work independently of pending peers. |
| A389 | A fully occupied ordinary budget can prevent the very publication that would free it. Dedicated workspace per obligation costs one reservation per simultaneously admitted obligation. | Precharge the actual peak of shared publication separately from ordinary admission. Authorize exact refund without new ordinary room. Account for dedicated queues if they are used. |
| A390 | A tentative write or another allocation's proof can appear sufficient before the original refund becomes durable. | Revalidate the exact live row and its own closed, absent state at publication. Retain original charges across an interrupted stage and resume under the durable local ledger. |
| A391 | New ready jobs can starve an older ready job under weak fairness of individual acquisitions. Scanning an increasing unbounded serial range can delay wrap indefinitely. | Give the ready set a bounded turn. A reference scheduler advances a local cursor over fixed slots and selects the next ready slot. Validate the exact non-reused allocation identity independently of its slot. |

## Study 98 · 2026-11-23

[Settlement redo](98-settlement-redo/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A392 | A visible refund can vanish from a legal predecessor after dependent ordinary reuse has become durable. | Admit reuse only after every selectable recovery path covers the exact refund in the same order as the dependent charge. Use the original pool's existing command order. |
| A393 | Synced redo bytes without a durable locator do not support exact pool recovery. | Before reporting a refund from redo, require exact durable bytes and their recoverable location under every selector that still needs the command. |
| A394 | Reclaiming a refund frame based on the visible replacement can remove a dependency of the durable predecessor. | Recycle the redo extent only after every selectable root and independent live pin releases it. |
| A395 | A retained refund can consume the headroom its next checkpoint needs. | Fund the physical overlap of outstanding redo and alternate image staging and selection. An image-only variant can use a smaller reserve when reporting waits for a stable selector. |

## Study 99 · 2026-11-23

[Degraded evidence](99-degraded-evidence/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A396 | The same ready surviving quorum can occur with another AZ slow or unreachable. Treating its timeout as a true diagnosis can falsely classify the fault, while awaiting unavailable confirmation can stall admission. | State diagnosis as a separate premise from evidenced surviving eligibility. Compare explicitly authorized exclusion at the installed owner before adopting a changed protection contract. Preserve acknowledged durability and verify full coverage before renewal. |

## Study 100 · 2026-11-23

[Ranked pool refund](100-ranked-pool-refund/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A397 | Recovering a refund while dropping its hidden chosen dependent debit makes the same capacity appear reusable. | Recover the complete exact ranked pool prefix, apply its charges in order, and admit a fresh debit against the current applied scope. |
| A398 | An authentic historical refund receipt can remain valid after its credit has been spent. | Use the receipt to reconcile the exact original outcome. Require a separate successful current ordered debit before a new effect. |
| A399 | One readable selector or equal command length can count an inexact installation. | Attach the complete history and exact backed crash choices to each counted install vote. |
| A400 | Raw staged refund data is distinct from accepted evidence selected at a ranked cutoff. | Reconcile from the chosen installed order. Include a qualifying recorded candidate through the verified ranked installation and keep unselected staging outside authority. |

## Study 101 · 2026-11-23

[Selective read window](101-selective-read-window/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A401 | Strict next-only admission stalls independent later work behind a single lost read. | Use an exact bounded window for a caller that authorizes independent overtaking. Preserve next-only behavior at width one. |
| A402 | Compaction that skips a gap silently consumes an unadmitted identity. Losing a sparse mark permits replay. | Consume only exact admitted or authenticated abandoned nonces and compact only over already spent identities. Normalize the bounded bitmap in the chosen operation. |
| A403 | Equivalent spent sets with different unnormalized floors can give different window-edge admission results. | Certify the canonical floor and bitmap together with the exact grant and ordered cut. Bind the summary to every selectable recovery path. |

## Study 102 · 2026-11-23

[Selective ordered recovery](102-selective-ordered-recovery/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A404 | A result row can close before its nonce becomes contiguous. Clearing both would let a delayed exact invocation reopen. | Atomically mark the authenticated nonce with its existing admitted effect or abandonment. Keep the normalized window independent of live rows and delivery custody. |
| A405 | A recovery path can keep a correct floor while losing sparse marks or sourcing them from a different body. | Bind the packed window to the same named authenticated checkpoint and exact grant configuration. Project the old floor view from that same summary. |
| A406 | Replaying an old base without its complete chosen continuation can recreate a closed read. A seal can still belong to the current grant. | Replay the complete exact chosen suffix from either selectable base. Preserve the original window across same-grant transitions and reset only on a verified newer scope or terminal closure. |
| A407 | A successor's empty bitmap can make a delayed predecessor nonce look fresh, and closing a read can accidentally discard an independently paid delivery. | Check the exact current active grant separately from the window. Keep protected original delivery obligations with their original funding and let them settle independently. |

## Study 103 · 2026-11-23

[Grant read policy](103-grant-read-policy/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A408 | Two window widths can encode to identical packed bytes and decode successfully. | Authenticate the exact lineage, writer grant and configured width at the chosen cut before interpreting the bitmap. Bind the named historical checkpoint to that policy. |
| A409 | Resizing inside a live grant can discard sparse consumed identities and permit a duplicate. | Keep the policy immutable under an exact grant. A width change is chosen with its exact authorized newer grant, a bounded configured width and a fresh window. Existing custody stays in the combined read and delivery body. |
| A410 | A fresh policy offer for unchanged-width ordinary work or replacement adds an avoidable service dependency. | Use the installed width on ordinary work and inherit it on a legal replacement or transfer when no changed policy is chosen. Check the authenticated offer only when one accompanies the transition. |
| A411 | Applying a newer live policy when opening an older certified selector can block recovery. | Verify the selector under its own historical policy and replay the exact chosen continuation. Keep the format bound and chosen proof verification material available to historical replay. |

## Study 104 · 2026-11-23

[Ordered policy verifiers](104-ordered-policy-verifiers/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A412 | A policy can be substituted if a signed approval omits the exact successor, lineage, width or verifier version. | Sign the canonical scoped statement and keep the exact packet inline in the chosen request. Check the signed statement against the applied grant. |
| A413 | Treating retired verification material as current authority admits new offers with an expired version. Requiring the old signer for replacement can stall rotation. | Select a strictly newer bounded verifier in an authorized installed-journal command. Verify fresh policy offers against the exact current version at their ordered position. |
| A414 | Using today's verifier or fetching a live approval to replay yesterday's choice can stall recovery. Skipping the old decision changes the recovered width. | Open the checkpoint's named historical verifier and apply the inline offers and rotations in their exact chosen order. |
| A415 | A visible new checkpoint can coexist with an older crash-selectable root that still requires the former verifier. | Preserve the exact verifier and needed old signed frames while either selector or any independent pin still uses them. Recover verification material from the ordinary chosen suffix and checkpoint. |
| A416 | Keeping unrelated signer history alive forever adds persistent state and a separate availability boundary. | Store each base's applicable public descriptor and the rotations in its bounded retained suffix. Collect unneeded public material under the same selector and custody rules. |

## Study 105 · 2026-11-23

[Service scope and protection](105-service-scope-protection/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A417 | Installed quorum replies certify a current serving cut and leave physical loss unresolved. Waiting on diagnosis prevents service in a ready cut. | Open on the exact current quorum, window and inputs. Exclude an unreachable AZ from serving while leaving the fault interval unchanged. |
| A418 | A timeout followed by a single-copy acknowledgment can lose that work at the first actual AZ loss. Refusing that acknowledgment indefinitely is unavoidable with only one location and indistinguishable fault histories. | Make acknowledgment depend on exact reconstructibility in every credible first-loss case. Reserve enough independent durable placement for progress under uncertainty. Use a narrower case only with evidence of an actual first loss in the exact interval. |
| A419 | Removing a retained copy outside the serving cut can destroy protection for an earlier acknowledgment. | Enforce the post-withdrawal coverage condition with current exact custody at the effect boundary. Keep original resource charges until protected replacement or authorized disposition. |
| A420 | Voting readiness alone can renew the interval with one surviving copy of earlier work. | Before renewal confirm both exact eligible current quorum and reconstructible acknowledged coverage for all first-loss cases. Carry the verified interval through failover and reconfiguration. |
| A421 | Treating an armed service cut as evidence of all durability conflates two scopes. | Reuse the same operation's evidence when it proves both conditions. Require independent reconstruction evidence for any exact required input that voting or window readiness leaves uncovered. |

## Study 106 · 2026-11-23

[Ordered fault interval](106-ordered-fault-interval/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A422 | A protection bit in worker memory or a checkpoint without its chosen continuation can forget a confirmed loss or resurrect it after renewal. | Order both changes in the installed journal. Name the interval by its lineage and chosen start position. Preserve that summary and all needed suffix evidence through both selectable roots. |
| A423 | A previously authentic incident ticket can authorize a single-copy acknowledgment in a later interval. Binding the ticket to a voter family can instead make it unusable after an unrelated replacement. | Confirm only the exact lineage, interval and lost AZ. Carry the same incident through ranked voter changes. Require exact current serving readiness for fresh use. |
| A424 | Historical replay that calls the live detector can stall even with intact evidence and a current recovery quorum. | Replay the inline chosen evidence under its historical scope from every selectable base. Keep it charged while a suffix or independent pin still uses it. |
| A425 | A renewal proof can predate new acknowledged data or a different voter or custody basis. | Choose renewal only with full verified coverage of the exact current basis. Start the next interval at its chosen position. |
| A426 | Invalidating every attempted renewal on each covered append can prevent repair from completing under weak fairness. | Give fully prepared renewal a fair local turn at the owner, after its proof prerequisites are ready. |
| A427 | Carrying repair evidence across all writes can admit renewal with a new uncovered obligation. | Reuse earlier witnesses only with current proof of exact coverage across the intervening changes. Additional uncovered inputs require coverage before renewal. |

## Study 107 · 2026-11-23

[Protection handoff](107-protection-handoff/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A428 | A move can reset a spent allowance, inherit a rival protection section with the same data frontier, or accidentally change an unrelated target deployment's policy. | Bind the exact protection summary and obligations into the canonical seal. Install only that deployment's summary at a later cut of its same lineage. |
| A429 | Waiting for the old source or a full healthy renewal can strand a funded, exact target during an allowed outage. | Activate from its locally verified current basis under the inherited protection cases. Order a valid confirmation or renewal separately at the installed owner. |
| A430 | A correct durable activation can still rely on a copy in original custody. Deleting that copy at activation can lose an acknowledged input on the first loss. | Keep original copies charged while they are needed. Admit withdrawal only when exact remaining witnesses cover all continuing obligations. |
| A431 | Two effect requests can each pass a physical-layout check and jointly leave a single failure domain. | Reserve removals against one ordered survivor set per affected obligation. Remove a version from that set when authorization becomes durable and keep it absent while an authorized effect can arrive. |
| A432 | Counting retained copies can satisfy a threshold while every remaining copy sits in the same AZ. | Verify exact reconstruction for each inherited failure case, including the placement of every counted witness. |
| A433 | Delayed deletion by address can undo a later replacement. | Authorize and apply only the exact physical identity and generation. Return the original charge after its exact verifiable disposition. |

## Study 108 · 2026-11-23

[Withdrawal recovery](108-withdrawal-recovery/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A434 | A crash can choose a checkpoint from before withdrawal, while a scan still finds the copy and infers it is eligible. An older authorized effect can then erase it after a second removal. | Recover and apply the exact chosen original custody phase and holds from either selectable image and its complete suffix. Count only versions still open at the chosen frontier. |
| A435 | An older selectable root or an independent delivery can outlive the root or read that was most recently visible. | Require release of all registered exact references and borrows together with surviving AZ coverage before ordering withdrawal. |
| A436 | Dispatching a staged request can erase bytes without a chosen withdrawal. | Derive positive effect authority only from the exact original row's durable withdrawing phase. |
| A437 | Rechecking the issuer online after dispatch can block independently valid work at the provider. | Allow the dispatched exact effect to proceed through the provider's original-version fence when the custodian is offline. |
| A438 | A probe or disposition for another version cannot establish stable absence at the original allocation. | Settle the original debit only from authenticated exact stable disposition after effective fencing or completion. |
| A439 | Separate volatile eligibility and pending maps can diverge across restart. | Use the original charged custody phase as the common basis for exact holds, witness eligibility, dispatch and settlement. Keep the charge and required evidence until terminal accounting. |

## Study 109 · 2026-11-23

[Dynamic protection](109-dynamic-protection/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A440 | Seeing a version's bytes cannot distinguish one still eligible for custody from one already authorized for withdrawal. | Order the exact acquire and withdrawal at the original custodian. Publish from durable exact registered holds of the immutable plan. |
| A441 | A certificate valid after the first AZ loss may cover fewer cases than the renewed protection promise. Invalidating every certificate after renewal can also strand still-covered work. | Check the current required cases at publication. Reuse held evidence when it still covers those cases. Obtain additional eligible backing for any unmet case. |
| A442 | Recontacting the original custodian at publication can block a complete plan whose exact bytes and durable holds are still usable. | Reuse independently verifiable original receipts for effective registrations and validate current protection and identity at the installed publisher. |
| A443 | Cancel and publish can race, and a timeout after publication can look like an abandoned preparation. | Record one exact ordered outcome at the publishing authority. Authorize abort releases from that outcome and preserve any already published use. |
| A444 | A missing acquisition reply can stall cleanup. Freeing a reference without closing its identity permits delayed acquisition to reopen it. | Settle every exact planned interest from durable cancellation, including unknown outcomes. Fence the original reference at its custodian. |
| A445 | A visible checkpoint can share a recovery frontier with an older selectable root that needs different versions. | Keep both roots' exact registrations through the selector transition, plus any independent holds. Release only after the last authorized use of that scope. |

## Study 110 · 2026-11-23

[RTDB recovery closure](110-rtdb-recovery-closure/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A446 | An inline suffix can read storage. A matching block upload loads the adopted root and its table blocks, and upload, trie and artefact additions add references that serving and compaction later read. A certificate that names only the checkpoint inventory and external payloads can admit an unrecoverable cut. | Derive the recovery obligation from typed replay of the base and every retained frame's decoded body. Include each adopted root's full closure, its upload's tries, and the added tries and artefacts. Over-approximate deletions and stale additions unless a verified replay decision excludes them. |
| A447 | An oversized payload is fetched after term admission and before the stale or hold decision. Its decoded continuation can be any non-oversized body, including a matching upload. | Protect the outer payload of every admitted oversized frame, whether or not its decoded body takes effect, together with the dependencies of the decoded body. |
| A448 | The upload frame at the pinned RTDB names the adopted root only by block index, and the loader reads the provider's latest version. RTDB origin/main adds an upload catalog digest and an oversized payload digest, both conditional on configuration. | Bind each root adopted in the tail, and each oversized payload, to its digest and exact physical version in the recovery certificate. Refuse portable publication of a digestless upload or payload unless authenticated inventory evidence covers it. |
| A449 | RTDB names table blocks per block index. Keying a table body by table path alone aliases the bodies of different roots. | Name each table body by its root and table. |
| A450 | A hold on a logical path survives relocation to a different physical version, and several members of one pack share one carrier. | Bind custody and coverage to the containing physical version. Count failure domains per carrier, not per logical member. |
| A451 | A legacy root without its table digest map cannot establish which table bodies it names. | Require authenticated inventory evidence for a legacy root's table digests before portable publication. |
| A452 | Carrying only the publication cut or position through voter replacement loses the exact receipts. Recontacting the previous publisher can stall recovery. | Retain the exact receipt set in the chosen publication decision. Recover it through ranked membership from either crash-selectable image without the previous publisher. |

## Owner decisions · 2026-11-23

[Requirements D01–D06](requirements.md#owner-decisions--2026-11-23)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A453 | No surveyed caller needs exact recovery of a lost read reply, and RTDB re-admits reads at their logical basis. | Remove exact read reissue from the baseline (D01). Keep exact mutation retry. |
| A454 | Journal suffix holds and archives can retain payload bytes past RTDB's erasure deadline. RTDB has one key per deployment, SQL `ERASE` destroys no key, and replay fails closed on a missing key. | Align a journal key-generation rotation with an ordered clean successor checkpoint, revoke the old generation at the erasure commit, and recover from the clean root with a new-generation suffix (D02, RTDB R7). |
| A455 | A one-copy acknowledgement under unclassified loss would weaken the durability promise. | Keep it forbidden (D03). |
| A456 | An exact historical feed needs separately funded retention and conflicts with erasure. | Exclude it from the baseline (D04). |
| A457 | Directory paths in mixed cells cannot carry the installed journal's premises. | Restrict the portable guarantees to installed journals and audit for bypass (D05). |
| A458 | No workload measurements exist for Q01. | Keep the budgets as premises until measured (D06). |

## Study 111 · 2026-11-23

[Maintenance liveness](111-maintenance-liveness/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A459 | RTDB charges every term's claim and recovery confirmation to the fixed maintenance reserve, which only checkpoint trim refunds. Repeated writer replacement before a checkpoint fills the reserve and stalls checkpoint progress permanently. | In installed journals, derive the RTDB term from the Logkeeper grant and drop the per-term claim and recovery confirmation records. Size the reserve for the retained previous upload and the in-flight boundary and upload. |
| A460 | Dropping the claim is safe only while the journal refuses appends from a superseded grant. | Keep the journal's grant fence on every append as a premise of the installed term derivation. |

## Study 112 · 2026-11-23

[Erasure rotation](112-erasure-rotation/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A461 | An erasure that commits while an older root is still crash-selectable can restore erased history, or need the revoked key after revocation. | Commit only when every selectable slot holds a clean root at or after the rotation cut. This refines A445 for erasure. |
| A462 | An old-generation record after the rotation cut becomes unreadable at revocation and breaks recovery. | Carry the key generation on the writer grant and rotate by installing a new grant. The journal's grant fence then refuses old-generation appends. |
| A463 | Revoking held views at commit breaks RTDB's admitted-view contract. | Keep held views until the deadline, then answer `rtdb/erased-under-view`. |

## Study 113 · 2026-11-23

[Worker disposal](113-worker-disposal/report.md)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A464 | Disposal on operator evidence lets a partitioned worker serve bytes that were then trimmed. | Bind serving to a journal-issued lease renewed under an enrolled grant, and dispose a withdrawn worker's holds only after the lease end plus the drift bound. |
| A465 | Grant change and withdrawal leave a superseded worker's holds in place, so a dead but undisposed worker blocks trim forever. | Dispose automatically after lease expiry. Keep operator disposal only as an additional, earlier path backed by an effect-scope fence. |
| A466 | A fence that runs separately from read admission admits reads after the lease has lapsed. | Check the lease at each read admission. Add bounded clock rate error over the lease interval as an environment premise. |

## RTDB conformance replay · 2026-11-23

RTDB `rtdb_replication::replay_closure` (branch `codesign/typed-closure`)

| ID | Finding | Design amendment |
| --- | --- | --- |
| A467 | Table blocks name active search runs that serving and later checkpoints read. Study 110's base closure omitted them. | Include each table block's active search runs in the base closure. RTDB's typed model and production enumeration now do. |
| A468 | A promoting leader's recovery confirmation reads files of historical catalogs below the base, outside every base and suffix closure. | Remove the confirmation path in installed journals (A459). Until then, exclude leader promotion from the recovery closure premise. |
| A469 | Production table slugs can carry collision suffixes, so log records map to object keys only through catalogs. | Derive every key from the base or an adopted catalog's entries, and refuse a table with no slug. |
