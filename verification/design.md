# Logkeeper endgame · Design under verification

The [requirements](requirements.md) define the claim.
The [amendment ledger](amendments.md) governs this design.
Each study has its own statement of evidence and assumptions.
This document specifies the design under study for a regional deployment with one-AZ durability.

## What the service owns

A stream incarnation has one ordered committed history, a writer epoch, a retention floor, replay grants, and terminal state.
Its current replica group owns the authoritative transitions.
Many streams share one group and many groups share a regional service.
A group commits its payload and the ordering decision together under its own quorum.
RTDB owns SQL resolution, application, and checkpoints.
It publishes evidence of a reconstructable cut and asks Logkeeper to trim.
Directory routes locate an authority.
They confer no write, retirement, or read-barrier authority.

The reference layout is three durable voters per group across three AZs.
The ordering protocol is a linearizable replicated state machine at this level.
A group counts verified durable identities. Addresses can be reassigned, but persistence evidence follows the durable identity.
Order membership authorization, durably fence the preceding scope, and install one exact recoverable cut for the successor voters.
Joint voting requires both majorities. Keep the old retained data protected until adoption of the verified successor cut.
The reference transition uses dual-majority joint reads.
A majority from the successor side can serve a joint read with the existing successor-side finalization fence.
Allowing a majority from either side requires finalization to durably fence a majority on both sides.
The authoritative membership decision still follows the joint write quorum.
The selected recovery image can be restaged or replaced before its authoritative successor installation.
A control-plane snapshot must retain exact replay data or independently durable references to it.
See [A34–A37](amendments.md#study-12--2026-11-22).
The journal proof refines the logical kernel under these vote and storage obligations.
Fixed-group prefix agreement has a separate protocol model.
The implementation must refine the group protocol and storage contracts.
The finite comparison also admits a durable immutable payload followed by ordered metadata publication.
Latency between these alternatives remains a qualification question.

## Baseline decisions

A regional service adds journal groups and capacity pools as demand grows.
A deployment's writer can move among eligible RTDB workers while its current journal placement and funded windows stay fixed.
Each journal group has its own voter, recovery, and admission limits.
Replace physical voters under the same logical group when changing replica placement can meet capacity or failure-domain needs.
Moving an incarnation to a different independently ordering group is a separate operation for changes that require a new authority.
Existing funded traffic, eligible writer replacement, and proof-bearing checkpoint publication depend on the installed group and their exact data paths.
Keep any regional decision service outside those paths.
See [A303–A305](amendments.md#architecture-reopening--2026-11-23) and the [architecture comparison](architecture-reopening/comparison.md).

### Put authoritative decisions in the journal

The current journal group owns the deployment's writer grant, lifecycle fence, and certified checkpoint publication.
It orders changes to effective worker eligibility before those changes can authorize or exclude a new writer.
A worker eligibility change takes effect at its ordered group cut.
An administrative request still waiting for that cut is pending.
The group validates a nomination against the candidate's exact enrollment at the grant's ordered position.
Enrollment binds the deployment lineage, engine and isolation constraints, and the admitted worker identity.
A bounded roster uses one durable issuance watermark and keeps only current worker rows.
Re-enrollment of the same identity uses a fresh serial.
Withdrawal names the original enrollment and consumes no new serial.
Withdrawing an installed holder removes its eligibility and fences its grant at the same position.
The fenced vacancy retains the epoch and placement anchor, paid windows, history and custody.
The journal can fill it with a higher eligible grant or close it with an authenticated administrative retirement.
Encode the live roster and watermark together as a canonical bounded section in the authenticated control image.
The committed transfer seal retains the same section alongside its realized storage and funding record.
The target's durable import evidence covers that exact seal body.
Activation installs the decoded roster and its funded target window together.
The predecessor's roster remains frozen after sealing.
Charge a roster section for each retained seal slot and for the current control image, under both selectable checkpoint budgets.
The width and caps are part of the current stream format.
See [A309–A311](amendments.md#study-78--2026-11-23).
See [A306–A308](amendments.md#study-77--2026-11-23).
A gateway that knows a usable group route can obtain the current certified writer binding directly from that group.
Authenticate the route for the exact lineage and installed placement.
The original request can reconcile against the retained result after the new grant.
The lookup compares the original binding even when a staged payload claims the same log position.
The directory publishes discovery hints and places new deployments.
Directory recovery can repair hints from the original ordered decisions.

RTDB Multi's current target contract makes `Claim` an epoch-conditional directory operation and creates a fresh loglet.
The integration must replace that path for same-placement replacement and publish checkpoint decisions through the installed journal.
Cross-group transfer carries the exact final source seal and target installation.
A cold client still needs a route to an enrolled authority.
A group still needs a reachable quorum and an eligible candidate.
See [A299–A302](amendments.md#study-76--2026-11-23).

### Make recovery and watch history separate contracts

The journal owes a bounded reconstructable suffix and exact reconciliation for retained appends.
An expired or truncated watch cursor returns the retained floor and can reopen from a certified state snapshot.
A separate exact event history service belongs to a configured product tier with its own event projection, retention horizon, and custody.
When a stream promises gap-free exact history from that service, trim waits for its durable event coverage.
A stalled required checkpoint, pinned suffix, or required event archive can exhaust its own admission budget.
Existing funded control work keeps reserved room for checkpoint publication, trim, and verified settlement.

### Define retirement and erasure by separate evidence

A terminal receipt orders closure against new invocations.
An overlapping invocation may complete from an earlier certified live cut under its protected borrow.
A physical erasure receipt waits for every original extent to have verified stable disposition.
An inaccessible custody holder keeps erasure pending and its original debit charged.
Shared versions stay in the continuing referrer's verified custody.
A product that requires a stricter retirement deadline needs a separate contract for effective revocation at every admission and effect path.

### Spend the failure allowance once per protected interval

Healthy admission establishes coverage for any one AZ loss.
Select the eligible serving cut independently of physical diagnosis.
During one confirmed outage, fresh work can proceed within the spent interval on the surviving eligible quorum and exact dependencies.
An unclassified outage leaves the full one-AZ acknowledgment condition in force.
These commits are inside the existing failure interval.
Fresh admission is reconsidered if another fault affects that interval.
Full healthy coverage has to be reverified before a new one-AZ allowance begins.
A larger fault envelope requires its own configured durability and quorum design.

### Bound background debt and choose the isolation contract

Reserve per-pool repair and control capacity independently of ordinary traffic.
Budget incomplete physical moves, recovered outcome slots, unreturned original custody, and any still-reachable old journal separately from live writer windows.
Admit physical changes only when the original charges and their full destination footprint fit together.
Prepared or committed durable debt remains charged until exact disposition or transfer to paid custody.
Keep a pending remote wait in its original funded row.
Use shared settlement workspace at the original owner only for locally verifiable ready work.
Reserve its actual peak through durable publication and recovery.
An interrupted stage leaves the original charge in place, and a ready exact refund can publish at full ordinary occupancy while another obligation waits.
The owner schedules continuing ready work with a bounded turn through stable slots.
The scheduling position selects a candidate, and the refund still checks the exact physical allocation identity.
See [A388–A391](amendments.md#study-97--2026-11-23).

Make the exact refund recoverable from every selectable checkpoint before reporting it or admitting a dependent charge.
Order both decisions in the original owner's existing ledger.
A checkpoint can cover the refund directly, or a still-selectable predecessor can replay the exact durably discoverable command from its suffix.
The shared-suffix reference keeps that command until all selectable checkpoints and independent pins release it.
Reserve enough concurrent space for retained redo and the alternate checkpoint that can retire it.
A design that reports only after stable whole-image publication can omit the redo overlap and waits for the selector barrier before reusing the credit.
See [A392–A395](amendments.md#study-98--2026-11-23).

Recover the exact ranked pool cut through any installed-owner change, including every chosen charge that reused an earlier refund.
Replay the current owner's chosen continuation before fresh admission.
Use a historical refund receipt only to reconcile its original result.
Permit physical materialization only from its own exact successful ordered debit in the current scope.
See [A397–A400](amendments.md#study-100--2026-11-23).

Finite unresolved debt can pause new background work.
Already-funded appends spend their own cursor under the current authority.

The shared service protects exact data and authorization and exposes aggregate contention through admission and latency.
An unconditional reserve belongs to independently protected capacity.
A stronger timing-isolated tier needs separate scheduling and qualification.
A parked deployment keeps bounded durable metadata.

### Keep the storage effect interface narrow

Use immutable exact extent identities with a provider-side admission and fence for any operation that can materialize bytes.
An original custodian binds each effect and charge to that scope through retries, takeover, and settlement.
Qualify one concrete media and effect protocol for the baseline before generalizing the adapter.
A provider whose copy, staging, or deletion path cannot establish the required fence and disposition cannot certify physical reclamation.
The ordered source can retire and recover from existing authorized evidence while such a disposition remains pending.

## Commit and observe

An authoritative append requires the installed holder, writer epoch, and placement generation, the expected next LSN, and durability for the exact payload.
Apply chosen commands in group order and recheck the credential and LSN against the state at that position.
The group log can order a command whose stream outcome is refusal.
Only a successful append advances the stream LSN.
Use that applied result together with the exact chosen request to authorize a positive receipt.
A cached result is scoped to the original chosen position and its exact request.
A higher writer grant becomes effective when the group durably installs it and returns the entire committed cut.
An unknown result with a retained request can be reconciled against committed history.
See [A01–A07](amendments.md#study-01--2026-11-22).

### Reconcile the exact retained append

Store the original logical request binding, chosen position, and successful range alongside the retained record.
The binding includes the original lineage, writer grant, expected LSN, and canonical payload identity.
Physical relocation and fresh delivery credentials leave that original binding intact.
Retain the exact row through every selectable checkpoint and suffix while its LSN remains retained.
A certified checkpoint can name the same charged immutable receipt bytes or an authenticated equivalent representation.

Reconcile under current read authority at the certified cut.
Return the original result only for the complete matching binding and retained range.
An occupied range with a different request conflicts.
An authenticated lookup below retention returns the floor, and a future uncommitted position remains unresolved.
This operation leaves the append and window cursors unchanged.
See [A269–A272](amendments.md#study-69--2026-11-23).

### Replace the writer in the same placement

Order a replacement against the exact current writer using an authenticated eligible nomination.
The ordered grant advances its epoch, names the successor, and identifies the exact committed data cut and its command position.
An append earlier in the order appears in the cut.
Later commands from the old grant are refused.
The predecessor worker can be unavailable.
The candidate acquires its existing journal recovery inputs and catches up to that cut before serving transactions.

Keep placement, paid window identities, byte cursors, history, and outstanding custody in the installed group.
The successor can spend the original window subject to its remaining range, recovery headroom, configured quorum, and exact staged-write evidence.
An authorized replacement can pass a pending physical plan while the source still serves.
A chosen physical seal requires its own exact activation and cannot be bypassed by a local writer replacement.
See [A299–A302](amendments.md#study-76--2026-11-23).

### Spend prepaid journal windows locally

Charge each exact journal allocation against current occupancy in its physical pool before granting it to a stream placement.
The grant binds the stream, placement, non-reused allocation, and usable footprint.
Install it in the stream's ordered state.
Each append uses the current window's next LSN and byte cursor and an exact frame attachment under the durability contract.
An accepted command advances both cursors and consumes a positive fitting range.
A refused command advances only its ordered decision position.

The append spends owned capacity and can proceed when the pool has no unallocated space.
When the active window runs out, install a new funded window before admitting an append that cannot fit.
Preserve the live and obsolete windows and their exact dependencies through validated ranked recovery.
Apply historical requests using the certified window basis and original attached evidence.
An old grant cannot restore a pruned window below its issued watermark.

When trim or retirement releases the source's hold, retain the debit while either recovery path, provider work, or any independent reader still needs the allocation.
Return it after the provider certifies exact physical disposition.
Account separately for preparation, physical copies, and outstanding unchosen writes before they can materialize.
See [A239–A243](amendments.md#study-62--2026-11-23).

### Isolate candidate bytes until choice

The logical append offset identifies where a successful command belongs.
Stage competing candidates in distinct scoped physical allocations funded before any write can materialize.
A prepaid workspace can supply those allocations locally under its existing debit.
Share existing immutable bytes only through their exact charged versions.
Check the current physical generation at the effect boundary so a delayed write cannot mutate a reused address.
Persist the exact bytes and the recovery locator before durably installing the accepted rank and physical binding together.
The durable binding can name the staged bytes directly.
Use the ranked quorum to choose the command, then apply it to the stream and its funded window.

Keep the old accepted binding recoverable through the replacement decision.
Count each independently pinned older version and each staged candidate at its actual pool.
When space is tight, a replacement can proceed only when its new physical footprint fits alongside every version that recovery or another holder can still reach.
The budget counts distinct physical versions, allowing immutable ranges held by more than one cut to share an allocation.
Confirm every original hold and provider effect has closed before returning its debit.
See [A244–A248](amendments.md#study-63--2026-11-23).

### Recover the chosen window basis and suffix

Order window installation and pruning with stream decisions.
The checkpoint's ordered cut identifies its source state and window book, including the exact cursor and issuance watermark.
A window change can advance the ordered cut at the same data LSN.
Authenticate the selected control and data bodies and their complete dependency manifest together.
Keep each selectable body's own window state and its suffix readable until the selector is durable.

Resolve the exact voted frame at each chosen position, validate its lineage and ordinal, and replay through the installed cutoff.
The frame supplies the original append request and its exact evidence.
An intact later frame waits for its own chosen position.
See [A249–A252](amendments.md#study-64--2026-11-23).

### Observe an applied cut

A fresh barrier returns an exact committed cut within its invocation interval.
An explicitly latest observation can use an invocation-bound quorum index through the ordered frontier and acquire exact local custody from a validated standing window.
The local admission compares the installed scope, applied cut, gate and process session in the same acquisition.
Retrying latest as a new invocation gives it a new freshness interval.
An explicit named basis stays exact throughout its own retention and authorization.
An exact recoverable operation uses an original identity known before its decision and retains the original authorized result across a lost reply.
The next-nonce rule belongs to that protected exact path.
A read transaction with an existing pinned basis continues at that basis.
See [A364–A367](amendments.md#study-92--2026-11-23).
The ordered path for an exact recoverable capture chooses one marker for its invocation and uses the cut at its applied position.
Issue a positive result only from the exact chosen marker's successful ordered application.
The journal authenticates a canonical, fixed-width receipt covering the lineage, exact writer grant, invocation identity, ordered position and applied cut.
The receiver validates the exact bytes under the receipt's journal scope.
Allow an already-issued receipt to verify locally while its verification material and protected cut remain available.
A chosen marker that refuses at application produces no positive receipt.
For a latest snapshot, record the exact marker result with its protected admission before releasing a positive receipt.
The retained result lets the current issuer recreate the same logical response without the original marker frame or the old issuer.
Recover by the authenticated original invocation so a lost reply may also have lost the permit.
Authorize reissue as a control frame in the existing installed journal.
At that position verify the live original row, its exact permit serial and captured basis, and an authenticated paid delivery proof.
A close that wins first excludes later authorization for that read.
The physical proof binds the original operation and basis independently of the frame's position.
Reframe an overtaken operation against the next eligible position while that exact row and backing stay live.
Order reissue without consuming a new invocation nonce or result slot.
The retired current journal can return an earlier result under its existing paid backing.
Complete an authorized result using its own still-held physical borrow.
See [A342–A345](amendments.md#study-87--2026-11-23).
Record each successful authorization in an independently funded finite delivery book in that same ordered decision.
Bind the authenticated paid proof to its non-reused delivery key and original physical borrow independently of frame position.
Refuse a stale or occupied key.
Keep the delivery row after logical read closure.
Every selectable named checkpoint carries its exact delivery book, issuance floor, and independent physical dependencies.
After every selectable path covers the exact record, retire the old frame once replay and borrowers have released it.
Recreate the original canonical response from the authenticated retained row and its exact still-held physical borrow.
Clear the row only on exact completion or effective stop from the original custodian and keep the issuance floor.
An overtaken frame can be rebuilt using its paid proof while its delivery key and original read remain eligible.
See [A346–A350](amendments.md#study-88--2026-11-23).

Split capture can retain the exact selected basis while preparing first delivery.
A candidate fused open can choose capture and its first delivery together if an original provider has delegated prepaid coverage for the exact view selected at application.
A ticket fixed to an earlier candidate can be overtaken on each retry.
Under delegation, the journal orders assignment against unused fencing at the exact non-reused credit key.
The original provider keeps the physical charge until it can verify and apply the corresponding disposition.
A current authority can fence unused credit after writer replacement.
A successful open preserves the normal independent delivery lifetime, and a refusal leaves both books and the read nonce unchanged.
Use split capture until delegated window coverage and its costs are established.
See [A368–A372](amendments.md#study-93--2026-11-23).

An optional standing grant prepays its exact physical allocation and reserves a disjoint serial range at the original provider.
Preparation leaves the lineage's delivery sequence untouched.
The group assigns the next delivery serial and issues the exact physical serial from the installed grant at the same choice.
At window replacement, persist the new generation and freeze the old window's exact outstanding assignments at that ordered cut.
The new window spends its own prepaid allowance.
The original provider retains its debit until verified settlement, including an earlier assignment whose response it missed.
An older generation cannot reopen behind the current watermark.
Ordinary writes and checkpoint publication use their own admission.
When fusion has no coverage, the separately funded split program can still proceed.
See [A373–A377](amendments.md#study-94--2026-11-23).

Authenticate the current window proof name, spent cursor and installed generation in each exact checkpoint.
Retain the exact cursor after completion clears the last live delivery.
Replay all later chosen standing decisions before offering fresh use.
The bounded cursor field must also represent the fully exhausted range.
Use immutable historical evidence for replay and current exact backing for fresh admission.
The source seal authenticates the frozen original grant, cursor and delivery book at one cut.
The target inherits the watermark and starts with no current standing grant.
Original-provider settlement retains its own exact evidence and custody.
See [A378–A382](amendments.md#study-95--2026-11-23).

At the original provider, install the exact frozen book from the chosen seal without resetting local operation state.
A previously chosen original operation can use its still-live original charge and exact frozen row until authenticated terminal settlement.
Require a live exact allocation at every effect, with a matching chosen operation and a compatible frozen row when the window is sealed.
A drained window excludes all further effects.
Return its exact original charge only after stable physical absence under the lower provider fence.
Refund needs no new allocation.
Keep the provider allocator's durable issuance frontier.
After refund, positive live allocation admission rejects delayed work without retaining a permanent enforcement record per window.
Other independently retained receipts follow their own retention rules.
See [A383–A387](amendments.md#study-96--2026-11-23).

A tentative marker without protected admission can be retried under a fresh identity while the deployment remains live.
See [A318–A321](amendments.md#study-81--2026-11-23).
Scope a protected invocation by the exact writer grant and a bounded nonce.
The chosen admission consumes exactly the next nonce and protects its result with the same journal decision.
The current writer can order an authenticated abandonment for an unresolved next nonce without using a result slot.
Process earlier issued nonces by admission or abandonment before admitting a higher nonce.
Carry the floor with the authenticated read book and journal control in every selectable checkpoint.
Closing a result leaves the consumed floor unchanged.
An issuer that loses its issuance state fences its grant and establishes a newer authenticated scope before issuing new invocations.
At exhaustion the current grant refuses fresh nonce consumption.
A live retained result keeps its original scope for reissue across the fence.
See [A330–A333](amendments.md#study-84--2026-11-23).
An independent exact caller can use the bounded selective candidate once its contract permits overtaking.
Advance its floor over resolved nonces only, preserve the exact sparse marks, and normalize the admitted state before applying another window-boundary decision.
Bind the fixed width, floor and bitmap to the same authorized grant and exact checkpoint.
Width one gives the next-only admission policy.
See [A401–A403](amendments.md#study-101--2026-11-23).
Apply selective identity choice and the existing protected capture or authenticated abandonment in one ordered command.
Keep its resolved identity when the result closes, and keep independently charged deliveries until their own exact settlement.
Use the same named checkpoint body for the floor word, packed bitmap, live reads and deliveries.
Replay its exact chosen suffix under either selectable root.
Keep the window when the grant remains the same and begin a fresh one on a verified newer grant.
Fresh use must match the current active grant.
See [A404–A407](amendments.md#study-102--2026-11-23).
Bind the exact width to the lineage and full writer grant in the chosen order.
Keep that width for the grant's lifetime and inherit it on ordinary replacement or transfer.
Choose an authenticated width change only with its exact newer writer grant and check it against the durable format bound.
Use the historical grant and width to open each certified selector before replaying any chosen grant and policy change.
Treat configured width and bitmap size as separate facts.
Retain the verification material needed to apply historical policy changes without contacting a live policy service.
See [A408–A411](amendments.md#study-103--2026-11-23).
Bind the offer's lineage, successor, width and verifier version in one canonical signed body.
Carry the signature inline with its chosen command.
Order a strictly newer bounded verifier under installed administrative authorization.
Check a fresh offer with the exact verifier at its applied position.
Open historical replay with the public descriptor from its authenticated named checkpoint and apply each chosen verifier transition in the suffix.
Retain those exact bytes until every crash-selectable path and independent use has released them.
See [A412–A416](amendments.md#study-104--2026-11-23).
The result stays fixed if later commands apply before reply delivery.
RTDB applies through the captured cut and acquires the checkpoint and replay reservations required to serve it.
Admission accounts for ordered metadata, read markers, and refusals independently of the stream's retained data.
See [A98–A101](amendments.md#study-28--2026-11-22), [A312–A314](amendments.md#study-79--2026-11-23), and [A315–A317](amendments.md#study-80--2026-11-23).

## Read a ready replica group

The read-index candidate issues a fresh quorum round for the exact invocation, group incarnation, placement, voter configuration and ballot.
Open the round on an activated ballot with exact durable quorum coverage of the earlier chosen prefix.
Each eligible voter checks its durable promise and reports its accepted position in that same scope.
The greatest returned position covers the group cut at round opening.

Serve an independently certified, applied snapshot that covers the greatest observed position.
Check read authority at the selected snapshot and establish its exact checkpoint and replay reservations.
The selected snapshot can use the sampled prefix after exact certification, or another certified prefix covering the position.
The quorum bound needs scoped positions.
Using the sampled prefix itself also requires checking its exact identity against certified application.
When the only available evidence is a discarded minority sample, change to a valid basis or retry in the current scope.
A completed round can still supply an earlier exact cut after a successor activates if the invocation retains its authorized basis.

The logical reference uses complete command boundaries inside the invocation interval.
A durable batch is allowed to carry several such boundaries.
If the product contract requires an exact physical batch frontier, the checked alternative matches the round's sampled maximum to a cut already certified before that round opens.
See [A102–A105](amendments.md#study-29--2026-11-22).

Membership publication closes every predecessor read quorum promised by its read policy.
Each reply retains its original authenticated scope and round identity.
A previously valid round can carry its immutable floor across a voter change within the same group, incarnation and placement.
Reserve on the current authorized applied view once its certified group position covers that floor.
Map that position through ordered application to the stream cut and protect the exact root and replay suffix together.
An applied view can lag the group's chosen position.

Take a fresh round when the old floor refers to a discarded speculative tail that the successor cannot cover.
New reservations can use a newer applied root.
An already admitted reservation keeps its exact basis until effective release.
If the reservation is an ordered command at the group head, it supplies its own freshness witness.
The path without a command per read requires independent atomic custody against the certified applied view.
Carry across a placement change still requires refinement of the handoff and physical custody evidence.
See [A106–A109](amendments.md#study-30--2026-11-22).

## Share a physical snapshot reservation

The no-marker candidate registers a serving window for one certified applied view in an authenticated endpoint session.
Register the exact root, its complete immutable dependency graph, and every required physical replay extent before the window can open.
Register the hold with each custodian that can reclaim one of those dependencies.
If any dependency is still being registered, the staged window remains ineligible for reads.
Protect the admitted view through its registered custody independently of later checkpoint publication and logical trim.

In the endpoint's admission decision, compare the window's certified group command position with the invocation's verified floor and check read authorization at that cut.
Validate the exact open window and session in the same decision that adds the local borrow.
Multiple calls can use the same window and each keeps its own invocation evidence.
The window's binding stays fixed as it moves from serving to draining.
An eligible replacement can be prepared under a second capacity charge and installed locally in one switch that seals the previous gate.
Release the old charge only after every physical operation finishes or a fence conclusively stops the exact old session and its I/O.
A restart increments the serving session and preserves old custody until settlement.
Completion captures the result before releasing its physical inputs.

Count staged, open and sealed windows under the same limit.
The slot count bounds control state for this registration protocol.
Charge physical bytes and in-flight operations separately and reserve control progress outside ordinary admission.
At capacity, draining old work can leave a gap before a newer applied view becomes available for reads.
The reference ordered path remains available under its own capacity and quorum premises.
See [A110–A113](amendments.md#study-31--2026-11-22).

## Recover a replica-group ballot

A ballot belongs to one proposer and one certified voter configuration.
It orders group commands and carries the RTDB writer grant as replicated state.
Writer epochs and stream placement generations have their own authority transitions.

Before returning a prepare reply, each voter durably promises to refuse lower ballots and captures its latest complete accepted prefix in the same decision.
Rank by the ballot that accepted that prefix and then by its logical end position, which includes checkpointed positions.
A durable higher promise or a partially copied prefix leaves the accepted rank unchanged.
An eligible proposer adopts the greatest report in a prepare quorum.
Each subsequent proposal in that ballot extends the adopted prefix on one immutable chain.

A write round casts durable votes for exact prefixes.
Incremental transfer is valid when the retained base and ordered suffix reconstruct the same prefix.
A quorum at one ballot certifies the positions common to its exact votes.
Uncertified minority data can be adopted and chosen during recovery.
Learning a delayed certificate preserves every previously known prefix.
See [A94–A97](amendments.md#study-27--2026-11-22).

## Close a voter configuration

Bind the closure to one authorized successor intent.
Each closing voter permanently fences its predecessor scope and returns its exact complete accepted prefix in the same durable decision.
For a stable scope, use an intersecting majority of its voters.
For dual-majority joint writes, a successor majority suffices to recover the write prefix under the corresponding prepare rules.
The read policy still determines which other gates must close.
Keep the successor intent single-valued even if several independently sufficient write fences can form.

Rank the reports by accepted ballot and logical position.
Recover the greatest reported prefix, using the already installed basis when the scope has accepted nothing further.
Recover from the exact durable voter evidence even if the coordinator never learned a completed write.
A previously cast vote can still combine with a delayed vote from an unfenced voter.
Every such old quorum proves a prefix of the recovered image.
After activation, reconcile its receipt against the inherited ordered result, while all extensions go through the successor.
Requiring every old vote to cease before closure needs a stronger fence and can block during a one-AZ outage.

The durable scope fence ends predecessor authority.
It permits another ranked recovery attempt for the same successor before an activation has been chosen.
If a longer unchosen tail loses its only accessible source, take another exact cut from the surviving fenced quorum.
Stage immutable copies under their exact attempt identity.
Choose one installation under the successor authority after its own write quorum verifies identical recoverable contents.
Retry through that same ordered installation decision after a lost reply.
Once an installation is chosen, every retry must inherit its cut.
Settle abandoned staging through its original custody records.
See [A115–A120](amendments.md#study-32--2026-11-22).

Bind each selectable named checkpoint to its exact certified historical prefix and applied state.
Read its named immutable contents, verify its dependencies, and replay the complete exact suffix of the ranked cut.
Stage the reconstructed image before ordering its successor installation.
The successor installation slot chooses the exact prefix and image after its voting replicas verify durable backing.
Verify the exact lineage, successor revision, and ordered cutoff with the live successor recovery quorum.
Reconcile a delayed install acknowledgment against the chosen installation result.
See [A334–A337](amendments.md#study-85--2026-11-23).

Capture the local publication session before dispatching recovery.
Attach the applied image by comparing its lineage, revision, exact local ordered frontier and session while filling the empty serving slot in one serialized transition.
After a process restart, reopen the exact certified prefix of the existing installation under the new local session.
Advance a live image and its applied frontier together by applying the exact chosen suffix of its own journal scope.
A materialized local view can lag choices that have yet to arrive.
Fresh use takes its own current ordered authorization for the matching applied view.
Recovery-time quorum evidence stays historical when reachability changes.
An admitted exact reply uses its own still-held physical borrow until completion or effective stop.
See [A338–A341](amendments.md#study-86--2026-11-23).

## Order activation in an existing target

Allocate the exact incoming reservation in the target's serving journal and stage candidate images outside the command order.
Durably register a candidate's validated readiness before choosing its activation.
The ordered activation decision checks the current reservation, exact live grant and logical revision at its position.
Discarding a grant fences its exact attempt against delayed reuse.
Reconcile ambiguous results at the original ordered command position or with its retained outcome.

When target voters change, recover their ranked accepted command prefix and its live dependencies.
The recovered prefix can contain an activation the learner has yet to apply or report.
Historical commands replay under their ordered revisions.
A delayed packet proposed at a newer position must satisfy the newer conditions.
Before the new physical family serves, verify its own exact coverage for the recovered installed view.
An unselected grant from an earlier revision can remain a charged cleanup obligation.
Obtain current exact readiness before using its image for a new activation command.

An incoming reservation awaiting data can remain pending during target voter repair if the recovered journal has no command depending on its absent image.
See [A126–A130](amendments.md#study-34--2026-11-22).

Issue monotonically increasing attempt serials within the intent from the target's ordered journal.
Advance its cutoff through exact ready or spent attempts and compact the individual spent rows behind it.
Read an absent row behind that cutoff as spent.
Keep exact live bindings and the independent cleanup obligations through voter replacement.
The installed cutoff releases issuance credit.
Physical staging and cleanup consume their own budget until authorized settlement.
See [A131–A134](amendments.md#study-35--2026-11-22).

## Close an incoming activation intent

Bind every incoming command to the original authority incarnation and its exact non-reused admission handle.
Keep the target's durable issuance fence through voter replacement.
Remove the admission row and its attempt fences after the target orders either the source's exact abort or its own exact installed activation.
An unresolved sealed move retains its admission.

Installation atomically leaves an exact result and the live serving binding.
The target keeps that result durably retrievable through admission closure, onward movement, and voter replacement.
The source records the exact result before acknowledging it.
The acknowledgment releases result capacity at the target.
Reserve that capacity before authorizing the source seal so a ready sealed move already has space for the result it owes.
When retained results exhaust their budget, withhold new authority to seal until capacity returns.

Record and charge physical copy plans before dispatch.
Closing the admission row leaves those plans and any serving custody intact.
Settle a releasable plan at its original custodian and fence its exact key, even if the provider sees no bytes yet.
After that fence, a delayed copy for the old key is refused.
The target can close the admission row while the provider or source receipt path is inaccessible.
Fresh admission and staging still need the corresponding capacity.
See [A135–A139](amendments.md#study-36--2026-11-23).

## Move an activation home

Name the authority for incoming activation by a stable logical home.
Mint each admission handle within that home and retain its exact scope across physical ownership changes.
Use one monotone directory binding per home to find its published owner.
Current cached routing can serve while the locator is unreachable.
A request to a stale or stopped endpoint retries discovery.
It can report an unresolved transport failure without claiming that the activation result is absent.
Certification of the ordered operation supplies authority.

Seal the previous owner and stage the exact unresolved book, including original result bindings, physical keys, outstanding charges, and issuance fences.
The sealed predecessor accepts no further book changes.
Already dispatched physical effects and durable records at the source can still settle under their original keys.
Reserve successor capacity for the cut and its staging before sealing.
The successor durably installs the exact image before its revision can publish.
Old publications cannot replace a higher published revision.
Wait for independently recoverable publication before planned shutdown of any covered predecessor and before beginning the next move of that home.
Direct shutdown at the exact retired owner revision because network addresses can be reused.
The former physical owner keeps no forwarding role after shutdown.

The original custodian still owns the physical effect.
If a former coordinator also owns storage, retire that custody only through its own handoff or exact settlement protocol.
Reconciliation through the new owner can complete once the counterpart and locator are reachable and an exchange can finish before another fence.
An unbounded sequence of fenced relocations can overtake every fresh lookup.
The protocol's progress envelope includes an eventually stable owner interval or a delivery rule that assures an authorized exchange.
See [A140–A144](amendments.md#study-37--2026-11-23).

The target cut owns the admission fence, chosen activation evidence, retained results, serving bindings, and copy plans.
The source journal owns durable result intake.
The original custodian owns the physical fence.
A source can record a previously certified reply and a custodian can complete an authorized fence while the target is sealed.
Installation restores the exact target fields and leaves those external decisions in their owning authorities.

Discharging a retained result or copy plan orders a fresh command under the current open target revision.
It checks the durable source record or custodian fence for the original exact binding.
A delayed request can carry valid evidence with an obsolete address.
Refresh discovery and retry that evidence under the current revision.
If the source already has the exact record, repeated result delivery has the same effect as a single delivery.
The duplicate cannot reopen the target's retained result after acknowledgment.
See [A145–A147](amendments.md#study-38--2026-11-23).

Order each acknowledgment or cleanup with its exact validated evidence when eligible.
Record the original input at its ordered position, including when eligible evidence was absent.
Ranked closure recovers chosen commands that the learner never applied.
Replay reproduces their outcomes from the certified basis and historical inputs.
An earlier refusal stays refused if evidence arrives later.
A fresh command can submit that evidence under the current authority.
Replaying an already chosen command requires no fresh lookup from the source or custodian.

Validate the physical receipt against the original registration key and immutable binding.
At that custodian, durably refuse new or delayed acquisition before reporting settlement.
An empty slot with a queued acquire still needs the refusal fence.
Release the target's charge after verifying exact absence and closure of outstanding I/O, or after the original custodian takes durable responsibility for all remaining bytes and effects.
The latter leaves the custodian's charge in place.
Physical erasure completes only with exact absence evidence from each required location.
See [A148–A151](amendments.md#study-39--2026-11-23).

## Close provider writes before certifying erasure

Record the exact version and one-use write ticket before dispatch, while its physical footprint remains charged.
At the provider's materialization boundary, check the exact ticket and version fence.
Serialize durable ticket consumption with the effect so a repeated delivery of a completed ticket cannot create bytes again.
Recover both the effect fence and ticket decision after restart.

Close issuance before observing I/O closure.
For an authorized retiring version, install and verify an exact provider fence that excludes every previously issued ticket at the effect boundary, or verify durable terminal completion of each exact issued ticket.
A producer-side close, timeout, or completion from a sibling ticket leaves the original ticket unresolved.
An effect fence permits progress when an admitted upload never completes.
Then establish exact physical absence under the closure proof.

When the provider is unavailable, the original custodian can take durable responsibility for the complete remaining footprint and issued tickets under its independent capacity budget.
Release the target charge after verifying that exact custody commitment.
The receiving custodian holds its charge until stable absence.
If custody has no room and the provider cannot settle, the target continues to hold its charge.
The custody receipt can arrive after subsequent erasure because its authority then has the stable absence proof.
See [A152–A156](amendments.md#study-40--2026-11-23).

### A guarded physical slot

A provider with durable atomic replacement can keep one small preprovisioned guard per slot.
Arm the guard for the next separately funded allocation with a non-reused generation.
Check and consume its exact live permission in the same durable update that installs the current payload.
An authorized fence invalidates that permission at the same boundary.
Clearing the payload leaves the vacant guard and issuance watermark recoverable.
The next allocation receives a fresh generation.

Track every staged write and retained version under its exact original physical scope.
An old upload can still consume storage after the current slot is cleared.
Charge each affected location until its own authenticated closure and stable absence.
A logical name may move to a separately charged new allocation while old physical bytes await disposition.
Reclaiming the old allocation requires its complete original proof.

The adapter verifies that every materialization path enforces the same exact conditional update.
Guard creation and destruction of the entire storage namespace need their own durable admission and closure authority.
See [A223–A226](amendments.md#study-58--2026-11-23).

### Close the namespace that can create guards

Keep a durable provider root outside the namespaces it manages.
Reserve a bounded guard plan for a fresh exact namespace under that root before provisioning.
The provider creates each guard only when the root's current scope and provisioning phase authorize that exact planned address.
Publish the complete plan for service.

Seal the root scope against new guards and new child grants before draining a nonempty namespace.
Keep the original charges while an earlier grant can still take effect.
Use the exact child fence and disposition for each materialized guard.
Verify complete auxiliary closure for the original scope.

At an authoritative empty cut, the same durable transition can exclude provisioning and record terminal retirement.
Return pool credit against that exact terminal result and cleared original accounting.
The root preserves the scope watermark through its own recovery.
Fresh admission uses a new scope, and closed scope evidence remains bound to its original namespace.
See [A227–A230](amendments.md#study-59--2026-11-23).

### Recover the provider root before enabling effects

Order root creation, sealing and retirement in the provider's durable history.
Confirm a retirement from its exact chosen and applied result after both its record bytes and recovery address are durable.
A previously durable locator can satisfy the recovery address check.

Open either selected base against its exact root state and recover the chosen ordered suffix.
Check the authorized prefix against decoded frames and apply exactly that prefix.
Resume provisioning only after applying the recovered cut.
Queued creates use the current recovered generation guard.
Keep external custody effects separately accounted and resolve them by their original scope.
See [A231–A234](amendments.md#study-60--2026-11-23).

Keep only exact live provider write tickets and a durable issuance watermark in the admission book.
Allocate the next serial and register its live binding in one durable provider decision.
Materialization consumes the live ticket with the effect.
Validate the binding and immutable physical namespace on every delivery.
A capability identifies the requested write and a live row authorizes it.

From an authenticated recovered book, an issued serial with no live row is permanently closed.
This recovers closure after losing the original receipt.
An unseen future serial can still be issued.
Closure supplies no historical payload or complete response, which needs its own retained evidence if required.
Charge actual outstanding bytes and physical obligations independently of admission row count.

With closed issuance, an empty live book proves provider write closure.
A certified effect fence can establish the same closure while old live rows remain.
After stable physical absence, reclaim the retired namespace's book and keep the address's non-reused generation watermark.
Opening a new namespace at the address grants authority only to its fresh scope.
See [A157–A160](amendments.md#study-41--2026-11-23).

## Reserve recovery before sealing

Apply a durable footprint envelope to the installed recovery basis and every eligible new source vote.
Size the envelope for the exact recoverable command cut and its physical dependencies.
The learner can lag an accepted cut that ranked closure must recover.
Before sealing the source, reserve residency for the envelope at the destination and workspace for the peak coexistence of incumbent and replacement images.
Two full envelope-sized reservations suffice for that workspace when the two images use disjoint physical copies.
Other ordinary admissions can consume only their unreserved capacity.

Hold the incumbent's exact media while the replacement stages.
Install only the recovered cut under its authorized target quorum.
Promote that same staged image against its existing residency credit.
The switch preserves earlier chosen outcomes and needs no new ordinary allocation.
Retain the old physical charge until its custodian proves exact disposition.
An outage at that custodian can postpone returning its workspace while the already funded installation finishes.
Account for those outstanding charges when admitting any later move.
See [A161–A165](amendments.md#study-42--2026-11-23).

## Reserve capacity across failure domains

Describe each move's peak footprint as a vector over the physical resource pools it needs.
Account for ordinary usage, prepared holds, committed move capacity, and retained copies at each pool.
When residency and workspace use the same physical pool, include their combined peak in that pool's debit.
Refuse admission if any component exceeds its limit.

Prepare the complete vector for the exact move before asking the source to seal.
The source's ordered seal commits the vector and closes the old writer authority in the same decision.
Use an atomic pool operation when one authority owns the complete pointwise debit.
With separate pool authorities, acquire holds in one strict order over the pools, and keep the exact terminal decision recoverable from the move's authority.
A separate vector coordinator is an alternative for future physical move admission given enforceable spending rights at every affected pool.
Exact target installation has to preserve the evidence needed to activate without that coordinator or the source route.
The order excludes cycles among those holds.
Progress also needs recovery of the decision authority and either eligible capacity or a reachable path to exact pre-seal abort.
Each affected pool must reconcile the abort and fence that move before returning the hold.
Install the same fence at a pool with no current hold to exclude a delayed prepare for the canceled move.
Once the decision binds the vector to sealing, keep the capacity committed through restart, coordinator replacement, and timeouts.
The ordinary capacity check counts each prepared hold as soon as its pool grants it.
Binding a complete held vector to the seal reclassifies those credits with no change to available capacity.

At installation, reclassify the reserved capacity into resident and obsolete charges in their actual pools.
Return the obsolete charge only against disposition for its exact physical scope.
Each pool can apply its own verified disposition.
An overlapping move or a matching route supplies no authority to spend or release that capacity.
See [A166–A170](amendments.md#study-43--2026-11-23) and [A171](amendments.md#study-44--2026-11-23).

### Install the move's exact prepaid window

Plan each destination allocation by exact stream, move, custody key, original pool incarnation, role, and required footprint.
Prepare it in the same local ledger used for ordinary traffic and old physical custody.
At the first successful preparation, mint the physical identity from the original pool's local durable sequence and charge the exact footprint in that same decision.
A retry of the live grant uses the original identity.
The complete vector resolves each distinct planned scope to the exact physical allocation in its authenticated receipt.
Bind that realized vector and the selected recovery cut in the ordered seal and its resulting activation evidence.
The same byte total cannot stand in for a different allocation or move.

Order the exact logical plan under the source move key before the pools prepare it.
Use the original receipts at the seal and retain their realized vector in the ordered record, or an equivalent certified checkpoint.
The successor checks the original sealed vector along with the cutoff and durable installation.
Name a serving window by its source lineage and ordered activation position.
Bind that logical window to its exact pool-issued physical extent.
A move can install a newer source window whose physical serial is lower than the predecessor's.
Recovery cleanup requires the installed move's exact anchor, recovery role, original physical scope and stable disposition.
The append window remains charged under its own lifecycle.
See [A285–A289](amendments.md#study-73--2026-11-23).

The source's canonical control body stores the original realized vector under the exact move slot, serial, lineage, and seal position.
Check the body size against the admitted extent and byte budget before parsing its fields.
Certify the complete control body and its evidence dependencies at the exact checkpoint cutoff.
Reclaim the original frame once both selectors release its replay dependencies and every remaining claim has exact retained evidence.

Keep one acknowledgment for the target and one for each original pool.
A pool acknowledges a committed move after verifying closure and stable absence or durable charged custody for every original recovery scope it owns.
The acknowledgment names the original realized seal.
The source compacts that move row once all participants acknowledge and no live handoff still needs its realized vector.
Its current append window keeps its own lineage, activation position, exact extent, and paid custody in the serving window book.
See [A290–A294](amendments.md#study-74--2026-11-23).

Rank the whole source frame, including every original attachment and realized physical binding.
A selectable checkpoint authenticates the exact augmented image at its ordered prefix.
Replay that image using only the complete chosen suffix and its original evidence.
Keep a live handoff's vector until the source applies the exact activation, including when target installation and all custody acknowledgments have already arrived.
See [A295–A298](amendments.md#study-75--2026-11-23).

Publish the destination window from its already charged allocation as part of applying the certified activation.
Pointwise occupancy stays unchanged at installation.
Give the new append cursor its own exact physical range outside the extents holding the recovered image.
Packed storage can represent those roles with independently identified disjoint ranges.
Retain each original physical charge through every pending predecessor and staging obligation.
Settle it using exact original disposition under the provider fence.
See [A253–A257](amendments.md#study-65--2026-11-23).

The preparation receipt remains backed while the source can still order the seal, including when the coordinator is lost or replaced.
A replacement uses the original receipt for the same reservation.
Neither elapsed time nor a lost reply changes the debit.
After an authenticated source abort, fence the exact scope at every planned pool before returning its capacity.
A delayed request reaching a pool before its fence can still acquire a charged hold.
The ordered abort bars its use for a seal, and reconciliation settles the hold at that pool.
Recovery preserves the effective fence and remaining debits in that original custody authority.
See [A273–A276](amendments.md#study-70--2026-11-23).

A pool charges the extent and publishes the exact prepare grant in one durable local decision.
Exact retries use that grant without acquiring another extent.
The source's ordered cancel or retirement supplies the exact terminal result for every original participant.
Applying it closes the pool's preparation and new provider ticket admission for that scope.
Keep already-issued work in its original charged custody and verify stable physical absence before returning the debit.
The source can compact its result once the original pool certifies closure and absence or accepts responsibility under that retained charge.
The custodian can compact the spent marker behind its own installed floor without changing any physical charge.
See [A277–A281](amendments.md#study-71--2026-11-23).

### Replay activation within its authority

The ordered activation frame carries both the certified exact installation and the original funding evidence for its designated window.
Apply both effects at that position, or refuse the frame while keeping the prior writer and window.
Every selectable source checkpoint replays the same historical evidence through its installed cut.

Recover physical charges, original borrows, and settled claims from their own custody authority.
Join the recovered source with the current custody book and replace only that stream's window rows and cursor.
An authenticated applied installation can authorize settlement for its still-live original claim.
A receipt arriving after the claim closes leaves closure in force.
Verify the recovered current window and all required dependencies against current eligible custody before exposing fresh service.
See [A258–A262](amendments.md#study-66--2026-11-23).

## Move a capacity pool's authority

Bind every reservation key to the immutable physical pool and a non-reused channel and serial.
Resolve retries by the exact key and binding.
The current owner orders every new admission and verifies the move authority's exact decision before converting or canceling a hold.
A change of owner keeps the same physical pool, reservation keys, and already minted physical identities.
Recover the allocator watermark, admission gate, physical charges, and outstanding provider custody at the same ranked installed cut before enabling fresh admission.
A new physical incarnation changes the namespace before restarting its local sequence.
See [A282–A284](amendments.md#study-72--2026-11-23).

Use the channel's installed floor to refuse an absent old key after compacting individual cancellation records.
Keep live debits and any unsettled physical obligations when advancing that floor.
Base the issuer's next credit on an acknowledgment of durable floor installation.
An offered floor supplies no credit.
Retain exact keys and their charges independently of admission metadata when retiring a channel.

Fence the predecessor and install its exact closed cut, including ordinary occupancy, every live debit, the resource limit, and the channel issuance and refusal state.
An earlier staged copy can miss an acquisition or closure ordered before the cut.
The installed successor can reconcile an already chosen move decision independently of the old owner's availability.
Reject new operations at stale owners and resolve the original scoped request at the current owner.

Order a planned reduction of a pool's limit only if the full charged occupancy fits the lower limit.
Apply that admission limit before removing the capacity.
Raise the limit only when the added capacity is verified usable.
Loss of an AZ is a failure that can remove eligible resources and delay new admissions.
Moving bytes to a different physical pool needs separately funded destination custody and exact disposition of the old bytes.
See [A172–A175](amendments.md#study-45--2026-11-23).

## Decide the funded seal at the source

Each move has one exact intent that names its source placement, target, and complete resource vector.
The source can order a seal only for its outstanding intent and only with exact durable receipts for every required pool.
Those receipts stay backed until the source orders an exact abort, so the seal can validate them while a pool controller is changing.
The seal reclassifies the existing debits and requires no new pool allocation.

Order seal, abort, and retirement in the source's current authority.
When retirement wins before seal, the same durable decision closes stream admission and records abort for the outstanding intent.
Return the terminal retirement result without waiting for the pool owners.
Each pool applies the exact abort when reachable and closes its local key, including keys with no current hold.

When seal wins, the target has the sole right to install the successor and inherits the associated capacity.
An outstanding retirement request goes to the installed successor for its own terminal decision.
The predecessor supplies no further retirement authority after its seal.
Keep physical charges until exact disposition under the existing custody rules.

A move coordinator can prepare or verify receipts before that ordered decision.
A receipt or coordinator preflight supplies provisional capacity and no independent irreversible commitment.
See [A176–A179](amendments.md#study-46--2026-11-23).

## Compact settled source decisions

Reserve a source result row when issuing an exact move identity and record its participants before any prepare can take effect.
Record the exact seal or abort in that row.
At full width, use the reserved rows to decide and reconcile existing work.
Defer fresh move admission when all result rows remain charged.

Keep the exact result while any participant still needs it.
For an abort, a pool acknowledges only after its exact key is durably closed and any remaining physical work has independent accounted custody.
For a seal, each pool acknowledges after it durably owns the continuing charge and associated obligation.
The target acknowledges the exact abort closure or installed result as appropriate.
Order each acknowledgment against its full binding, result, and participant.
An offered acknowledgment or a missing response leaves the debt outstanding.
If another consumer is owed an exact result, record its obligation under a result budget until it acknowledges or its explicit retention contract ends.

Reclaim each row once its own consumers have durably settled.
An older unresolved row remains charged while a later settled row returns its slot.
Preserve the issuance watermark and never reassign an issued identity.
Read an authenticated issued identity with no live row as closed.
Closure supplies no exact historical result or authority to apply an abort.

Carry the outstanding book under its stable authority and through stream retirement until obligations settle.
Recover from the certified base and ranked closed prefix, including chosen decisions and acknowledgments the learner has yet to apply.
Replay their original authenticated bindings and evidence without consulting the participants.
Keep current discovery available while the book still owes exact results.
See [A180–A183](amendments.md#study-47--2026-11-23).

## Settle move evidence against physical work

An ordered abort authorizes local closure for the exact move.
Its provisional capacity stays charged until the pool has closed that key and accounted for its physical work.
Return the charge to ordinary admission when the pool verifies stable absence or proves that no physical work was ever issued for the key.
When bytes or issued writes can remain, reclassify the charge to exact durable custody at the pool where those bytes can reside.
The reclassification preserves the debit for outstanding bytes and possible effects.
A charge in another failure domain supplies no backing for that pool.

The current pool authority can acknowledge the abort after this settled state is durable.
Recovery of that authority preserves the refusal, the charged custody and its pending work until effective physical disposition.
Source compaction can reclaim the result slot while that independent physical work continues.
Provider unavailability can delay erasure and physical credit return without keeping a source result slot after all participants have taken responsibility.

Bind target installation evidence to the exact funded decision and the recovered command cut as well as the installed target scope.
An acknowledgment for that seal requires the verified exact installation.
Committing an acknowledgment at the source changes the result book alone.
Continue charging residents and obsolete physical copies at their owning pools after source compaction.
See [A184–A187](amendments.md#study-48--2026-11-23).

## Replay one source command history

Order funded lifecycle decisions, result records, acknowledgments and compaction in the same source command history.
Publish the stream authority and its reserved result from the same applied command.
A successful seal both fences the writer and commits its result.
A successful retirement records any outstanding pre-seal abort at its own position.
Routine stream commands cannot invoke those transitions directly.

Record each evidence attachment with its request before choosing the command.
An ordered request without eligible evidence retains its refusal even if the participant supplies evidence later.
Process later evidence as a new ordered input.
Replay a chosen acknowledgment using its exact attached decision, participant, and durable settlement evidence.

The seal anchors the exact funded decision at its ordered command position in the certified lineage.
Verify that the install covers that anchor, its exact inherited prefix, and the exact target.
A command that only changes authority or the result book can leave the data LSN unchanged.

Certify one checkpoint of stream authority, the reserved result book and issuance state, pending intents and any live seal anchor at the same ordered position.
Recover the ranked chosen tail against that checkpoint, even if the old learner has yet to apply those commands.
Expose the recovered cut only after applying all its commands to both pieces of state.
This replay uses attached proof material and needs no fresh participant lookup.
See [A188–A191](amendments.md#study-49--2026-11-23).

## Trim a joint checkpoint and its evidence

Separate the compact control image from the logical data history.
The control image binds the stream and ordered position, writer authority, data frontier and certified root, source result book, issuance, pending move, and live seal anchor.
Carry live replay reservations under their own bounded representation.
The data root and its physical dependencies use the checkpoint and custody contract.

Keep each evidence object while a tail from any crash-selectable base needs it, an endpoint still borrows it, or an outstanding claim lacks equivalent durable evidence.
A visible checkpoint alone supplies no authority to reclaim evidence needed by the previously durable selector.
When issuing a substitute from a checkpoint, verify its exact scope, position, decision binding, and named outstanding participant.
Every selectable recovery cut must still permit the corresponding authenticated claim or reach an independently retained evidence object.

A current-cut attestation establishes the exact settled choice recorded in that cut.
It carries its own cut position.
If a recipient is owed an original ordered reply, retain the original command position and required proof material under its result budget.
The current result alone cannot reconstruct where that command originally ran.

Bound the encoded header and each live result row, including its participant and evidence representation.
Reserve for both selectable copies of the control image during publication.
Charge staging, retained tail attachments, borrowed evidence, and physical data dependencies under their existing budgets.
See [A192–A195](amendments.md#study-50--2026-11-23).

## Authenticate the joint checkpoint envelope

Authenticate one canonical checkpoint message with an explicit checkpoint domain and format.
It names the lineage, ordered command position and prefix commitment, data frontier, and exact immutable control, data and evidence components.
Select it against the expected certified cut.
Decode exactly one complete message and require its original authenticated bytes.

Read each component by the immutable identity the message names.
Validate the decoded control and data against the same chosen scope and prefix.
A control-only update can certify a new control and evidence pair while referencing the same immutable data root.
The shared data frontier cannot identify the control or evidence components.

Verify that the evidence manifest contains all dependencies required by that checkpoint and that their exact objects have durable custody.
Hold those dependencies while a certified base, replay suffix, borrower, or outstanding claim needs them.
Open the data root and replay the retained joint commands from the verified control basis.
See [A196–A199](amendments.md#study-51--2026-11-23).

## Charge each exact physical extent in its pool

Debit the full allocation once for each immutable physical extent at its actual pool.
For packed objects, use the allocation that must remain resident for any retained member.
Equal data in different versions or pools uses separate physical allocations.
Reserve the new allocation before any write can materialize it.

Register an additional use against the exact already charged allocation in the same local authority that orders disposal.
A checkpoint, evidence record, or move can use the same debit once its own custody reference is durable.
Charge reference and borrow metadata to their respective quotas.
Keep all original obligations through replacement or recovery of the pool controller.

Closing one use releases its own reference.
Keep the physical charge while the old extent is present or an issued write can still materialize it.
A surviving reference or independent read borrow retains the exact old extent during repacking and withdrawal.
Return the debit after exact stable disposition of that version at its physical owner.
See [A200–A202](amendments.md#study-52--2026-11-23).

## Restore physical protection after a pool fault

Track serving eligibility independently of the durable debit book.
An unavailable pool supplies zero new admission capacity.
Keep its issued keys, outstanding charges, references and borrows in the original physical scope.
An old borrow resumes on its original usable extent or settles with its own completion or effective stop.
A fresh read can acquire the replacement through ordinary admission.

Reserve each repair copy in the pool that will hold it.
Verify the exact source image and the replacement's durable registered bytes before placing it.
Declare a certified placement protected when each required input retains accessible exact coverage after removal of any single AZ.
The voter family also satisfies its current quorum contract before serving operations that require it.
Expose observed degradation with the scope of the evidence used to observe it.

Withdraw the old copy from fresh use after the protected replacement is installed.
The exact cutover can finish while the original custodian is unavailable.
Use the same protection check before a planned withdrawal.
Allocate room in eligible failure domains for repair while ordinary traffic is busy.
When that room is exhausted or the surviving source is unavailable, retain the unresolved obligations and defer recovery that requires the missing resources.

Require fresh scope and content validation before reusing a returned pool as a source of coverage.
Settle the original extent and return its charge only through its exact provider disposition path.
See [A203–A206](amendments.md#study-53--2026-11-23).

## Certify the complete recoverable cut

Bind a recovery certificate to the exact installed voter family and ordered prefix.
At certification, verify every checkpoint and suffix that its crash selectors can choose.
Each selector names an exact checkpoint envelope.
Its certified base and contiguous suffix reconstruct the same installed prefix.
Require readable custody of the envelope, its named control, data and evidence, all required manifest descendants, and all exact replay attachments of that suffix.

For each permitted AZ loss, verify a majority of the current distinct voters and charged physical coverage of every required input outside that same AZ.
Every available recovery majority intersects the durable installation quorum for the basis.
The recovery worker gathers that basis and reads the other inputs from their verified placements.
Several inputs can share the same physical allocation.

Evaluate coverage for both stable and visible selectors until the replacement selector is durable.
Keep old-only dependencies while any allowed selector, borrower or outstanding result still needs them.
An authority changes its voter family by the existing certified installation.
Redo the scope check at certificate use after a family change.
See [A207–A210](amendments.md#study-54--2026-11-23).

### Admit with the current AZ fault allowance

Validate the applied source, exact eligible append window, current voter family, and complete dependency support together.
Include the envelopes, named components, manifest descendants, and suffix attachments of every still-selectable view.
Use one failure case for the quorum and all of its independently held inputs.
Bind any preverified admission evidence to the exact lineage, installed prefix, selectable views, and their authenticated current custody and voter revisions.

Select a serving cut from the exact ready quorum, append window and dependencies.
The cut may exclude an unreachable AZ and can be selected without classifying its physical state.
A serving exclusion leaves the current protection interval unchanged.
A fresh acknowledgment requires exact reconstructibility across every credible first AZ loss.
The same durable operation can establish both readiness and protection when its evidence covers both.
In a replication layout, two exact durable copies in distinct surviving AZs suffice for a new input while the first loss is unknown.
Retain earlier copies and original debits until the post-withdrawal layout preserves coverage for every affected obligation.
A confirmed first loss continues to use the surviving case in the existing interval.
Bind that diagnosis to the exact interval, and keep it and its associated custody obligations through authority and voter changes.
Reverify exact eligible quorum and input coverage for every single-AZ case before resetting the interval.
Fresh admission uses the actual current scope and leaves earlier historical replay deterministic.
See [A263–A267](amendments.md#study-67--2026-11-23) and [A417–A421](amendments.md#study-105--2026-11-23).

### Recover protection as ordered control

Name each protection interval by the lineage and the chosen position that began it.
Keep that position and the optional confirmed lost AZ in the named control image.
Bind a confirmation and its inline proof to the exact interval and lost domain.
The confirmation may survive voter and custody changes within that interval.
A different confirmed loss cannot replace it.
A renewal sets a new interval at its chosen position after full proof for the exact current installed basis.
Include the covered acknowledged inputs, current voters and current evidence of custody in that basis.
Treat the frontier as a unique already chosen prefix in its lineage.

Carry the interval, the included frame evidence and its historical verification rules through ranked voter changes.
Recover from the selected checkpoint and all needed chosen frames in its suffix.
An older selector may need the confirmation or the renewal, even after the newer selector becomes visible.
Historical replay uses the retained proofs and scope at their chosen positions.
Fresh use verifies its own installed serving cut after recovery.

Give fully prepared renewal a fair local turn after its dependencies are ready.
Keep a ready turn local to choices whose changes would invalidate its checked basis.
Bind the chosen renewal to the exact basis even when some of its proof was obtained earlier.
Earlier evidence can carry forward when an exact current comparison proves the existing witnesses still cover the affected voters, custody and all current obligations.
See [A422–A427](amendments.md#study-106--2026-11-23).

Bind the interval to the deployment incarnation's continued ordered history.
A placement changes the acting authority and its local voters and custody.
The inherited interval keeps the same identity and regional AZ interpretation.

## Bound physical pool incarnations

Allocate a durable inventory slot before exposing a physical pool incarnation.
The same row accounts for the scope when it is eligible, quarantined, or still has outstanding custody after withdrawal.
Failure closes fresh admission and advances the scope's access epoch in its registered row.
Keep original charges, references, and possible effects at that physical scope.

Bring a reachable scope back through quarantine.
Verify its immutable incarnation, current access epoch, and authenticated exact book, including live allocation coverage and issued-operation fences.
Preserve its original accounting and apply the complete recovery certificate before using the returned copies for protection.
Creating an independent physical scope uses an independent row and a fresh non-reused namespace, even at a reused address.

At capacity, defer new incarnation registration and keep current eligible operations, validation, and settlement under their existing admission rules.
A terminal namespace closure can finish with the old service endpoint unavailable if the exact provider evidence is independently obtainable.
Release a row after its original durable disposition and after all charges and obligations are settled.
Use monotone durable issuance and positive registration to refuse a forgotten scope.
Provision an eligible replacement with sufficient physical and control headroom when the required availability budget calls for it.
See [A211–A214](amendments.md#study-55--2026-11-23).

## Encode the incarnation inventory and close exhausted identities

Give each inventory issuer a fixed-width non-reused serial within its authority scope.
When it reaches the largest serial, refuse new incarnations under that issuer and continue existing operations and exact settlement.
If an access epoch cannot advance on a fault, seal the incarnation with a terminal phase and retain its custody.
Only exact settlement can remove the sealed row.

Encode the issued watermark and the rows in one canonical inventory body.
Each row carries its scope, epoch and phase in fixed width.
Require strict descending scope order and reject unknown phases, out-of-range data, trailing bytes, and catalogs beyond the configured row limit.
Reserve bytes for both selectable inventory bodies.
Authenticate their enclosing checkpoint and complete the certified ordered replay before resuming admissions.
Keep inventory scope and order bound to the original physical custody catalogs.
See [A215–A218](amendments.md#study-56--2026-11-23).

## Recover the ordered incarnation inventory

Order incarnation changes and their immutable inputs in the inventory authority.
An issuance request names the exact next identity.
Apply it under the current bound and publish its result after the command is chosen and applied.
Reconcile the exact earlier result using its original command and ordered position.

Recover the current installed cutoff through the ranked authority protocol.
Carry previously chosen decisions even when the last learner or client never saw them.
A physical frame or durable accept is evidence for the ranked recovery process.
Only certified installation and applied recovery establish the authority's current inventory.

Open the selected base against its exact inventory body and physical ledger.
Recover each ordered frame through the installed cutoff, then resume admission.
Replay recorded evidence under the rules for the original command position.
Process later return or terminal evidence in a new ordered decision.
See [A219–A222](amendments.md#study-57--2026-11-23).

## Recover a bootstrap installation decision

When the authorized successor has no serving journal, allocate one single-value bootstrap slot for the exact intent in its certified target family.
Propose an exact image and its complete installation binding.
Each higher ballot durably promises and captures the latest accepted value at its prepare quorum.
Adopt the value with the greatest accepted ballot reported.
When every report is empty, propose an eligible recovered image.
A lost reply has no effect on the slot.
Use a fresh ballot and its certified reports to recover the choice.

For the data-bearing path, make each voter's exact image durable before accepting it and bind it to that accepted state.
Keep that binding through prepare, restart, and retransmission.
An installation that uses a physical reference instead must pre-register independently durable exact custody for that reference before the vote.
A readiness receipt may refer to a staged image already released.
Publication uses an exact chosen and applied seed.

A donor can fail after prepare, before the recovering coordinator materializes its reported image.
Take a new ballot and collect fresh reports from the reachable quorum.
Any previously chosen seed is still represented there.
A discarded unchosen attempt leaves its physical obligations to custody settlement.

Two surviving voters can each retain a different unchosen image.
Arrange enough repair headroom for an exact replacement while the older accepted image remains pinned.
Switch the accepted binding through a valid higher vote once the replacement is durable.
Release the unused older image after checking remaining custody.
Verify equivalent replacement headroom when media can share immutable extents.
See [A121–A125](amendments.md#study-33--2026-11-22).

## Replace a local journal base

A local vote means the exact bytes and the recovery binding are durable.
A storage adapter may establish both in one durable operation.
Decode contiguous exact records from a complete validated base after restart.
Use the ordered authority's certified cut for committed visibility and reconcile additional surviving frames as candidates.

Capture a fixed prefix for bulk compaction and keep subsequent records in a shared ordered suffix.
Make the complete replacement durable before publishing its selector.
During selector uncertainty both generations must recover the required history through every local durability vote, including votes issued during the switch.
Reclaim the predecessor only after the replacement selector is durable and its extents have cleared physical custody.
The bulk copy can finish and publish even if the head advances past its captured cut.
Stream-level checkpoint publication and logical trim still control which records need coverage.
This protocol depends on successful byte and namespace barriers and atomic selector replacement under the media contract.
See [A86–A89](amendments.md#study-25--2026-11-22).

An exclusive replica holder can serve from a validated visible selector after a process restart.
That reopen leaves both crash paths protected until successful durability evidence resolves the switch.
Resolve one switch before publishing the next.
A delayed durability barrier can hold both recovery paths in place, so foreground votes still depend on available tail capacity and its own durable storage path.
Bind a staged image to the validated predecessor for publication.
Reusing a stale preparation requires establishing a forward cut and its full exact coverage against the current view.

Keep every base and suffix extent required by either crash path, along with separately pinned extents.
Reclaim an unneeded unpinned extent independently of older live reads.
Recovered borrows stay charged until the exact operation completes or an effective stop is established.
The two-selector bound covers recovery choices.
Staging and historical pins consume physical capacity under their own admission budgets.
See [A90–A93](amendments.md#study-26--2026-11-22).

Bind named terminal witnesses to the exact selecting path.
Persist the exact bytes and discovery record before publishing a selector that uses a witness.
Store the bounded terminal evidence in the chosen settlement frame so replay can verify that frame from its own bytes.
Keep any required frame or named witness available under both crash-selectable roots.
Retire each independently when all selecting paths and borrower pins release it.
See [A360–A363](amendments.md#study-91--2026-11-23).

## Move ownership

Ordinary host replacement or membership changes act within the same logical group.
A cross-group move requires an authorized, destination-bound intent before seal.
A durable one-use destination reservation is the candidate for keeping former groups free of per-stream certificate replay fences.
The source binds the reservation, cuts an irreversible seal for its placement generation, and certifies the retained prefix and outstanding custody.
The seal certifies the holder and writer epoch current at its commit decision.
The source validates one authenticated attachment against its exact applied seal.
The attachment binds the protected reads, writer invocation floor and independent delivery book at the ordered position of the seal.
Its manifest covers the needs of both books, including original physical delivery dependencies after logical read closure.
The placement change preserves the lineage-wide delivery issuance floor and each row's original physical borrow.
The installed successor applies later ordered releases using authenticated evidence from the original custodian.
See [A351–A354](amendments.md#study-89--2026-11-23).

Keep the authenticated seal and its original delivery rows identical under each recovery realization.
An exact durable terminal receipt can realize a stopped delivery whose original extent is unavailable.
Verify every affected delivery against its original lineage, delivery key and physical binding.
Keep custody for any use of that extent by base replay, installation, a protected read or a delivery without exact terminal proof.
Check and pay for the recoverable receipt before activation uses it in place of media.
The receipt cannot authorize physical use of the stopped borrow.
Allow physical disposal after all selectable paths can recover without that extent and the existing provider disposition conditions hold.
See [A355–A359](amendments.md#study-90--2026-11-23).

### Carry protection and settle original copies independently

A cross-group seal within the region covers the exact protection interval and every continuing recovery obligation at its ordered cut.
The destination opens the named control and rechecks target installation and all inherited coverage.
Activation carries the interval and affects only that deployment.
An authentic confirmation of the same interval remains usable by the installed target after the source seals.
A transfer preserves any spent allowance until the target orders an independently qualified renewal.

Coverage may include held exact original copies while the target has an eligible installation and replay path.
Activation preserves original custody charges and permits no unconditional physical release.
Admit withdrawal against the current survivor set for every continuing obligation.
Exclude the exact version from future witnesses when withdrawal is ordered, before its storage effect can happen.
Require later reservations to use that reduced set.
Providers act only on positive authorized withdrawal of that exact physical generation.
Existing live read, delivery and checkpoint holds retain their own disposition requirements.
Keep the withdrawal and its charge until exact terminal settlement.
See [A428–A433](amendments.md#study-107--2026-11-23).

Record the withdrawal in the original allocation's custody phase.
The ordered transition excludes that version from coverage, closes fresh use and supplies exact effect authority.
Require release of every registered hold before choosing it.
An older selectable root and an originally paid delivery keep their holds independently of the latest root and the ordinary read.
Use only open, charged versions as witnesses.
The provider can execute a dispatched exact withdrawal while the issuer is unavailable.
This uses durable authorization of the original version and the provider's effective write fence.

Recover the custody phase and its registered holds from the named image and complete chosen suffix before admitting fresh work.
A physically present copy can already be withdrawing.
A staged action cannot authorize an effect.
Keep its debit while the provider effect or stable settlement remains pending.
Settle only with authenticated stable absence at that original version, then apply the ordinary exact charge return and collection rules.
See [A434–A439](amendments.md#study-108--2026-11-23).

### Publish changed dependencies with original registered custody

Record the exact preparation and its planned version identities before sending to custodians.
Each original custodian orders acquisition and withdrawal against its exact version phase.
A held registration keeps the version open for its charged use.
An ordered withdrawal excludes later acquisition of that generation.

The installed publisher checks the current exact catalog and ordered basis, complete exact registrations, and reconstruction under every currently allowed failure case.
An immutable preparation can preserve evidence through a protection change when its registered placements still cover all current cases.
The publisher can use retained receipt evidence without recontacting the custodians whose holds remain effective.
Evidence for each covered failure case can be calculated over the immutable registered plan and checked against the current required cases at publication.
A plan with insufficient coverage needs independent qualified backing before publication.

Order publish and abort at the authority that owns the plan.
Apply an exact canceled decision at each original custodian, including one whose acquisition reply was lost.
Close the original planned scope so delayed acquisitions cannot reestablish the hold.
Keep an unresolved preparation charged until the authority recovers its outcome.
A new visible checkpoint preserves the prior selector's separate registrations until its exact release becomes authorized.
See [A440–A445](amendments.md#study-109--2026-11-23).

The target's ordered activation verifies the exact sealed image against its current quorum and consumes the reservation.
Activation carries the same holder and epoch at a higher placement generation.
A pre-copy receipt refers to the membership that certified it. Revalidate on a membership change or install a durable obligation that transfers the prepared cut across changes.
Protect each attested copy through activation. Invalidate readiness before disposing of any copy it relies on.
Release a source copy after durable activation if its withdrawal preserves all affected recovery obligations and any original physical borrows have completed or stopped.
See [A38–A40](amendments.md#study-13--2026-11-22).
A holder change is a separate higher-epoch fence. An unreachable holder still needs normal RTDB failover.
Directory routes update independently after activation.
See [A31–A33](amendments.md#study-11--2026-11-22).

The source can still serve during precopy.
There may be a write pause between seal and target activation.
Without proof that the old authority is fenced, a destination cannot take over based on silence.
With a current durable image and the authenticated seal in hand, the target quorum can activate during a directory outage or loss of the inter-group link.
A forgotten or expired reservation after seal can strand the stream.
The source serializes seal against abort for the exact reservation nonce.
Only an abort receipt for that nonce lets the target release it.
An unreachable source can leave the reservation pending within the fleet's bounded preparation budget.
See [A08–A12](amendments.md#study-02--2026-11-22), [A21–A23](amendments.md#study-06--2026-11-22), and [A29–A30](amendments.md#study-10--2026-11-22).

## Bound retention explicitly

Replay admission and logical trim share the stream authority.
The authority allocates a never-reused permit ID scoped to the stream incarnation.
Prepare records the exact first required LSN. Admission consumes the matching still-live preparation and validates that LSN against the current floor.
Close clears that exact issued ID, including an ambiguous pending admission.
A trim cut must fit the published checkpoint and every still-active replay grant.
The seal carries the pending and holding table, floor and issuance high-water mark.
See [A44–A46](amendments.md#study-15--2026-11-22).

A checkpoint certificate binds the stream incarnation, compatible format, exact committed prefix, decoded continuation state, and durable manifest closure.
It names the exclusive position from which replay resumes.
Continuation state includes an intake position if reopening needs it.
RTDB currently retains the boundary record for this purpose.
A fork can share immutable objects with its parent under a child-genesis certificate and child custody.
Replay uses a compatible protected root at or before its captured upper cut and ends exactly at that cut.
See [A47–A49](amendments.md#study-16--2026-11-22).

The latest-read decision captures the head and reserves the current checkpoint root and its nonempty replay suffix together.
It takes a logical reference to the root's already registered custody.
It needs one authority decision regardless of how many objects the manifest names.
A checkpoint at the captured head requires only the root reference.
The exact reservation survives publication and handoff.
A protected marker result shares that reservation's bounded control lifecycle.
The selected control image binds its original invocation and canonical result to its exact hold serial.
The checkpoint authenticates the read rows and hold table as one named control at the same ordered position as the journal state.
A sealed read attachment carries that section and its original dependencies at the exact source seal.
The attachment excludes the source image that contains its own reference.
Verify each retained basis against the named manifest before opening reads or activating the target.
Keep the sealed logical read book frozen.
An exact physical stop can finish at the original endpoint, and the installed successor orders the corresponding logical release.
See [A322–A325](amendments.md#study-82--2026-11-23).
Order the complete protected admission and logical release among the journal commands.
The chosen frame binds the full invocation or permit and its exact evidence.
Replay the full frames from the selected combined base through the chosen cutoff.
Use stable historical verification to reproduce a chosen decision.
Keep the verification material for the command histories that either selectable base still requires.
Bind physical completion and effective stop to the exact permit so the installed owner can use the evidence at its own next eligible position.
Then check current serving authority and required live read dependencies before any recovered reply.
See [A326–A329](amendments.md#study-83--2026-11-23).
A second request for the live invocation uses that row.
Exact completion or effective stop releases the pair and permits reuse of its slot under a new serial.
An explicit historical cut needs its own protected recovery basis or the applicable history contract.
Checkpoint publication and root disposal share a fence on the exact custody identity.
Following disposal authorization, a delayed receipt for that identity cannot republish it.
See [A53–A56](amendments.md#study-18--2026-11-22).

A stale cursor receives the floor and reopens a valid checkpoint or uses an exact historical feed if the product supplies one.
Return success only after the required custody and replay protections are in force.
An extent lookup is a hint. Validate the current index and exact contents while acquiring a physical borrow.
Keep that borrow against its original extent and endpoint if the catalog changes or the stream moves.
Expiry first fences new admission. Exact operations that already pin every input may finish under independent physical custody after their logical hold releases.
An operation that can still discover more dependencies drains or is effectively fenced before its logical protection is released.
Physical custody ends only on successful completion or a verified effective stop. A timeout leaves it charged to the physical budget.
See [A24–A26](amendments.md#study-08--2026-11-22) and [A41–A43](amendments.md#study-14--2026-11-22).

RTDB declares the full immutable graph of a checkpoint, including inherited versions and the containing version for each packed dependency.
The object custodian registers each exact physical dependency before the root is admitted.
Publication consumes the complete receipt bundle under the root's authority.
Reads share the registered root through their stream reservation.
Root closure precedes release of its dependency registrations.
A release settles the exact root-version identity even if a delayed acquisition has yet to arrive.

Each physical version has a disposal gate at its custodian.
The gate closes only when the version has no active reference or admitted borrow.
A scan can identify candidates, and the gate revalidates them in the same order as new references.
Once closed, the exact version cannot admit another reference.
The provider deletes the fenced identity in its original namespace, even if the logical name now resolves to another version.
The graph can register different versions independently, using one ordered custody decision per version or a correctly scoped batch.
See [A57–A60](amendments.md#study-19--2026-11-22).

Before any acquisition is sent, the root authority records the immutable binding and the serial issued for each custodian batch.
After a crash, recovery replays those identities or durably closes the attempt and releases all its planned interests.
The issuer orders publication against terminal close.
The intent remains recoverable until its closure is settled, including when the receiver floor has already advanced past its serial.
The exact binding includes the root, immutable manifest, and physical versions in the batch.

A custodian compacts terminal markers by advancing a durable per-channel floor.
The issuer certifies the covered prefix using closed intents and durable acknowledgments of exact installed grants.
The custodian preserves existing grants, including old grants whose roots are still live.
It serves their exact retries and accepts their exact releases.
For an absent slot, the floor rejects new acquisition at or below its serial.
The issuer replenishes its finite window only after the custodian confirms the floor is installed.
An unsettled intent can consume that channel's window.
Existing live and staged grants remain charged to their physical footprint, and cleanup has reserved service at full capacity.
See [A62–A66](amendments.md#study-20--2026-11-22).

The custodian mints a fresh channel handle under a durable issuance counter for its physical incarnation.
Each configured route slot holds at most one active channel.
Closing a channel frees the slot and discards its floor and terminal acquisition markers.
Already installed grants remain at the custodian under their original exact keys.
An exact live retry or authorized release uses that grant directly.
An absent old grant cannot be admitted again, even when a successor uses the same route and serial.
After closure, an authenticated exact lookup distinguishes a held grant from stable absence.
Control messages and acknowledgments carry the handle they apply to.
See [A67–A70](amendments.md#study-21--2026-11-22).

When custody issuer authority moves, the final seal carries its exact unresolved intents and terminal decisions.
The successor can reconstruct this book from the certified checkpoint and retained tail.
The predecessor stops deciding at the seal.
A registration authorized before the seal can still arrive afterward at its original custodian.
The successor reconciles and settles it by the inherited physical key.
Keep the intent until settlement is durably fenced, including when the receiver has not yet seen the acquisition.
Fresh work uses fresh scoped keys while inaccessible old grants remain charged to their custody budgets.
See [A76–A80](amendments.md#study-23--2026-11-22).

The physical custodian recovers its own complete committed state from the active recovery quorum.
Recover the issuance counter, channel floors and remaining refusal markers alongside exact grants, active borrows and erasure fences.
Apply the same exact-coverage and old-majority fence to custodian voter changes.
An authenticated cancellation fences its exact slot when it is empty or holds the matching binding.
Persist that refusal before acknowledging closure.
See [A81–A84](amendments.md#study-24--2026-11-22).

Admission charges the committed recovery debt and retained debt separately, plus pending work and physical resource budgets.
A failed checkpoint may consume the remaining headroom and lead to backpressure.
A live replay hold can fill retention with already checkpointed records.
A copy or replica installation also consumes a bounded budget.
Control operations needed to release capacity have reserved resources.
Guaranteed storage reservations cannot be loaned into irreversible committed work.
Stream isolation protects record contents and authorization.
Shared admission and latency can reflect aggregate load.
See [A13–A15](amendments.md#study-03--2026-11-22) and [A27–A28](amendments.md#study-09--2026-11-22).

### Exact historical resume, if required

Exact history can come from RTDB's durable history format once it proves the promised event projection, or from a dedicated archive.
Within the history window promised by the product, retirement of journal bytes needs published gap-free exact event coverage in addition to checkpoint coverage.
The reader freezes the upper cut and joins the archived prefix to a suffix admitted against the current floor.
When trim moves past the proposed join before admission, the reader can refresh from archive coverage and retry at the same upper cut.
Lagging event coverage consumes retention headroom independently of checkpoint progress and can stop new writes when that headroom fills.
See [A50–A52](amendments.md#study-17--2026-11-22).

## Close authority, then dispose of copies

The current owner serializes retirement against seal.
Retirement before seal prevents the transfer from activating.
After seal, the predecessor can redirect and the active successor can retire.
The successor inherits every outstanding custody obligation.
Record a custody destination before issuing a copy and retain it through retirement until disposition is verified.

A terminal receipt closes the stream at its serving authority.
A fresh invocation after that decision has a floor at or past the terminal command.
No certified applied view at or above that group position grants read authority, even if the stream data LSN is unchanged.
The standing-window candidate permits an earlier overlapping invocation to borrow its exact live view when its own verified floor permits it.
Requiring physical admission to stop before terminal publication also needs a decision excluding every open gate and every staged gate still authorized to open.
A disconnected gate can prevent that stronger terminal receipt until it can be fenced.
See [A114](amendments.md#study-31--2026-11-22).
A physical erasure receipt is a later result.
Before certifying disposition, each addressed location durably fences new writes and read admissions for the retired incarnation and resolves its outstanding physical borrows by completion or an effective stop.
When a surviving fork still depends on a version in the retirement scope, install a verified independent copy and publish the replacement reference before withdrawing the source.
The copy verifies each declared logical member through its exact version and range.
The physical packing or encryption envelope can change.
Bind the replacement to the captured stream, cut, root and catalog revision, and to the exact destination incarnation and root version.
Register the target dependencies before accepting its verification as publication evidence.
Compare the capture with the current publication under the referrer's authority when switching the root.
That decision preserves the checkpoint cut and can use durable target evidence during source disconnection.
Older snapshots continue to hold their original source basis, and admitted reads keep their physical borrows.
Authorize source disposal when every remaining referrer, snapshot and borrow has settled.
See [A71–A75](amendments.md#study-22--2026-11-22).

An erasure receipt for the retired deployment covers its defined physical and authority scope.
The surviving fork retains its admitted history under independent custody.
A provider or replica that cannot attest leaves erasure pending.
Forgetting a local fence requires another gate that rules out every older write.
Commit the exact erasure fence before dispatching the provider operation.
An issued effect can complete during custodian downtime, and exact recovery preserves its authorization.
Commit disposition on exact absence evidence.
See [A16–A20](amendments.md#study-04--2026-11-22).
See [A61](amendments.md#study-19--2026-11-22).
See [A85](amendments.md#study-24--2026-11-22).

### Settle regional custody by exact identity

Bind each newly admitted hold to a non-reused read identity, its deployment's registered root, and the exact physical version.
An authenticated completion or effective stop consumes that identity once.
Keep one physical charge per version while independent references or admitted reads depend on it.
The per-version count follows from the live exact identities.
Meter the hold table separately so that reads of existing bytes can still proceed at full physical capacity when read quota is available.

The ordered close excludes fresh read authority for the retiring deployment, while existing protected operations retain their exact holds.
Resolve the deployment's own registered references and holds.
When an extent is outside its exact erasure scope, an independent holder may keep serving it throughout the retirement.
When an extent is inside the scope, complete its original physical disposition before certifying erasure or returning its debit to the pool.
The recovered authority must establish complete scope and exact terminal evidence.
See [A235–A238](amendments.md#study-61--2026-11-23).

## Availability boundaries

| Desired behavior | Premise and limit |
| --- | --- |
| Writes and eligible writer replacement on an enrolled stable placement | The group has a usable route, quorum, ordered eligibility, recoverable inputs, and headroom. The successor catches up before serving. |
| Transfer during directory loss | The intent is already durable and its evidence reaches the successor. Installed evidence removes the source-link premise for activation. |
| Repair an existing target while an incoming image is unavailable | Both membership quorums are reachable, and the recovered target journal has no dependency on the missing image. |
| Reclaim attempt markers while a ready candidate remains | Advance the installed cutoff through the exact ready row. Issuance can resume within its window, while every live grant and unsettled copy remains physically charged. |
| Uninterrupted writes through arbitrary disconnection | An isolated target cannot guarantee takeover while the source might still serve. A safely frozen source may create a pause. |
| Bounded recovery with ongoing commits | Checkpoint progress must eventually reclaim work. Once the finite budget fills, ordinary admission can pause. |
| Latest snapshot through ongoing checkpoint publication | The stream reserves the root and needed suffix when it captures the head. Completion needs an admission slot, fair service, and access to the protected inputs. Stalled reads can hold retention until completion or a proved stop. |
| Exact replay at a historical cursor | A declared history window and an exact event source cover the cursor. Beyond the WAL, lagging event coverage can stop new commits under a finite retention bound. |
| Terminal closure with quorum | The active authority can close. Fresh floors exclude new invocations on lagging serving endpoints. Cleanup may still need inaccessible current, retired, or staging locations. |
| Deadline for all first physical borrows at terminal closure | Enforcing the deadline for overlapping invocations needs an admission decision that intersects retirement or a fence on every eligible open and staged gate. |
| Read through a serving-window rotation | Prepare a verified replacement under spare custody capacity, switch local admission and settle the old holds independently. The replacement's cut must cover each new read's floor. |
| Physical erasure completion | Every recorded scope has trustworthy physical disposition and a durable proof that no authorized write can still take effect. |
| Physical read reclamation after expiry | Every affected endpoint can establish completion or an effective stop. An already-protected exact read can remain charged to its source extent even after logical trim. |
| Interrupted checkpoint registration | The durable plan survives. Cleanup progresses when its issuer and each affected custodian become reachable. Registered pins stay charged until exact release settles. |
| Custody channel rollover | The custodian can retire its admission handle while an old grant stays live. Releases of old grants remain available through the custodian that owns them. |
| Custody issuer failover | The successor has the exact staged seal and can take over with the predecessor offline. Old grants still require their original custodian or durable settlement evidence. |
| Physical custodian restart | A reachable current quorum recovers the complete certified state. Pending provider effects keep their exact fences and settle under verified provider evidence. |
| Moving a checkpoint during source disconnection | A reachable referrer can publish its current verified and registered copy. Source references and staging remain charged until their independent obligations settle. |

The current evidence is strongest for bounded design behaviors and the stated Lean abstractions.
The move and journal models refine the logical kernel. Their composition connects successful activation to current recovery coverage.
Remaining refinements include actual consensus and persistence, cancellation under repeated moves, RTDB checkpoint encoding and reopen, endpoint implementations of admission and stop fencing, physical custody, and authorization.
Expressiveness and independence remain open for the whole contract.
The shared stream projection and constructive countermodels show that the two logical bounds and both trim guards remain independently necessary.
See [A268](amendments.md#study-68--2026-11-23).
Latency and recovery-time targets require measured workloads.
