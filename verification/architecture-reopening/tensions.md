# Logkeeper architecture tensions

2026-11-23

## Decision

Keep one ordering authority per installed deployment and let it share voters, batching, storage and scheduling with other deployments.
Scale a regional cell by adding or reshaping these groups within it.
Keep physical location, replication and capacity planning out of the identity of an ordinary deployment request.
Use a separate cross-group handoff only when the ordering authority itself must move.

The [contract review](contract-review.md) gives the priority changes, persistent limits and product decisions.
The [protocol decisions](contract-resolution.md) track the selected fixes and unresolved choices.
The reference already separates a new latest observation from exact recovery of an earlier protected invocation.
The caller inventory leaves the Bijection gateway's ambiguous read contract open.
The exact path also requires next-nonce admission within a writer grant.
The finite comparison below shows an alternative with bounded additional state.

## Fundamental limits

| Tension | Limit that survives architecture changes | Boundary that resolves it |
| --- | --- | --- |
| One writer and availability in a partition | A destination with no intersecting decision or recoverable fence cannot distinguish an isolated live source from a source that irrevocably stopped. | Keep ordinary commits and failover with the installed group. Activate a new authority only from a verified fence and exact installed state. A separate regional decision quorum would introduce an extra failure condition for ordinary service. [Architecture comparison](comparison.md) · [Handoff](../02-handoff/report.md) |
| Exact replay and finite resources | If a stalled consumer, checkpoint or event archive must retain an indefinitely advancing exact history, bounded resources eventually run out. | Keep a bounded checkpoint-backed recovery suffix. Put exact historical event history under a separately funded horizon. A permanently lagging required archive consumes its own budget and eventually blocks that stream. [Bounded retention](../03-retention/report.md) · [Exact feed](../17-exact-feed/report.md) |
| Instant transfer and peak physical custody | Old data that a borrower can still legitimately use occupies capacity even after a new version is chosen. No allocator can spend that capacity twice. | Prepay peak destination, staging, retained predecessor and repair costs. Queue transfers without a feasible schedule. Prefer in-group replacement or leave a healthy group in place when relocation yields no service benefit. [Concurrent capacity](../43-concurrent-capacity/report.md) |
| Bounded cleanup space and independent progress | A finite reserve can fill with waits if remote operations hold it. Even a ready operation can be bypassed indefinitely if it races every new arrival. | Keep the pending obligations charged in their original records. Use shared local workspace only for ready publication and bound each ready slot's turn. Use dedicated workspace when its full per-obligation reservation is justified. [Settlement workspace](../97-settlement-workspace/report.md) |
| Early reuse and bounded crash recovery | A confirmed credit can fund new capacity only if every recovery choice can recover the refund. Keeping redo for an old selector can itself prevent funding the replacement needed to retire it. | Use the original owner's exact durable suffix with workspace for the overlap. A stable whole-image switch trades earlier reporting for lower overlap in the checked model. [Settlement redo](../98-settlement-redo/report.md) |
| Fast retirement and a global physical deadline | A quorum that can close fresh logical admission may be unable to stop a previously authorized operation at an isolated endpoint. | Return distinct evidence for logical closure and physical erasure. An overlapping protected operation may complete in the current contract. A strict physical cutoff needs an intersecting admission or stop at the effect boundary and can delay that stronger receipt. [Standing custody](../31-standing-custody/report.md) · [Provider I/O closure](../40-provider-io-closure/report.md) |
| Mask every AZ failure and keep writing through successive failures | Healthy coverage for one AZ says nothing about a subsequent loss before the lost coverage is restored. | Spend one fault allowance per verified interval. Admit degraded work under the surviving scope, protection evidence and headroom limit, then restore a fresh allowance after verified repair. Separate durability from throughput and recovery-time objectives. [Full degraded admission](../67-full-admission/report.md) |
| Durable acknowledgment while AZ failure is unclassified | A lost A and a slow A can give the same replies. An acknowledgment on B alone would lose the write if A was slow and B was the first true loss. | Open the verified serving cut directly. Keep the full acknowledgment and withdrawal checks until the actual first loss is independently established. Prepay the independent placement needed for the unknown-loss write path. [Degraded evidence](../99-degraded-evidence/report.md) · [Protection model](../105-service-scope-protection/report.md) |

Logical groups solve the authority-placement and blast-radius problem.
The proposed regional cell can grow by adding groups under the region’s actual capacity and service budgets.
The RTDB Multi Allium currently has explicit configured cell bounds, so the models do not establish an unbounded deployment count.
A single hot deployment still has a finite ordered command service rate.
Parallelize payload preparation, batching, checkpointing, reads and repair before considering independently ordered state inside it.
Splitting that state changes which operations require cross-group ordering and must be evaluated under RTDB's actual transaction semantics.

## Proved choices worth reopening

### A next-nonce floor imposes head-of-line blocking

Study 84 proves the one-word floor and ordered abandonment preserve exact non-reuse through closure, compaction and scope change.
The same rule makes an otherwise independent read with nonce 2 wait for nonce 1, even when the journal, all physical inputs and admission slots are available.
Abandonment resolves the gap when the issuer can prove it is safe to abandon.
A new writer grant fences the old identity space but also forces unrelated work to move scope.
This is an architecture cost of the floor and issuer interface.
The lower bound proved in Study 84 applies when arbitrary subsets of identities may remain outstanding and replayable.
[Invocation floor](../84-read-invocation-floor/report.md)

A bounded selective window stores a floor and a fixed bitmap above it.
Admission or authenticated abandonment marks exactly one bit.
The floor advances only across a contiguous run of decisions.
An arrived independent request inside the window can proceed without dropping any earlier request.
Once the window fills behind a gap, admission still needs resolution or an explicit scope change.
A largest-seen watermark has smaller state but silently spends requests the journal never decided.
Journal-assigned IDs avoid sender-side holes, but cannot by themselves identify a request whose first reply was lost.
They need caller-known durable deduplication identity or a fresh-retry product contract.

[ReadIdentityChoices.tla](ReadIdentityChoices.tla) compares three usable nonces and widths one and two under the same conditions.
It holds the writer grant fixed and abstracts exact receipt, slot capacity and scope replacement.
TLC checked the following under weak fairness of enabled actions.

| History | Evidence |
| --- | --- |
| Nonce 1 never arrives and nonce 2 is eligible except for its position | The next-nonce rule has a temporal counterexample. The width-two window admits nonce 2 in the 5-state configuration. |
| Nonce 1 arrives independently later | Both nonces complete and can never be admitted twice in the 22-state width-two configuration. |
| Another request arrives past a full window behind the first gap | Nonce 2 can complete and nonce 3 remains excluded in the 5-state configuration. |
| Earlier identity is explicitly abandoned | The incumbent advances and completes nonce 2 in the 6-state configuration. |
| Replace explicit consumption by largest-seen or drop the sparse marks on crash | Exact consumption fails in one and two transitions respectively. |

The window is a candidate for callers that permit overtaking.
[Study 101](../101-selective-read-window/report.md) verifies general canonical compaction and next-only compatibility at width one.
[Study 102](../102-selective-ordered-recovery/report.md) checks exact ordered replay, a named packed checkpoint and writer handoff.
The candidate still needs comparison against the number of independent protected reads RTDB actually has per writer grant.
If RTDB already serializes them, one word may be the right design.

### Exact lost-response recovery is a separate service from latest-read freshness

The current contract asks the journal to return an original protected admission result after a lost reply, then separately support finishing an already authorized delivery through authorizer loss.
The read book and delivery book have different lifetimes.
Studies 88–91 show that a delivery may outlive its read row, and its proof can outlive both.
Collapsing all three lifetimes into one slot drops evidence or prolongs custody.
Keeping a unique table and protocol for each operation also raises state, serialization and failure costs.
[Retained delivery](../88-retained-delivery/report.md) · [Receipt selectors](../91-receipt-selectors/report.md)

Compare two product-preserving and one product-changing shape against the same histories.
First, use one explicit protection operation on the existing ordered journal that atomically captures a basis, authorizes use and reserves its custody when the caller needs all three.
It targets the gap between marker admission and delivery authorization, where separate public operations may expose an extra failure window.
It still needs the two lifetime distinctions when multiple independent uses of a captured result are part of the contract.
[Study 93](../93-atomic-read-capture/report.md) reproduces repeated invalidation with fixed preparation and checks a conditional one-decision path with enforceable prepaid delegation.
The split reference remains available when no paid delegation spans selection.
[Study 94](../94-standing-read-credit/report.md) moves logical serial assignment out of provider preparation and checks that missing optional coverage cannot hold ordinary publication.
Second, use an invocation-bound current-quorum read index and a pre-registered serving window for fresh reads that acquire local exact physical protection.
Study 29 checks the fresh quorum fence and Study 31 checks the standing custody case.
The separate exact reissue and uncertain protected-admission paths still require a durable identity and result.
A read index alone supplies neither operation admission nor a replacement for an exact receipt.
Third, offer fresh retry for ordinary observation-only reads and make exact recoverable read handles an explicit operation.
This removes the need to preserve the original answer on that ordinary path, but changes the current API guarantee and needs owner agreement.
[Read index](../29-read-index/report.md) · [Standing custody](../31-standing-custody/report.md) · [Ordered reply admission](../87-ordered-reply-admission/report.md)

The decisive comparison is to run the same lost response, close, retirement, checkpoint and reconfiguration schedules against those paths.
Compare durable decisions and retained bytes as well as safety.
A path that shifts work from the journal to an equally synchronous remote proof issuer may cost more and weaken availability.
Study 96 shows that a recovered choice can be settled with the exact frozen delivery set, a live allocation check and durable non-reuse.
This gives the standing-credit candidate a bounded retirement mechanism.
After a hidden choice the original provider needs the journal's exact recovered set even when it saw no work locally.
Count that recovery traffic and the pointwise peak of live, staged and retained charges in the comparison.
Select fusion only if it improves durable decision count or observed completion time on the exact-recovery workloads, within the same capacity and outage contract.
Keep the split reference if fusion only shifts synchronous work, or if the gain requires ordinary writes or checkpoint publication to wait for optional read backing.
[Original provider settlement](../96-standing-provider-settlement/report.md)

An initial read-only inventory of RTDB commit `f3be413735` found separate paths already.
In `rust/crates/node/src/session.rs`, `Session.pin` first awaits the client token, then decodes an explicit snapshot or asks for `fresh_snapshot_basis`.
A read-only transaction subsequently reuses its pinned basis.
In `rust/crates/node/src/node.rs` and `database.rs`, the placed fresh path confirms a replica read index and waits for application before returning the local basis.
In `rust/crates/multi/src/logs.rs`, `LogletReadIndex` confirms a quorum frontier with a timeout.
The separate placed attempt redemption path in `node.rs` and `placed_receipts.rs` reconciles the exact **transaction attempt**, waiting for the recoverable closed-epoch frontier when required.
The `ServeOnSubscriber` rule in `allium/rtdb-multi.allium` likewise uses a read index and application wait for fresh observations.

This is evidence that latest observation and exact transaction reconciliation can use different primitives in RTDB.
It does not establish what Bijection promises to a caller that loses a protected read result or starts an effect before its result is visible.
[Study 92](../92-read-contracts/report.md) extends the inventory to RTDB Flight SQL owned reads and Bijection’s WorldStore and warehouse boundaries.
It compares latest and exact recovery under response loss, scope replacement, retirement and custody races.
Confirm the remaining gateway retry semantics before changing a public exact-recovery guarantee.

### Cross-pool order prevents deadlock and leaves placement quality open

The strict pool order proof rules out cyclic acquisition.
It does not show that prepared partial holds admit the same moves or meet the same deadlines as a single enforcing vector owner.
When one authority actually enforces all relevant reservations, use local atomic admission to avoid partial holds.
For independent pools, the comparison should include centralized scheduling of independently enforced holds, atomic vector escrow and direct local preparation under the same bounded scratch space.
Keep all three off the installed group's ordinary request path.
Before paying for the extra coordinator, require measured or modeled improvement in feasible admissions, pause or recovery under the same skew, pin and one-AZ histories.
[Concurrent capacity](../43-concurrent-capacity/report.md) · [Shared comparison](comparison.md)

### A receipt can be complete without retaining the same physical copy

The recent proofs converged on three distinct questions after a provider stop.
Did the exact effect stop, can the current authority settle the obligation, and can each old recovery selector still reconstruct the choice?
A terminal receipt can replace a delivery-only payload for readiness while independent base, read or live delivery needs keep their data.
Put bounded evidence inside the chosen settlement record so exact ordered replay has no detached lookup.
Keep a named witness only where a mounted path needs early terminal evidence.
Share the verification and naming mechanism across domains where their evidence has the same role, and keep accounting at the original physical owner.
A unified regional receipt table would recreate a remote availability dependency unless its contents were independently replicated into each installed scope.
[Terminal delivery witness](../90-terminal-delivery-witness/report.md) · [Receipt selectors](../91-receipt-selectors/report.md)

## What would change the design

1. Compare bounded selective admission and one-word FIFO using the same RTDB caller mix, pending gaps and crash histories.
   Keep exact non-reuse and durable ordered settlement fixed.
2. Inventory RTDB latest-read callers before extending the receipt protocol.
   Model the standing read path, atomic capture-and-use and existing ordered lifecycle against the same histories.
   Bring any change to exact original reissue or overlap-at-retirement to the product owner.
3. Reuse the existing relocation comparisons to measure whether the bottleneck is authority placement, physical bridge capacity, or scheduling fairness.
   Keep the funded installed service contract fixed.
4. Treat pool erasure and stable stop as interfaces to the provider effect boundary.
   Qualify that boundary against delayed writes, version creation and restore before proving more service-level behavior that assumes it.

The formal results used here cover their stated models and fault bounds.
The new read comparison is bounded evidence.
It does not change the current contract or establish throughput.

## Reproduction

Run the architecture comparisons or just the read identity cases with Python 3.13, Java 21 and TLC 2.19.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
python3 verification/architecture-reopening/run.py read-identities
```
