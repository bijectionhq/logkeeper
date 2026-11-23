# Independent design seeds

2026-11-23

All eight proposals were collected before the shortlist.
The three designers received the same [brief and histories](brief.md) in isolated contexts.
They shared no prior design, files, or peer proposals.
The identifiers below preserve their separate proposals where the underlying designs converge.

## A1 · Stable pooled journal

- **Owner and success.** A group's quorum jointly orders bytes, append results, writer grants, barriers, trim, retirement and membership. A new worker takes an existing funded grant. Intersecting membership replacement protects the same group identity. A separate group can activate from an authenticated source seal and exact target installation, using permits from independent pools.
- **Failure.** Recover a hidden chosen append from the surviving quorum after one AZ loss, a lost reply and worker failure. Staged rivals remain invisible. A pinned reader prevents its original capacity release. Unreachable scope without terminal evidence keeps erasure pending.
- **Cost and rejection.** The group needs usable routing, spare recovery capacity, and retained receipt and payload coverage. Reject if an eligible worker needs the allocator or reconfiguration admits competing extensions. Test after the reply is lost and with reconfiguration in flight.

## A2 · Sharded decision ledger and coordinated funding

- **Owner and success.** Extent pools attest protected bytes. A separate sharded ledger chooses the stream position, writer epoch and result against those receipts. The ledger orders checkpoints and closes admission. A joint capacity transaction admits the physical move, and an installed target keeps its activation certificate.
- **Failure.** The decision ledger distinguishes a lost chosen result from an unchosen object even after an AZ loss. Coordinated scheduling can use charged scratch space. Pins continue to charge their original pools. Effect owners fence and dispose of retired data.
- **Cost and rejection.** Append has two dependent durability steps. The ledger must remain reachable through the claimed fault envelope. Reject if its outage, tenant coupling, or added step misses the budget, or if bundled funding fails to improve moves with real temporary headroom. Test the same moves with and without a bridge.

## A3 · Storage-native conditional append

- **Owner and success.** The storage namespace atomically commits bytes, head, generation and exact result under one conditional operation. It owns replica repair, read pins, retirement fences and physical disposition. Cross-namespace moves require an authenticated seal and exact destination capacity or a protected borrow of bytes already in valid placement.
- **Failure.** After one AZ loss, the old request is either represented by its exact receipt or remains uncommitted. A delayed old-generation physical write is rejected where the bytes would materialize, including after restore.
- **Cost and rejection.** Requires a real storage primitive with ordering, exact results, multi-AZ durability, staging-scope inventory and restore-safe effect fencing. Reject on any unguarded persistent path. Force a delayed write across retirement, scope outage and restoration before relying on this candidate.

## B1 · Stable logical quorum with independent pools

- **Owner and success.** A logical quorum owns order, receipts, worker fencing and membership. Pool owners admit their own exact byte and staging reserves. An irrevocable source seal and durable destination installation bind the retained history, suffix, results and funding. The original custodian can return capacity after verified disposition.
- **Failure.** A replacement consumes a prepaid slot and returns the chosen receipt despite the lost worker and AZ. The target can rely on retained installation evidence after source-route loss. A previously pinned source remains charged even where eventual occupancy would allow the move.
- **Cost and rejection.** Handoff coordinates two quorums and several pool owners, and temporarily holds both placements. Reject if a lost reply across membership replacement changes the receipt. Compare reservation fragmentation and peak charges on reciprocal moves with the same pins.

## B2 · Fixed regional witness and coordinated funding

- **Owner and success.** A regional witness quorum independent of the directory owns the exact append and placement decisions. Data pools attest the bytes and repair the physical copies. An outside capacity ledger atomically reserves the move's vector. An installed successor can validate retained cut and funding evidence locally.
- **Failure.** A chosen receipt survives independently of the staged rival. With the old route down, the successor can finish local activation. New writes still need the witness quorum and data path. Custodians fence all persistent scopes, including any witness records carrying data subject to erasure.
- **Cost and rejection.** Two append dependencies and a wider contention and failure domain. Isolate the witness with the current data placement still reachable. Reject if the ensuing service stall violates the product contract, or if mandatory dual-path append exceeds Q01.

## C1 · Stable groups with replica replacement

- **Owner and success.** The pooled logical quorum owns writer change, read cuts, retention, retirement and voter replacement. The worker uses existing funding and known routing. A true move prepares independent capacity, seals at the source and installs the protected exact cut at the target.
- **Failure.** A competing staged tail cannot acquire authority when a chosen reply is hidden. After one AZ loss the surviving group can replace the worker before it repairs full protection. A pinned copy withholds its original capacity; an installed target needs no old route to open.
- **Cost and rejection.** Membership transition coordinates both configuration quorums. True relocation adds source and target group coordination. Reject if a required set of cross-group moves routinely stalls despite feasible bridge headroom. Test after the last old decision and before vote repair.

## C2 · Sharded decision ledger and capacity authority

- **Owner and success.** A regional ledger owns order, scope registration and placement. It chooses over durable payload receipts. A regional capacity authority admits paired moves under a physical charge vector. Storage controllers impose terminal materialization fences and attest exact disposition.
- **Failure.** With routing and fresh allocation unavailable, a reachable ledger and protected data can reconcile the exact receipt. A paired move can use a real bridge. An old borrow withholds its charge through installation. An unreachable original custody scope holds physical erasure pending.
- **Cost and rejection.** Two dependent durability steps plus coordination for moves. Test a physical bridge with the old pin in place and the same schedule without it. Reject for excess write-path latency, broad tenant interference, or unqualified terminal storage closure.

## C3 · Replaceable authority cohorts with optional relay

- **Owner and success.** Each incarnation uses a pooled current cohort with ordinary worker replacement in place. A durability-cohort change uses an irrevocable source seal bound to one successor; the successor opens only after exact durable import. A separately funded relay can perform a second such handoff where the intermediate footprints fit.
- **Failure.** The installed successor can reopen from retained evidence. If the source is lost before the successor receives the terminal seal and import inputs, the stream waits. One successful import carries hidden chosen results and leaves staged rivals excluded. Old custody survives both hops until exact disposition.
- **Cost and rejection.** Each hop adds a pause window and overlaps protected copies. The relay adds temporary residency, recovery and erasure scope. Reject when client routing, peak occupancy or handoff pause breaches the contract; crash at each seal and import boundary.
