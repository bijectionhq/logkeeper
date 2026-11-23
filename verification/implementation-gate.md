# Logkeeper design and implementation gate

2026-11-23

End-to-end implementation follows the verified design.
The design still needs the proofs below.
The [requirements](requirements.md) define the baseline, and the [evidence matrix](evidence.md) records the strength of each study.

## What the design must establish

| Design claim | Evidence required by the verification method | Current state |
| --- | --- | --- |
| Validity | Each safety and resource law holds in a common reference machine or through a proved refinement into it. Each liveness law says exactly which environment and fairness it uses. | The regional reducer composes exact borrows, append windows, and the prepared move vector against one pool ledger. The recovered source admission checks all selectable dependencies and separates current serving readiness from the protection interval. The remaining work includes discharging the exact codec, custody, fault interval, and certificate premises and consolidating the linked reducers and liveness conditions. |
| Expressiveness | The acceptance programs run in the same reference with their expected outputs and refusals. | The funded chosen reducer executes the logical writer, fence, replay, trim and retirement programs. The full suite still needs its distributed end-to-end cases in the common reference. |
| Independence | Every proposed mechanism has a weakening that preserves the other mechanisms and breaks a named requirement or acceptance program. | Five one-guard countermodels are checked in the common logical stream state space, covering parts of M02, M05 and M08. Independence of the full mechanism list and redundant enforcement across layers still need analysis. |
| Coherent fault and capacity contracts | Provider, quorum, routing, and RTDB assumptions are explicit and their composition preserves the checked laws. | A one-AZ fault envelope, finite recovery and custody budgets, and conditional progress are explicit. Exact media and provider durability, transfer and repair reservations, and usage across multiple streams still need composition. |

The baseline uses bounded per-stream recovery, ordered-command read cuts, and deployment-scoped erasure.
The baseline uses checkpoint-based watch restart after retention, invocation-scoped retirement, and a single protected AZ-loss interval until repair.
The design defines distinct contracts for an exact historical feed, a physical batch frontier, stronger overlapping-read exclusion, and larger fault envelopes.
Integration must move same-placement writer grants and exact checkpoint publication from RTDB Multi's current directory-dependent path into the installed journal.
Each stronger product contract needs its own requirements and verification.
The [architecture reopening](architecture-reopening/comparison.md) selects stable logical group ownership and keeps a separate regional decision quorum outside funded installed-group service.
Coordinated capacity is an alternative for true physical moves only.
The bounded comparisons isolate the dependencies in P142 and funded activation.
[Study 79](79-rtdb-failover/report.md) executes P142 in the reference under exact local certificate, custody, headroom and route premises.
It checks the one-AZ histories and distinguishes matching an invocation identity from keeping that identity fresh.
Study 77 models the ordered roster and the committed fence for effective withdrawal.
[Study 80](80-applied-barrier-receipt/report.md) refines the read result into canonical bytes and a scoped issuer that requires a successful chosen application.
[Study 81](81-recoverable-read-admission/report.md) couples the successful marker with protected admission and checks reissue after source loss before the first permit or receipt.
P142 qualification still needs authentic routing, actual nomination and packet verification, physical recovery, and RTDB snapshot materialization.
Study 78 gives the roster a canonical bounded codec and checks its attachment to the actual sealed transfer and named recovery image.
Exact provider import attestations, the complete control-image and frame encoding, and physical replica coverage remain to be refined.

## End-to-end completion evidence

1. Implement the reference decisions and their durability and transport boundaries in the standalone Logkeeper repository.
2. Connect RTDB Multi's log service to the resulting client and provider interfaces, including activation, failover, checkpoint replay, retention, and retirement.
3. Verify the call paths that confer authority, persist command and effect evidence, and reclaim storage. Compare recorded running histories against the models under faults.
4. Run the RTDB Multi acceptance paths and standalone RTDB compatibility checks. Qualify latency, recovery time, and repair against the workload budgets in Q01.

These steps provide the completion evidence from running code.
RTDB's `LogService` contract in `allium/rtdb-multi.allium` covers epoch and position checks, distinct durable journals, and standalone process-bound transport.

## Installed Logkeeper boundaries

The [C9 evidence](evidence.md#c9-installed-boundaries) records the application frame and signer checks, the ordered voter recovery barriers, and the remaining provider and physical volume contracts.
The remaining deployment qualification includes trustworthy manifest distribution, real failure-domain placement, and power-loss trials on the installed storage stack.
Exact provider disposition and aggregate physical capacity require evidence from the provisioned providers and volumes.

## Current composition

[Study 42](42-recovery-capacity/report.md) checks one full-pool handoff in a shared reference with ranked quorum recovery, exact stream replay, physical custody, and numeric residency and workspace.
[Study 43](43-concurrent-capacity/report.md) composes that handoff with pointwise numeric accounting and separately checks atomic and ordered partial preparation.
[Study 44](44-prepared-capacity/report.md) proves that ordinary admission must see provisional debits under exact capacity checks and that converting a full held vector to a commitment preserves every pool's usage.
[Study 45](45-pool-authority/report.md) checks local pool takeover, including numeric charges, compact cancellation fences, and guarded planned contraction.
[Study 46](46-funded-source-seal/report.md) checks the exact full-vector commitment at the ordered source seal and its competition with abort and retirement, including two moving pools.
[Study 47](47-source-outcomes/report.md) checks sparse compaction of fully settled source outcomes, retention of older unresolved evidence, and replay of the chosen book across ranked recovery.
[Study 48](48-settlement-composition/report.md) connects funded source outcomes and physical settlement evidence to reserved result recording, acknowledgment, and compaction.
[Study 49](49-unified-source-history/report.md) checks ranked replay of one ordered source reducer, including lifecycle decisions, effect evidence, source result intake and compaction.
[Study 50](50-joint-checkpoint/report.md) checks evidence reclamation across selectable checkpoints, current-state attestations, and a byte bound for the encoded control books under explicit field ceilings.
[Study 51](51-checkpoint-envelope/report.md) checks canonical checkpoint framing, exact binding of the three immutable components, and joint replay after verified opening.
[Study 52](52-shared-extent-accounting/report.md) composes pointwise debits for exact physical allocations with concurrent manifest registration, provider effects, and independent borrows.
[Study 53](53-pool-evacuation/report.md) checks exact fault-domain coverage and independently funded physical replacement while the original borrow and debit stay in scope.
[Study 54](54-joint-recovery-protection/report.md) joins every selectable checkpoint dependency and suffix with ranked recovery in the current voter family for the same AZ fault.
[Study 55](55-pool-incarnations/report.md) bounds unsettled physical incarnations, checks exact return validation, and proves slot replenishment is necessary for continued registration at fixed capacity.
[Study 56](56-finite-inventory/report.md) checks finite issuer and epoch exhaustion, exact ordered recovery, and a canonical incarnation inventory byte bound for both selectable bodies.
[Study 57](57-ordered-inventory-recovery/report.md) proves the ordered incarnation reducer refines finite custody and recovers unlearned choices through the current ranked cutoff and either selectable journal base.
[Study 58](58-storage-effect-boundary/report.md) refines atomic payload effects to a live scoped guard and separates current-slot clearance from exact staging and retained-version disposition.
[Study 59](59-namespace-closure/report.md) composes the scoped provisioning root, child guards, auxiliary disposition, and the incarnation registry's terminal rule.
[Study 60](60-durable-provisioning-root/report.md) composes the provider root's ordered decisions with exact media durability, applied receipts, and recovery through either crash-selectable base.
[Study 61](61-regional-retirement/report.md) joins ordered stream retirement with the shared pool ledger, binding each regional borrow and release to the exact read and proving preservation of both reducers' bounds across finite traces.
[Study 62](62-funded-appends/report.md) couples every successful append to an exact charged window, proves non-reuse of spent ranges, and projects the resulting machine onto the regional reducer.
[Study 63](63-staged-votes/report.md) composes independent candidate versions with the durable acceptor and pointwise charged pool ledger. It proves exact local recovery and the summed capacity bound for coexisting versions.
[Study 64](64-chosen-append-recovery/report.md) connects ranked durable frame decisions to the exact funded append path. Either certified selectable checkpoint reproduces the original source and window state and the original outcomes in its retained suffix.
[Study 65](65-funded-window-move/report.md) connects the prepared vector to the exact source seal and funded destination window in the shared pool ledger. Installation keeps pointwise occupancy and the predecessor borrow's original debit unchanged.
[Study 66](66-move-recovery/report.md) replays the combined activation through either certified source base and merges only its scope. The model preserves independently settled pool claims and existing neighbor cursors and checks current custody at fresh admission.
[Study 67](67-full-admission/report.md) links fresh admission to the full recovered scope and current quorum and immutable input support. The stable-outage model shows why a one-AZ envelope must preserve its remaining allowance while degraded.
[Study 68](68-core-reference/report.md) projects every funded chosen command to the original logical kernel and checks the writer and replay programs with five constructive weakening cases.
[Study 69](69-retained-receipts/report.md) carries exact lost append results through either certified receipt basis and the exact funded activation. The receipt predicate checks the retained committed range and does not append.
[Study 70](70-distributed-preparation/report.md) derives the exact source seal from paid allocations and their certified local receipts, then executes the funded successor and retained result program.
It also checks abort racing delayed preparation under finite fairness.
[Study 71](71-delayed-pool-prepare/report.md) constructs delayed preparation from the existing gate and exact ledger transitions and applies the exact chosen cancel or retirement to its original pool.
Its general proof preserves the fence and physical charges across custody and provider steps.
The installed pool image still needs to join both projected states across actual ranked recovery with independently minted physical scope identities.
[Study 72](72-pool-local-issuance/report.md) proves pool-local minting, exact scope accounting and ranked preservation of the joint pool image through repeated takeover.
It replaces preassigned physical versions in plans with receipt-bound realization.
Concrete ranked media coverage remains an implementation boundary.
[Study 73](73-realized-source-seal/report.md) binds the exact authorized plan and pool-issued vector to the order of the actual source seal and activation.
It proves that the physical append extent can have a lower serial while the ordered source window advances, and that cleanup refunds only its verified recovery row.
[Study 74](74-realized-checkpoint/report.md) checks the bounded canonical seal body and opens it by exact source slot through the existing authenticated control envelope.
Its ordered source settlement proof requires coverage of all original scopes at each pool and keeps the serving window independent of result compaction.
[Study 75](75-joint-realized-replay/report.md) composes the original reducers in one augmented source image and proves equality of exact replay from alternate certified bases.
The source protects still-pending activation from early result compaction even after every participant acknowledges.
Ranked media and remaining canonical typed frame encoding, concrete certification, and fresh physical admission still require refinement.
[Study 76](76-stable-writer-handoff/report.md) separates worker replacement from physical migration in the augmented source reducer.
It proves exact reuse of the existing paid range and validates the scoped nomination and checkpoint evidence gates.
The RTDB Multi authority transfer, direct certified route and checkpoint publication during directory loss still need a joint proof and deployment qualification.
[Study 77](77-ordered-worker-eligibility/report.md) adds the exact roster and issuance watermark to the chosen source and ranked recovery image.
It proves joint withdrawal and grant fencing, matching by current enrollment, and authenticated retirement of a vacancy.
[Study 78](78-sealed-worker-roster/report.md) binds the canonical roster and watermark to the chosen seal and requires the target install predicate to cover the same retained body.
It checks the stale-roster and rolled-back-watermark failures under equal data frontiers.
The actual eligibility and import attestations and the complete transfer encoding still need refinement. The installed application framing and its transport trust boundary are recorded under C9.
[Study 79](79-rtdb-failover/report.md) composes ranked reopen, exact retry, same-placement grant, fresh marker and prepaid append.
The composed program runs under the stated authenticity, eligibility, custody and headroom premises.
The bounded cases exercise all three single-AZ faults and preserve refusal when exact coverage is missing.
[Study 80](80-applied-barrier-receipt/report.md) proves that a positive marker receipt names its actual chosen successful result, and that an issued reply can complete locally under scoped authentication and protected materialization.
The installed signer and retained-key policy are recorded under C9. The protected RTDB materialization and deployment trust qualification remain open.
[Study 81](81-recoverable-read-admission/report.md) proves exact reissue by authenticated invocation from the recovered bounded admission row and its paired hold.
[Study 82](82-joint-read-recovery/report.md) checks the combined named read section, its ordered checkpoint and seal selection, original dependency coverage and target reissue.
Refine the actual certifying source projection and the complete combined wire body, key and custody adapters, and physical endpoint stop.
[Study 83](83-ordered-read-replay/report.md) composes the read book with ranked source replay and proves result provenance under one exact chosen suffix.
Historical evidence remains verifiable through issuer loss, and serving checks current authority and protected dependencies separately.
Refine full protected operation framing and the exact journal-to-snapshot root projection.
[Study 84](84-read-invocation-floor/report.md) carries a one-word consumed nonce floor in that ranked machine and opens its exact value from the authenticated checkpoint control.
Refine external nonce assignment, lost-reply reconciliation, and authenticated abandonment and writer fencing at the RTDB integration boundary.
[Study 85](85-ranked-named-recovery/report.md) composes the typed named base with fenced capture and the exact ordered replay, then requires the existing single-choice installation slot and the current lineage, revision and command frontier.
Refine compact authenticated issuance and cutoff names and exact target backing.
[Study 86](86-atomic-recovery-publication/report.md) composes exact ranked preparation with an atomic local compare-and-attach. It verifies monotone live replay and separates current authorization for fresh use from completion under an independent exact borrow.
Refine the actual local serialization and process identity, operation-side authority, provider reservation and stop, and signer and transport boundaries.
[Study 87](87-ordered-reply-admission/report.md) instantiates reissue authority with one exact chosen and applied control frame. It checks the original paid permit and basis in the same order as close and produces the protected completion token.
Refine canonical framing and durable evidence retention for unfinished chosen delivery, exact physical payment and stop, and settlement of unused preparations.
[Study 88](88-retained-delivery/report.md) puts the bounded delivery book inside the ordered state and named checkpoint, and verifies original-use completion and exact settlement through independent custody.
Refine whole-control encoding, authenticated issuance and provider settlement, and the full staging budget.
[Study 89](89-sealed-delivery-handoff/report.md) verifies exact combined seal admission and local activation carrying the same delivery book, non-reuse floor and original physical custody after source loss.
Bind the combined admission to the chosen frame and ranked replay, and refine independently mounted catalogs.
[Study 90](90-terminal-delivery-witness/report.md) compares original media retention with exact locally durable terminal evidence for exclusive delivery dependencies.
Refine canonical receipt verification and the provider effect and compaction boundary.
[Study 91](91-receipt-selectors/report.md) composes exact named receipt readiness with local journal rotation, both crash roots, inline settlement and chosen suffix replay.
Bind the complete receipt plan to the real authenticated checkpoint and selector, and discharge stable naming and bounded pin accounting at the media boundary.
[Study 92](92-read-contracts/report.md) compares markerless latest observations against ordered captures and preserves explicit exact original-result recovery.
Confirm Bijection call-site retry promises and bind real current scope and the local gate.
[Study 93](93-atomic-read-capture/report.md) compares split, fixed fused, and delegated fused capture and first use.
Keep split as the reference unless delegated coverage, original provider settlement, and competing demands through window rotation and handoff refine the candidate.
[Study 94](94-standing-read-credit/report.md) derives operation identities from paid standing ranges at choice and compares old-provider loss, delayed assignments and optional funding loss.
[Study 95](95-standing-read-recovery/report.md) binds the generation, cursor and archived grant to the exact named checkpoint and source seal, and separates fresh coverage from historical replay.
[Study 96](96-standing-provider-settlement/report.md) composes exact original fence installation, positive effect admission, guarded refund and persistent refusal after collection.
Verify durable provider bookkeeping, complete guarded dispatch and aggregate staged and retained charges before selecting the candidate.
Compare both read designs under the same failure and capacity budgets before choosing fusion.
Its additional state needs to buy fewer durable decisions or faster completion on exact-recovery workloads while preserving ordinary write and checkpoint progress.
[Read architecture decision criteria](architecture-reopening/tensions.md#exact-lost-response-recovery-is-a-separate-service-from-latest-read-freshness)
[Study 97](97-settlement-workspace/report.md) checks the common settlement workspace rule under owner-local publication and stalled peers, and bounds ready-work turns under continuing admission.
Validate the physical peak through crash-selectable copies and stage reuse, and refine stable scheduling slots and cursor handling.
[Study 98](98-settlement-redo/report.md) orders exact refunds and dependent reuse in the same pool and journal state and checks every selectable recovery path.
Choose actual compact checkpoint and command formats, certify the same order at the quorum and media boundaries, and qualify the combined redo and alternate image reserve.
[Study 99](99-degraded-evidence/report.md) separates the existing physical diagnosis premise from a candidate decision to serve on a verified restricted scope.
Use a verified serving cut without attributing a physical failure to it.
[Study 105](105-service-scope-protection/report.md) preserves prior and new protection in its abstract transition system, and checks why a surviving single copy under uncertain loss is insufficient.
[Study 106](106-ordered-fault-interval/report.md) composes the carried interval with ranked voter changes and exact recovery from the current quorum's crash-selectable media.
The bounded traffic comparison exposes renewal starvation from unnecessary invalidation.
[Study 107](107-protection-handoff/report.md) composes the carried interval and the exact original promise with the existing activation fence and ordered physical withdrawals.
[Study 108](108-withdrawal-recovery/report.md) composes the original custody phase, registered holds, exact chosen recovery and provider settlement.
[Study 109](109-dynamic-protection/report.md) composes prepared exact registration, changing live roots and fault cases, and pending storage effects.
Refine canonical framing, complete real manifest dependencies, authority and original receipt binding at publication, and crash-recoverable registration and settlement across providers.
Create the authenticated effect and disposition from the actual provider and integrate terminal allocation accounting, dynamic physical provisioning and the combined regional capacity budget.
Refine a ready renewal turn that stays local while proof dependencies are held.
[Study 110](110-rtdb-recovery-closure/report.md) derives the recovery obligation from typed replay of the base and every retained frame.
It covers adopted roots, trie and artefact additions, and decoded oversized bodies, and retains the exact receipt set in the chosen publication.
Re-pin the typed projection to the counterpart RTDB revision and refine it against the production decoder and loader. Cover images cut while a block is pending.
[Study 100](100-ranked-pool-refund/report.md) ties the ranked installed basis to the locally exact pool media and preserves the hidden dependent debit.
Complete the authenticated live-cut and scope bindings, media format and provider effect refinement.
[Study 101](101-selective-read-window/report.md) verifies a canonical fixed-width admission window as the candidate for independent exact reads.
[Study 102](102-selective-ordered-recovery/report.md) integrates that window into the ordered model, packed checkpoint, both selectable paths, and ranked handoff.
[Study 103](103-grant-read-policy/report.md) binds width to the exact chosen grant and historical cut. Unchanged-width replacement can inherit the authorized width without a live policy offer.
[Study 104](104-ordered-policy-verifiers/report.md) checks the canonical signed policy body, ordered verifier rotation, and recovery using the named historical verifier.
Qualify Bijection caller contracts and refine deployed key and signature formats, signer provisioning and compromise policy, complete media framing, and the provider effect boundary.
The common reference still needs canonical control and data body encodings, authenticated identity and custody adapters, and actual allocation sizes and metadata charges.
Runtime certification needs to establish actual complete dependency enumeration and current voter and provider eligibility for the checked recovery contract.
The ordered inventory proof still needs concrete command framing and durable certificate and media bindings.
The storage adapter still needs a qualified atomic compare at the effect boundary, authenticated staging and version evidence, and actual media and authenticated frames for the checked provisioning root.
