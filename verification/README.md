# Logkeeper verification

The [requirements and mechanisms](requirements.md) define what the Logkeeper design claims.
They are a draft for product review.
The [revised design](design.md) incorporates the decisions forced by the studies.
The [evidence matrix](evidence.md) distinguishes checked claims from remaining proof obligations.
The [amendment ledger](amendments.md) records what changes when a check finds a counterexample.
The [implementation gate](implementation-gate.md) tracks the design proofs and end-to-end completion evidence.
The [architecture reopening](architecture-reopening/comparison.md) compares eight independent seeds and the incumbent against common histories.

| Study | Question | Evidence |
| --- | --- | --- |
| [01 · Commit authority](01-commit/brief.md) | Can quorum-first and object-first commits provide the same ordered, fenced, durable stream? | [Bounded TLC evidence](01-commit/report.md) |
| [02 · Authority handoff](02-handoff/brief.md) | Can a move finish under directory loss without permitting a fork? | [TLC comparison and Lean theorems](02-handoff/report.md) |
| [03 · Bounded retention](03-retention/brief.md) | What can trim race with, and when does progress exceed finite storage? | [TLC races and Lean limits](03-retention/report.md) |
| [04 · Retirement](04-retirement/brief.md) | What evidence makes physical erasure stable after delayed delivery? | [TLC fault coverage and Lean proofs](04-retirement/report.md) |
| [05 · Lifecycle composition](05-lifecycle/brief.md) | Can a stale route, move, or retire race close the wrong owner? | [TLC composition results](05-lifecycle/report.md) |
| [06 · Repeated generations](06-generations/brief.md) | How can former groups refuse stale seals without retaining floors forever? | [TLC comparison and Lean nonce proofs](06-generations/report.md) |
| [07 · Logical reference machine](07-reference/brief.md) | Do append, trim, handoff, and retirement preserve the shared invariants? | [Unbounded Lean trace proofs](07-reference/report.md) |
| [08 · Replay basis](08-replay-handoff/brief.md) | Can one snapshot survive trim, expiry, and a handoff across two custody authorities? | [TLC composition results](08-replay-handoff/report.md) |
| [09 · Isolation](09-isolation/brief.md) | What can shared admission hide or guarantee? | [Lean frame and capacity proofs](09-isolation/report.md) |
| [10 · Move cancellation](10-cancel-move/brief.md) | Can an isolated target safely reclaim a destination slot? | [TLC cancellation safety and liveness](10-cancel-move/report.md) |
| [11 · Writer and placement authority](11-authority-refinement/brief.md) | Can placement move without electing a new writer, and does it refine the logical kernel? | [TLC comparison and Lean trace refinement](11-authority-refinement/report.md) |
| [12 · Journal membership](12-quorum-membership/brief.md) | Can a voter change preserve exact retained bytes and fence stale decisions? | [TLC comparison and Lean journal refinement](12-quorum-membership/report.md) |
| [13 · Durable installation](13-install-durability/brief.md) | Can target membership make an authentic staging receipt unsafe to use? | [TLC counterexamples and Lean composition](13-install-durability/report.md) |
| [14 · Physical read custody](14-read-custody/brief.md) | Can compaction, a move, or expiry reclaim bytes still borrowed by a reader? | [TLC race analysis and Lean safety](14-read-custody/report.md) |
| [15 · Replay permits](15-replay-permits/brief.md) | Can delayed or overlapping grants survive a move without reopening a closed permit? | [TLC controls and Lean composition](15-replay-permits/report.md) |
| [16 · Checkpoint reconstruction](16-checkpoint-reconstruction/brief.md) | Which published image lets a worker recover precisely the cut it captured? | [TLC controls and Lean recovery refinement](16-checkpoint-reconstruction/report.md) |
| [17 · Exact historical feed](17-exact-feed/brief.md) | If exact historical resume is required, can a reader join two sources while trim advances? | [TLC scenarios and Lean composition and limits](17-exact-feed/report.md) |
| [18 · Snapshot admission](18-snapshot-admission/brief.md) | Can checkpoint publication overtake a read before its recovery basis is protected? | [TLC safety and liveness, Lean trace proofs](18-snapshot-admission/report.md) |
| [19 · Shared object custody](19-shared-object-custody/brief.md) | Can a fork or checkpoint pin an exact physical version while its reaper is in flight? | [TLC controls and Lean graph composition](19-shared-object-custody/report.md) |
| [20 · Registration recovery](20-registration-recovery/brief.md) | Can partial registrations settle and old reference markers compact without losing custody or reopening a closed slot? | [TLC cutoff comparison and Lean recovery proofs](20-registration-recovery/report.md) |
| [21 · Custody channel lifecycle](21-custody-channel-lifecycle/brief.md) | Can a channel rotate and forget its control state while the exact grants stay live? | [TLC rollover comparison and Lean lifecycle proofs](21-custody-channel-lifecycle/report.md) |
| [22 · Residence transfer](22-residence-transfer/brief.md) | Can a checkpoint move and preserve the exact view, including for readers still pinned to the source? | [TLC transfer scenarios and Lean replay and disposal composition](22-residence-transfer/report.md) |
| [23 · Custody issuer handoff](23-custody-authority-handoff/brief.md) | Which issuer decisions must move when previously authorized grants can arrive late? | [TLC races and Lean authority and custody composition](23-custody-authority-handoff/report.md) |
| [24 · Physical custodian recovery](24-custodian-recovery/brief.md) | Can the custodian restore pins, refusal state and in-flight provider effects after a failure? | [TLC failure comparisons and Lean recovery and disposition proofs](24-custodian-recovery/report.md) |
| [25 · Journal media crash consistency](25-media-crash-consistency/brief.md) | Can a durable local vote survive base replacement while appends continue? | [TLC crash comparisons and Lean prefix and selector proofs](25-media-crash-consistency/report.md) |
| [26 · Repeated journal rotations](26-journal-rotation/brief.md) | Can recovery reopen early and reclaim unused extents without losing a crash outcome or a physical borrow? | [TLC recovery comparisons and Lean repeated-trace proofs](26-journal-rotation/report.md) |
| [27 · Fixed-group prefix consensus](27-prefix-consensus/brief.md) | How does a successor distinguish a chosen prefix from a divergent minority tail? | [TLC ballot comparisons and Lean agreement over durable replica traces](27-prefix-consensus/report.md) |
| [28 · Ordered application](28-ordered-application/brief.md) | When can choosing a command produce a successful reply or a fresh read cut? | [TLC reply races and Lean projection to the stream kernel](28-ordered-application/report.md) |
| [29 · No-marker read index](29-read-index/brief.md) | Can a fresh quorum round supply the same read guarantee as the ordered marker? | [TLC read and batch comparisons and Lean interval refinement](29-read-index/report.md) |
| [30 · Reads across voter reconfiguration](30-reconfigured-reads/brief.md) | Which quorum evidence and storage protection survive a membership change? | [TLC reconfiguration comparisons and Lean reservation composition](30-reconfigured-reads/report.md) |
| [31 · Standing snapshot custody](31-standing-custody/brief.md) | Can reads share durable custody across rotation and restart, and which retirement deadlines can a quorum guarantee? | [TLC gate and retirement comparisons and Lean read composition](31-standing-custody/report.md) |
| [32 · Configuration closure](32-configuration-closure/brief.md) | What must a new configuration inherit when old receipts are delayed or a zone fails during transfer? | [TLC closure and retry comparisons and Lean repeated-handoff proofs](32-configuration-closure/report.md) |
| [33 · Recover the activation slot](33-activation-slot/brief.md) | Can a successor recover a hidden choice and exactly its physical image with one AZ unavailable? | [TLC media and recovery comparisons and Lean exact-slot proofs](33-activation-slot/report.md) |
| [34 · Pending activation across target reconfiguration](34-pending-activation/brief.md) | Can an existing target repair membership while preserving a pending or unreported installation? | [TLC target protocol comparisons and Lean historical replay proofs](34-pending-activation/report.md) |
| [35 · Compact activation attempt fences](35-attempt-compaction/brief.md) | Can the target bound spent attempt rows while keeping live grants and cleanup? | [TLC credit comparison and Lean representation equivalence](35-attempt-compaction/report.md) |
| [36 · Retire an activation intent](36-intent-retirement/brief.md) | What can the target reclaim when copies or installation replies remain in flight? | [TLC retirement and credit comparisons and Lean trace proofs](36-intent-retirement/report.md) |
| [37 · Move the home of unresolved activation obligations](37-obligation-home/brief.md) | Can all old coordinators shut down while results or copy plans are still owed? | [TLC discovery and churn comparisons and Lean handoff and outage proofs](37-obligation-home/report.md) |
| [38 · Compose activation with its home handoff](38-activation-composition/brief.md) | Can source and custodian work finish while the target cut is staged? | [TLC overlap comparison and Lean projection to both reference traces](38-activation-composition/report.md) |
| [39 · Recover activation decisions from certified evidence](39-certified-activation-replay/brief.md) | Can a successor recover chosen effects during a counterpart outage? | [TLC replay comparison and Lean quorum, intake and custody proofs](39-certified-activation-replay/report.md) |
| [40 · Close outstanding provider writes](40-provider-io-closure/brief.md) | What excludes a write already queued at the time of erasure? | [TLC closure and capacity comparison and Lean provider disposition proofs](40-provider-io-closure/report.md) |
| [41 · Bound provider write-ticket state](41-provider-ticket-compaction/brief.md) | Can a provider forget terminal tickets and safely reuse a physical address? | [TLC compaction comparison and Lean provider refinement](41-provider-ticket-compaction/report.md) |
| [42 · Compose ranked recovery, custody, and capacity](42-recovery-capacity/brief.md) | Can a reserved handoff finish while ordinary capacity is full and its incumbent remains charged? | [TLC capacity comparison and composed Lean handoff proofs](42-recovery-capacity/report.md) |
| [43 · Reserve concurrent recovery across failure domains](43-concurrent-capacity/brief.md) | Can concurrent moves reserve and recover exact per-pool capacity? | [TLC vector reservation comparisons and Lean capacity and wait proofs](43-concurrent-capacity/report.md) |
| [44 · Make provisional capacity visible at admission](44-prepared-capacity/brief.md) | Can ordinary admission ignore a partial hold? | [Lean admission counterexample and charge conservation](44-prepared-capacity/report.md) |
| [45 · Move a capacity pool's authority](45-pool-authority/brief.md) | Can a pool change owners without losing debits or reopening canceled keys? | [TLC authority and cancellation comparisons and Lean pool-cut proofs](45-pool-authority/report.md) |
| [46 · Decide the funded seal at the source](46-funded-source-seal/brief.md) | Can a move hold both pools permanently if retirement wins before source seal? | [TLC authority comparison and Lean projection to the stream kernel](46-funded-source-seal/report.md) |
| [47 · Retain source outcomes until settlement](47-source-outcomes/brief.md) | Can an older unresolved move outlive compaction of a later exact result? | [TLC compaction comparison and Lean ranked replay](47-source-outcomes/report.md) |
| [48 · Compose source compaction with physical settlement](48-settlement-composition/brief.md) | Can the source reclaim its result slot while a provider write can still land? | [TLC physical credit comparisons and Lean source, pool, and target evidence composition](48-settlement-composition/report.md) |
| [49 · Order funded moves and settlement in one source history](49-unified-source-history/brief.md) | Can a successor recover the joint authority and result book from the chosen prefix during outage? | [TLC replay comparisons and Lean joint reducer, checkpoint, and ranked replay](49-unified-source-history/report.md) |
| [50 · Replace replay evidence with a certified continuation](50-joint-checkpoint/brief.md) | When can old proof bytes leave while a participant still needs the exact result? | [TLC checkpoint comparisons and Lean evidence, provenance, and control budget proofs](50-joint-checkpoint/report.md) |
| [51 · Authenticate the complete checkpoint envelope](51-checkpoint-envelope/brief.md) | Can the checkpoint safely reuse a data root while replacing control state and evidence? | [TLC substitution comparisons and Lean canonical codec and opening proofs](51-checkpoint-envelope/report.md) |
| [52 · Charge shared physical extents across concurrent uses](52-shared-extent-accounting/brief.md) | Can references share an existing debit without undercharging separate allocations or lingering effects? | [TLC sharing comparison and Lean physical accounting and custody refinement](52-shared-extent-accounting/report.md) |
| [53 · Separate evacuation from physical disposition](53-pool-evacuation/brief.md) | When can exact replacement coverage restore protection while the original pool remains unreachable? | [TLC physical placement comparison and Lean exact protection and debit composition](53-pool-evacuation/report.md) |
| [54 · Certify an entire recoverable cut](54-joint-recovery-protection/brief.md) | Can all crash-selectable recovery inputs and the current voter majority survive the same loss with independent placement? | [TLC placement and selector comparison and Lean joint recovery proof](54-joint-recovery-protection/report.md) |
| [55 · Bound outstanding pool incarnations](55-pool-incarnations/brief.md) | When can an unavailable scope return or release its inventory slot while repeated replacements remain bounded? | [TLC in-flight validation and settlement comparison and Lean scoped inventory and replenishment proofs](55-pool-incarnations/report.md) |
| [56 · Encode and exhaust the incarnation inventory](56-finite-inventory/brief.md) | Can checkpoint recovery and exhaustion preserve scope non-reuse within a fixed inventory byte budget? | [TLC counter and checkpoint comparison and Lean finite refinement and codec proofs](56-finite-inventory/report.md) |
| [57 · Recover the chosen incarnation state](57-ordered-inventory-recovery/brief.md) | How does a recovering authority recover an inventory decision chosen ahead of its learner or checkpoint? | [TLC issuance and recovery comparison and Lean ordered custody and ranked media proofs](57-ordered-inventory-recovery/report.md) |
| [58 · Put the guard at the storage effect boundary](58-storage-effect-boundary/brief.md) | Can a reusable physical slot reject old writes and preserve charges for staged and retained bytes? | [TLC conditional effect comparison, Lean fenced-slot proofs, and documented provider behavior](58-storage-effect-boundary/report.md) |
| [59 · Close the provisioning authority](59-namespace-closure/brief.md) | Can terminal namespace closure exclude delayed guard creates and account for all original child work? | [TLC provisioning and retirement comparison and Lean namespace and slot composition](59-namespace-closure/report.md) |
| [60 · Recover the provider's durable fence](60-durable-provisioning-root/brief.md) | Can a published retirement survive an older selected base, loss of volatile writes, and delayed old creation? | [TLC receipt and media comparison and Lean recovered root composition](60-durable-provisioning-root/report.md) |
| [61 · Compose regional retirement and shared custody](61-regional-retirement/brief.md) | Can one deployment settle custody while another keeps using shared bytes and reuses returned private capacity? | [TLC comparison and Lean regional reducer projection](61-regional-retirement/report.md) |
| [62 · Charge append capacity before ordering](62-funded-appends/brief.md) | Can the stream append from its own prepaid window and replay independently of current allocator pressure? | [TLC capacity comparison and Lean funded append projection](62-funded-appends/report.md) |
| [63 · Bind a durable vote to an isolated physical version](63-staged-votes/brief.md) | Which physical versions must coexist before vote replacement, and what authority makes each recoverable? | [TLC overwrite and headroom comparison and Lean durable acceptor refinement](63-staged-votes/report.md) |
| [64 · Replay funded commands from the exact chosen basis](64-chosen-append-recovery/brief.md) | Do both certified bases recover the exact chosen window and append decisions despite speculative physical frames? | [TLC selector comparison and Lean chosen append and envelope composition](64-chosen-append-recovery/report.md) |
| [65 · Turn an exact move reservation into funded journal service](65-funded-window-move/brief.md) | Can the target start with its original paid window while an old physical borrower remains live? | [TLC capacity comparisons and Lean exact move and shared-ledger composition](65-funded-window-move/report.md) |
| [66 · Recover an activation without restoring another authority's book](66-move-recovery/brief.md) | Can either certified source base recover the exact funded activation after independent custody and neighboring stream changes? | [TLC recovery comparison and Lean ordered activation and scoped recovery](66-move-recovery/report.md) |
| [67 · Admit from one complete current recovery scope](67-full-admission/brief.md) | Can complete fresh admission preserve the intended one-AZ degraded progress? | [TLC safety and liveness comparison and Lean scoped dependency admission](67-full-admission/report.md) |
| [68 · Consolidate the ordered stream laws and acceptance programs](68-core-reference/brief.md) | Do the chosen funded commands preserve the same kernel laws and support the required logical programs? | [Lean projection, constructive programs, and guard countermodels](68-core-reference/report.md) |
| [69 · Recover exact retained receipts across a writer move](69-retained-receipts/brief.md) | Can the successor recover the original result after the chosen frame is reclaimed? | [TLC replay comparison and Lean exact receipt and successor programs](69-retained-receipts/report.md) |
| [70 · Distributed preparation and exact ordered seal](70-distributed-preparation/brief.md) | Can separately held pool capacity drive the existing move program through coordinator loss? | [TLC interruption comparison and Lean ledger and source programs](70-distributed-preparation/report.md) |
| [71 · Late pool preparation and exact terminal closure](71-delayed-pool-prepare/brief.md) | Can a pool maintain exact closure and physical backing when preparation arrives after abort? | [TLC comparison and Lean grant, debit, and abort proofs](71-delayed-pool-prepare/report.md) |
| [72 · Pool-local physical identities and joint recovery](72-pool-local-issuance/brief.md) | Can each pool mint on arrival and keep the exact allocator, admission, and debit cut through takeover? | [TLC ordering comparisons and Lean ranked recovery](72-pool-local-issuance/report.md) |
| [73 · Exact realized source seal](73-realized-source-seal/brief.md) | Can local allocations remain exact across source recovery and activation when physical and source orders diverge? | [TLC comparisons and Lean source, ledger, and cleanup proofs](73-realized-source-seal/report.md) |
| [74 · Realized checkpoints and complete settlement](74-realized-checkpoint/brief.md) | Can one pool acknowledgment protect multiple scopes through checkpoint replacement and source compaction? | [TLC comparisons and Lean canonical body and source settlement proofs](74-realized-checkpoint/report.md) |
| [75 · Joint realized replay](75-joint-realized-replay/brief.md) | Can alternate certified bases replay one full realized source history, including early acknowledgments? | [TLC comparisons and Lean ranked source replay](75-joint-realized-replay/report.md) |
| [76 · Stable journal writer replacement](76-stable-writer-handoff/brief.md) | Can an eligible worker replace the incumbent without movement of physical custody or directory publication? | [TLC outage comparison and Lean funded worker handoff](76-stable-writer-handoff/report.md) |
| [77 · Ordered worker eligibility](77-ordered-worker-eligibility/brief.md) | Can a stable journal fence a withdrawn worker and continue to authorize exact replacements and retirement? | [TLC comparison and Lean source and replay proofs](77-ordered-worker-eligibility/report.md) |
| [78 · Sealed worker roster](78-sealed-worker-roster/brief.md) | Can an exact funded destination install local roster evidence and refuse a stale nomination after source loss? | [TLC comparisons and Lean codec, seal and replay proofs](78-sealed-worker-roster/report.md) |
| [79 · RTDB failover](79-rtdb-failover/brief.md) | Can a replacement reconcile a hidden chosen append and serve a fresh cut and append on the installed journal? | [TLC failover traces and Lean composed acceptance program](79-rtdb-failover/report.md) |
| [80 · Applied barrier receipt](80-applied-barrier-receipt/brief.md) | Can a receiver verify the exact applied marker after source loss? | [TLC issuance and delivery comparisons and Lean scoped receipt proofs](80-applied-barrier-receipt/report.md) |
| [81 · Recoverable read admission](81-recoverable-read-admission/brief.md) | Can a successor reissue a protected read before the first receipt without retaining the old suffix? | [TLC retention and failure comparisons and Lean admission proofs](81-recoverable-read-admission/report.md) |
| [82 · Joint read recovery](82-joint-read-recovery/brief.md) | Can selected checkpoint and handoff recovery bind a read result to its exact original hold? | [TLC control history comparisons and Lean combined recovery](82-joint-read-recovery/report.md) |
| [83 · Ordered read replay](83-ordered-read-replay/brief.md) | Can either base replay exact read admissions and releases through historical issuer loss? | [TLC suffix comparisons and Lean combined replay and reissue](83-ordered-read-replay/report.md) |
| [84 · Read invocation floor](84-read-invocation-floor/brief.md) | Can a journal reject a spent read after reclaiming its result with bounded control state? | [TLC nonce histories and Lean joined issuance and recovery](84-read-invocation-floor/report.md) |
| [85 · Ranked named recovery](85-ranked-named-recovery/brief.md) | Can a named checkpoint produce the exact ranked state and activate only at the current installed frontier? | [TLC recovery comparisons and Lean composed activation](85-ranked-named-recovery/report.md) |
| [86 · Atomic recovery publication](86-atomic-recovery-publication/brief.md) | Can delayed recovery overwrite an advanced local image or grant fresh use, and can admitted work finish through quorum loss? | [TLC publication races and Lean local transition and admission](86-atomic-recovery-publication/report.md) |
| [87 · Ordered reply admission](87-ordered-reply-admission/brief.md) | Can a lost original result reissue safely through close, permit reuse and authority loss? | [TLC overlap histories and Lean chosen delivery and completion](87-ordered-reply-admission/report.md) |
| [88 · Retained delivery](88-retained-delivery/brief.md) | Can a chosen delivery outlive its original read and frame with bounded evidence? | [TLC compaction histories and Lean ordered retention and named recovery](88-retained-delivery/report.md) |
| [89 · Sealed delivery handoff](89-sealed-delivery-handoff/brief.md) | Can a successor carry outstanding paid delivery through a sealed move and predecessor outage? | [TLC transfer histories and Lean exact source-to-target preservation](89-sealed-delivery-handoff/report.md) |
| [90 · Terminal delivery witness](90-terminal-delivery-witness/brief.md) | Can durable proof of an exact stop satisfy a sealed delivery obligation through target crash? | [TLC stop and reclamation histories and Lean coverage and replay preservation](90-terminal-delivery-witness/report.md) |
| [91 · Receipt selectors](91-receipt-selectors/brief.md) | Can terminal receipt evidence survive exact ranked recovery and later be collected? | [TLC crash and reclamation histories and Lean selector and ordered replay proofs](91-receipt-selectors/report.md) |
| [92 · Read contracts](92-read-contracts/brief.md) | Can latest observation avoid a journal marker while retaining exact recovery for protected reads? | [TLC read-path comparisons and Lean custody and exact recovery laws](92-read-contracts/report.md) |
| [93 · Atomic read capture](93-atomic-read-capture/brief.md) | Can a recoverable capture and first use share one decision without losing progress under checkpoint churn? | [TLC funding and churn comparison and Lean atomic capture and credit fence proofs](93-atomic-read-capture/report.md) |
| [94 · Standing read credit](94-standing-read-credit/brief.md) | Can optional atomic first use spend standing funding across rotation without old-provider coordination? | [TLC window and provider comparison and Lean bounded issuance and closure proofs](94-standing-read-credit/report.md) |
| [95 · Standing credit recovery](95-standing-read-recovery/brief.md) | Does a cursor survive checkpoint and handoff without creating an optional recovery dependency? | [TLC crash and handoff comparisons and Lean exact recovery and freshness proofs](95-standing-read-recovery/report.md) |
| [96 · Standing provider settlement](96-standing-provider-settlement/brief.md) | Can an original provider fence hidden chosen uses and refund without permanent window records? | [TLC repeated retirement comparisons and Lean exact provider and pool closure](96-standing-provider-settlement/report.md) |
| [97 · Settlement workspace](97-settlement-workspace/brief.md) | Can a ready refund run at capacity while another obligation waits for an unreachable authority? | [TLC workspace ownership comparisons and Lean exact pool refinement](97-settlement-workspace/report.md) |
| [98 · Settlement redo](98-settlement-redo/brief.md) | When does a returned charge become reusable through every crash-selectable checkpoint? | [TLC media and reserve comparisons and Lean ordered pool recovery](98-settlement-redo/report.md) |
| [99 · Degraded evidence](99-degraded-evidence/brief.md) | Can surviving replies establish physical failure as well as a ready operating scope? | [TLC policy comparisons and a Lean indistinguishability proof](99-degraded-evidence/report.md) |
| [100 · Ranked pool refund](100-ranked-pool-refund/brief.md) | Can the successor reissue the exact refund and recover a hidden charge that spent it? | [TLC failover cases and Lean quorum-to-ledger recovery](100-ranked-pool-refund/report.md) |
| [101 · Selective read window](101-selective-read-window/report.md) | Can independent reads overtake with bounded durable identity state? | [Lean exact compaction and canonical window proof](101-selective-read-window/report.md) |
| [102 · Selective ordered recovery](102-selective-ordered-recovery/brief.md) | Can the window preserve exact capture, close, delivery, and handoff under ordered recovery? | [TLC recovery comparisons and Lean combined replay, ranked handoff and packed checkpoint](102-selective-ordered-recovery/report.md) |
| [103 · Grant read policy](103-grant-read-policy/brief.md) | Can a writer replacement inherit its read policy and recover from an older checkpoint with a different width? | [TLC policy and outage comparisons and Lean exact scope recovery](103-grant-read-policy/report.md) |
| [104 · Ordered policy verifiers](104-ordered-policy-verifiers/brief.md) | Can the journal rotate a policy signer and still recover offers chosen under it? | [TLC rotation and selector comparisons and Lean signed scope and historical replay](104-ordered-policy-verifiers/report.md) |
| [105 · Service scope and protection](105-service-scope-protection/brief.md) | Can an installed journal serve while AZ loss is uncertain and preserve all acknowledged durability? | [TLC physical loss and withdrawal traces and Lean assurance preservation](105-service-scope-protection/report.md) |
| [106 · Ordered fault interval](106-ordered-fault-interval/brief.md) | Can a new majority recover the same protection interval from either checkpoint and renew during foreground traffic? | [TLC recovery and scheduling comparisons and Lean quorum and selector composition](106-ordered-fault-interval/report.md) |
| [107 · Protection handoff](107-protection-handoff/brief.md) | Can the target inherit the protection interval and safely withdraw original copies after activation? | [TLC handoff and withdrawal races and Lean activation and effect composition](107-protection-handoff/report.md) |
| [108 · Withdrawal recovery](108-withdrawal-recovery/brief.md) | Can a custodian recover pending withdrawals and exact holds while an issued deletion is in flight? | [TLC crash and effect comparisons and Lean provider and custody composition](108-withdrawal-recovery/report.md) |
| [109 · Dynamic protection](109-dynamic-protection/brief.md) | Can changing checkpoint dependencies stay protected during withdrawal, renewal and partial registration? | [TLC publication and cancellation comparisons and Lean registered coverage](109-dynamic-protection/report.md) |
| [110 · RTDB recovery closure](110-rtdb-recovery-closure/brief.md) | Can the installed journal derive the complete recovery obligation from an exact RTDB checkpoint and chosen suffix and recover its custody evidence after publisher replacement? | [TLC closure and receipt comparisons and Lean typed replay closure](110-rtdb-recovery-closure/report.md) |
| [111 · Maintenance liveness](111-maintenance-liveness/brief.md) | Can the maintenance reserve always admit checkpoint progress under repeated writer replacement? | [TLC lane comparison and Lean bound under any number of replacements](111-maintenance-liveness/report.md) |
| [112 · Erasure rotation](112-erasure-rotation/brief.md) | How does an erasure commit compose with selectable roots, the grant fence and held views? | [TLC commit comparison and Lean selectable recovery](112-erasure-rotation/report.md) |
| [113 · Worker disposal](113-worker-disposal/brief.md) | When can the journal release a withdrawn worker's holds? | [TLC disposal comparison and Lean lease margin](113-worker-disposal/report.md) |

The [contract review](architecture-reopening/contract-review.md) presents the priority changes and product decisions.
The [protocol decisions](architecture-reopening/contract-resolution.md) connect these findings to the reference and list remaining choices.
The [architecture tensions review](architecture-reopening/tensions.md) tracks structural alternatives and the guarantees that force each boundary.

This effort starts at the design-model link.
The specifications for production code, checked source, bypass audit, and composed-system tests are separate evidence links.

To reproduce all studies from the Logkeeper checkout, use Python 3.13, Java 21.0.13+9, and Lean 4.35.0.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
for study in verification/[0-9][0-9]-*/run.py; do
    python3 "$study" || exit "$?"
done
python3 verification/architecture-reopening/run.py
```

Set `LOGKEEPER_TLC_SCRATCH` to an existing directory on a volume with more free space if TLC needs it.
The runner gives each case its own Java temporary directory and state queue, then removes both and keeps the command, configuration, and log in the study’s ignored .results directory.

## Production Rust proofs

The [Verus runner](verus/README.md) verifies shipped Rust functions against
reference laws and checks that each declared production mutation fails at
its expected function. The [ordered admission area](verus/ordered_admission/README.md)
covers checked debits, trim pinning, receipt expiry and exact fingerprint
comparison.

## Consensus keeper additions

The keeper-hosted consensus streams (`src/stream/consensus/`) run OpenRaft
0.10.1, whose election, log matching and commit rules are trusted. These
checks cover what Logkeeper adds on top of Raft, each at its own level.

- **Verus, local decisions.** The [consensus admission area](verus/consensus_admission/README.md)
  verifies the shipped functions in `decisions.rs` that the keeper calls on
  its real paths: admission budgets, lanes and batch cuts, the restart vote,
  recovery admission, term and fence epoch, the excluded-sender rule, vote
  eligibility, keeper incarnations, park eligibility and the parked answer,
  silent voters, stale learners, repair order, slots and backoff, the load
  ceiling and the two-live-voters rule, leader preference, retirement on a
  proof, the seal under the recovery fence, and WAL boundary-slot selection
  and rollback detection. Each law has negative controls, production
  mutations the proof must reject.
- **Lean, abstract protocol.** [`Logkeeper.ConsensusAdditions`](lean/Logkeeper/ConsensusAdditions.lean)
  proves state-machine theorems for any number of steps:
  [operator recovery](lean/Logkeeper/ConsensusAdditions/RecoveryFence.lean),
  [parking](lean/Logkeeper/ConsensusAdditions/Parking.lean),
  [retirement on a proof](lean/Logkeeper/ConsensusAdditions/RetireOnProof.lean)
  the [catalog's first claim](lean/Logkeeper/ConsensusAdditions/CatalogClaim.lean),
  [epoch leases](lean/Logkeeper/ConsensusAdditions/EpochLease.lean),
  [the offload prefix](lean/Logkeeper/ConsensusAdditions/OffloadPrefix.lean),
  [WAL crash consistency](lean/Logkeeper/ConsensusAdditions/SegmentedWAL.lean),
  [the journal contract](lean/Logkeeper/ConsensusAdditions/JournalContract.lean)
  and [RTDB's resume after a recovery](lean/Logkeeper/ConsensusAdditions/RTDBRecovery.lean).
  Run `python3 run_consensus_additions.py` in `verification/lean` for the
  theorems, their axioms and 27 negative controls.
- **TLA+, bounded model checking.** `verification/tla/LogkeeperProtocol.tla`
  and `CatalogStream.tla`, checked exhaustively by TLC within small bounds
  (3 to 5 keepers, terms up to 3, logs up to 8 entries).
  `verification/tla/check.sh` runs every configuration with a pinned TLC
  and exits non-zero on any unexpected outcome; `check.sh fast` skips the
  five deep ones. Its README lists the configurations, the four
  counterexamples the model found and their fixes, whose Rust reproductions
  run in `src/stream/consensus/keeper/tests/model_counterexamples.rs`.
- **The fault harness, randomized execution.** The Antigravity branch
  `fault-harness` adds `src/stream/consensus/simulation/`: seeded faults
  against seven in-process keepers, with linearizability, durability,
  fencing and cross-voter convergence checked on each history.
- **TLA+, trace validation.** The [keeper trace replay](tla/TRACE.md) uses the
  harness to observe the real WAL, state machine and catalog authority. TLC
  checks the observed vote, append, commit, snapshot, park, lease, recovery,
  fence and offload transitions against a projection of the consensus models.

| Property | Verus (local) | Lean (abstract) | TLA+ (bounded) | Fault harness |
| --- | --- | --- | --- | --- |
| Admission budgets, lanes, batch cuts, restart vote | `consensus_admission` | `LeaderJournal.PeerBudget`, `Headroom`, `RestartRead` | Not modeled | Not targeted |
| Recovery admission, term `T' = max + 2^32`, fence epoch | `allows_recovery`, `recovery_term`, `recovery_epoch` | `recovery_term_outranks` | `OperatorRecoverFrom` | `recover-stream` plans |
| Excluded senders keep lost voters below `T'` | `excludes_sender` | `lost_replicas_stay_below_the_recovery_term`, `survivor_excludes_lost_voters` | `RecoverySingleReturn*` | Recovery plans |
| No reader mixes the lost suffix with the recovered log | Not local | `barrier_reads_never_mix`, `recovered_replicas_never_mix` (one returning voter, reads behind a quorum barrier) | `NoMixedHistory` in `RecoverySingleReturn*` and `RecoveryBothReturn` (CE-3 and CE-4 fixed) | Linearizability before recovery |
| Both lost voters return: placement certification fences them | `fences_copy` | `two_returning_voters_serve_the_lost_suffix` (witness without certification) | `RecoveryBothReturn`, `RecoveryBothReturnLiveness` (CE-4 fixed) | Not covered |
| A returning voter's local read needs a certified copy | `serves_reads` | `unconfirmed_local_read_serves_the_lost_suffix` (witness without certification) | `RecoverySingleReturnSnap` (CE-3 fixed) | Not covered |
| Recovery fence refuses seals until acknowledged | `seal_step` | `fence_refuses_every_seal` | Recovery fence and `AcknowledgeRecovery` | Writer fencing invariant |
| Park eligibility and the parked answer | `accepts_park`, `idle`, `leader_parks`, `parked_answer` | `accept_requires_exact_log`, `parked_answers_preserve_state` | `RaftParkSafety` | Park and wake plans |
| Parking and unparking preserve the committed log | Not local | `parking_preserves_durable_state`, `parking_preserves_the_committed_log` | `CommittedEntriesPreserved` | Durability invariant |
| Retirement never removes a copy a quorum needs | `orphaned`, `certifies_exclusion` | `retirement_keeps_every_quorum`, `retirement_refuses_a_restaged_copy` | `RetiredNeverVotes`, `RepairReplaceSafety` | Replace plans |
| Repair queue order, slots, backoff, silent voters, stale learners | `repair_key`, `starts_repair`, `backoff`, `silent`, `learner_stale` | Not modeled | `ParkedRepairLiveness`, `AbortedReplaceLiveness` and `AbortedJointRestageSafety` (CE-2 fixed, `restages_replacement`) | Repair under faults |
| Placement load ceiling, live quorum, replication factor and domain spread, leader preference | `load_ceiling`, `roomy`, `repair_allowed`, `replication_factor`, `quorum`, `spread_allows`, `creates_replication`, `hands_off` | `LeaderJournal.Placement` (domains) | Not modeled | `prefer_leader` plans |
| Empty voter from a reused keeper ID | `reincarnated`, `registers`, `counts_grant` | Not modeled | `AmnesiaWipe` (calibration CE-1, passes since 6d75fec) | `allow_wipe` mode |
| Catalog first claim wins, one genesis per stream | Not local | `first_claim_wins`, `at_most_one_genesis_per_stream`, `replicas_agree`, `checkpoint_then_suffix` | `CatalogSafety` (`AtMostOneGenesisPerStream`) | Replicated catalog outages |
| WAL boundary slot and rollback detection | `newest_slot`, `checkpoint_within`, `replay_step` | Studies 25 and 26 (`SelectionFence`), `crash_replays_whole_published_rounds`, `rollback_rejected` | Not modeled | WAL crash cuts |
| Durable commit index (`Record::Committed`, LKRWAL06) | Not local | `commit_index_follows_its_round`, `crash_replays_a_sound_commit_index` | Not modeled | Not targeted |
| An ambiguous retry is never refused definitely, across a recovery too | Not local | `committed_attempt_retry_is_indefinite` (with the recovery check the keeper lacks: `keeper_lookup_refuses_an_erased_attempt`) | Not modeled | Lost replies (`bugs.rs`); ignored repro in `keeper/tests/authority.rs` |
| An RTDB follower never resumes across an unseen recovery | Not local | `recheck_keeps_the_applied_prefix`, `follower_never_resumes_across_an_unseen_recovery` | Not modeled | Not targeted |

The Lean recovery theorem is exact about its scope. While at most one lost
voter runs, a read or commit that a quorum of the serving replica's
configuration confirmed never observes the lost suffix, on any interleaving
of lost and recovered work, provided the lost voters run fewer than `2^32`
elections past the survivor's highest term and a recovered leader holds the
committed recovery entries (Raft's leader completeness). Two returning lost
voters form a quorum of the old configuration and, without placement certification, serve the lost suffix
until one of them contacts a recovered voter. A single returning voter
cannot commit or pass a barrier, but without certification a read it
answers from its own applied state can serve the lost suffix (TLA+ CE-3).
The keeper closes both for lost voters that restart: an uncertified copy
neither campaigns nor serves, and the catalog's record of the recovery
fences the lost configuration (`keeper/certify.rs`, TLA+ `RecoveryBothReturn`).
Lost voters that kept running through the recovery remain a residual risk.
The Lean model refuses every message a lost voter sends the survivor, and
so does the keeper: every peer frame that carries the sender's vote
(append, vote, pre-vote, snapshot chunk, leadership hand-off and park) goes
through `decisions::excludes_sender` in `keeper/ingress.rs`. Snapshot chunks
and hand-offs used to be answered with the survivor's vote, at the recovery
term; `the_survivor_refuses_a_lost_voters_snapshot_without_its_term` in
`src/stream/consensus/keeper/tests/recovery.rs` checks the refusal.
