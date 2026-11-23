-------------------------------- MODULE Residence ----------------------------
EXTENDS Naturals
CONSTANTS RefCount, Variant, Observe
VARIABLE state

Referrers == 1..RefCount
Empty == [body |-> <<0,0>>, reverse |-> FALSE, complete |-> FALSE]
NoCopy == [owner |-> 0, revision |-> 0, dest |-> 0]
NoRoot == [copy |-> NoCopy, pack |-> Empty]

Expected(revision) == <<revision + 1, revision + 4>>
Logical(pack) == IF pack.reverse THEN <<pack.body[2], pack.body[1]>> ELSE pack.body

Packed(revision, shape) ==
    LET data == Expected(revision)
    IN CASE shape = "repack" -> [body |-> <<data[2], data[1]>>, reverse |-> TRUE, complete |-> TRUE]
         [] shape = "wrong_index" -> [body |-> <<data[2], data[1]>>, reverse |-> FALSE, complete |-> TRUE]
         [] shape = "incomplete" -> [body |-> data, reverse |-> FALSE, complete |-> FALSE]
         [] shape = "wrong_bytes" -> [body |-> <<data[1], data[2] + 1>>, reverse |-> FALSE, complete |-> TRUE]
         [] OTHER -> [body |-> data, reverse |-> FALSE, complete |-> TRUE]

Init ==
    state = [revisions |-> [r \in Referrers |-> 0],
        catalog |-> [r \in Referrers |-> NoRoot], target |-> 1,
        staged |-> NoCopy, pack |-> Empty, verified |-> FALSE,
        source_present |-> TRUE, fence |-> FALSE, source_link |-> TRUE,
        old_snapshot |-> 0, old_borrow |-> 0, retired_read |-> FALSE,
        installed_offline |-> FALSE, served_alongside_old |-> FALSE, opened_after_swap |-> FALSE,
        repacked_offline |-> 0, opened_after_offline_repack |-> FALSE]

AdvanceSourceCatalog ==
    /\ state.source_link
    /\ state.source_present
    /\ state.catalog[1] = NoRoot
    /\ state.revisions[1] = 0
    /\ state' = [state EXCEPT !.revisions[1] = 1]

Prepare(referrer, shape) ==
    /\ state.source_present /\ state.source_link
    /\ state.staged = NoCopy
    /\ state.catalog[referrer] = NoRoot
    /\ state' = [state EXCEPT
        !.staged = [owner |-> referrer, revision |-> state.revisions[referrer], dest |-> state.target],
        !.pack = Packed(state.revisions[referrer], shape)]

Verify ==
    /\ state.staged # NoCopy
    /\ state.staged.dest = state.target
    /\ ~state.verified
    /\ IF Variant = "physical_equality" THEN state.pack.body = Expected(state.staged.revision)
       ELSE Logical(state.pack) = Expected(state.staged.revision) \/ Variant = "skip_bytes"
    /\ state.pack.complete \/ Variant = "skip_closure"
    /\ state' = [state EXCEPT !.verified = TRUE]

ReplaceTarget ==
    /\ state.target = 1
    /\ \A r \in Referrers : state.catalog[r] = NoRoot
    /\ state' = [state EXCEPT !.target = 2, !.pack = Empty]

LoseStaging ==
    /\ state.verified
    /\ state.pack # Empty
    /\ Variant = "reclaim_verified"
    /\ state' = [state EXCEPT !.pack = Empty]

SubstituteAfterVerify ==
    /\ state.verified
    /\ Variant = "swap_verified_version"
    /\ state' = [state EXCEPT !.pack = Packed(state.staged.revision, "wrong_index")]

Discard ==
    /\ state.staged # NoCopy
    /\ state' = [state EXCEPT !.staged = NoCopy, !.pack = Empty, !.verified = FALSE]

ExactIdentity(referrer) ==
    /\ state.staged.owner = referrer
    /\ state.staged.revision = state.revisions[referrer]
    /\ state.staged.dest = state.target

Ready(referrer) == state.catalog[referrer] = NoRoot /\ state.verified /\ ExactIdentity(referrer)

Activate(referrer) ==
    /\ state.catalog[referrer] = NoRoot
    /\ state.verified
    /\ state.staged.owner = referrer \/ Variant = "wrong_referrer"
    /\ state.staged.revision = state.revisions[referrer] \/ Variant = "stale_catalog"
    /\ state.staged.dest = state.target \/ Variant = "stale_target"
    /\ Variant # "drain_first" \/ (state.old_snapshot = 0 /\ state.old_borrow = 0)
    /\ Variant # "needs_source_link" \/ state.source_link
    /\ state' = [state EXCEPT !.catalog[referrer] = [copy |-> state.staged, pack |-> state.pack],
         !.staged = NoCopy, !.pack = Empty, !.verified = FALSE,
         !.repacked_offline = IF Observe /\ ~state.source_link /\ state.pack.reverse THEN referrer ELSE @,
         !.installed_offline = @ \/ (Observe /\ ~state.source_link)]

AdmitSourceSnapshot(referrer) ==
    /\ state.catalog[referrer] = NoRoot
    /\ state.source_present /\ state.source_link
    /\ state.old_snapshot = 0
    /\ state' = [state EXCEPT !.old_snapshot = referrer]

CloseSourceSnapshot ==
    /\ state.old_snapshot # 0
    /\ state' = [state EXCEPT !.old_snapshot = 0]

BorrowSource(referrer) ==
    /\ state.catalog[referrer] = NoRoot \/ state.old_snapshot = referrer
    /\ state.source_present /\ state.source_link
    /\ state.old_borrow = 0
    /\ state' = [state EXCEPT !.old_borrow = referrer,
        !.opened_after_swap = @ \/ (Observe /\ state.catalog[referrer] # NoRoot),
        !.opened_after_offline_repack = @ \/ (Observe /\ state.repacked_offline = referrer)]

ReadTarget(referrer) ==
    /\ state.catalog[referrer] # NoRoot
    /\ state.old_borrow = referrer /\ Observe /\ ~state.served_alongside_old
    /\ state' = [state EXCEPT !.served_alongside_old = TRUE]

FinishSource ==
    /\ state.old_borrow # 0 /\ state.source_link
    /\ state' = [state EXCEPT !.old_borrow = 0,
          !.retired_read = @ \/ (Observe /\ state.served_alongside_old)]

FenceSource ==
    /\ ~state.fence
    /\ (\A r \in Referrers : state.catalog[r] # NoRoot) \/
       (Variant = "skip_referrer" /\ (\E r \in Referrers : state.catalog[r] # NoRoot))
    /\ state.old_snapshot = 0 \/ Variant = "skip_snapshot"
    /\ state.old_borrow = 0 \/ Variant = "skip_reader"
    /\ state' = [state EXCEPT !.fence = TRUE]

EraseSource ==
    /\ state.fence /\ state.source_present /\ state.source_link
    /\ state' = [state EXCEPT !.source_present = FALSE]

ToggleSource ==
    /\ state.source_link \/ Variant # "permanent_source_loss"
    /\ state' = [state EXCEPT !.source_link = ~@]

Next ==
    \/ AdvanceSourceCatalog \/ Verify \/ ReplaceTarget \/ LoseStaging \/ SubstituteAfterVerify \/ Discard
    \/ CloseSourceSnapshot
    \/ FinishSource \/ FenceSource \/ EraseSource \/ ToggleSource
    \/ \E r \in Referrers : Activate(r) \/ AdmitSourceSnapshot(r) \/ BorrowSource(r) \/ ReadTarget(r) \/
          (\E s \in {"same", "repack", "wrong_index", "incomplete", "wrong_bytes"} : Prepare(r,s))

Spec == Init /\ [][Next]_state
FairSpec ==
    /\ Spec
    /\ \A r \in Referrers : WF_state(Activate(r))
    /\ WF_state(EraseSource)

RootInExactScope ==
    \A r \in Referrers : state.catalog[r] # NoRoot =>
      /\ state.catalog[r].copy.owner = r
      /\ state.catalog[r].copy.revision = state.revisions[r]
      /\ state.catalog[r].copy.dest = state.target

RootHasExactClosure ==
    \A r \in Referrers : state.catalog[r] # NoRoot =>
      state.catalog[r].pack.complete /\ Logical(state.catalog[r].pack) = Expected(state.revisions[r])

SourceProtection ==
    (state.old_snapshot # 0 \/ state.old_borrow # 0 \/ (\E r \in Referrers : state.catalog[r] = NoRoot)) =>
      state.source_present /\ ~state.fence

StableReadyCanInstall ==
    \A r \in Referrers :
      ((Ready(r) \/ state.catalog[r] # NoRoot) ~> (~Ready(r) \/ state.catalog[r] # NoRoot))

SettlesWithSource ==
    (<>[]state.source_link) => (state.fence ~> ~state.source_present)

SettlesWithoutSource == state.fence ~> ~state.source_present

NeverInstallsRepacked ==
    ~(\E r \in Referrers : state.catalog[r].pack.reverse)
NeverInstallsOffline == ~state.installed_offline
NeverUsesHeldSnapshotAfterSwap == ~state.opened_after_swap
NeverServesBothThenErases ==
    ~(state.served_alongside_old /\ state.retired_read /\ ~state.source_present)
NeverTransfersOfflineThenFullySettles ==
    ~(state.opened_after_offline_repack /\ ~state.source_present)
=============================================================================
