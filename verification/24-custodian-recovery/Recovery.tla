------------------------------- MODULE Recovery -------------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS MaxNonce, Variant, Observe
VARIABLE state

Old == {1, 2, 3}
New == {2, 3, 4}
Replicas == Old \cup New
Zone(replica) == IF replica = 4 THEN 1 ELSE replica
Quorum(votes, members) == Cardinality(votes \cap members) >= 2
Alive == {r \in Replicas : Zone(r) # state.lost_zone}
Available == Quorum(Alive, state.members)
Ready == state.online /\ Available

InitialView == [issued |-> 1, active |-> 1, floor |-> 0, spent |-> FALSE,
    grant |-> FALSE, borrow |-> FALSE, gate |-> "open"]

Init ==
    state = [view |-> InitialView, members |-> Old, copies |-> {1, 2},
        lost_zone |-> 0, online |-> TRUE, crashed |-> FALSE, recovered |-> FALSE,
        provider |-> TRUE, prepare |-> FALSE, cancel |-> FALSE, settled |-> FALSE,
        ref_outstanding |-> FALSE, io_outstanding |-> FALSE, retired |-> {},
        delete_packet |-> FALSE, physical |-> TRUE, old_fenced |-> FALSE,
        stale_acted |-> FALSE, refused_after_recovery |-> FALSE,
        fence_before_crash |-> FALSE, deleted_while_down |-> FALSE, resumed_with_pin |-> FALSE,
        compacted_before_crash |-> FALSE, protected_at_replacement |-> FALSE]

Commit(view, votes) == [state EXCEPT !.view = view, !.copies = votes]
Writable(votes) == Ready /\ votes \subseteq (Alive \cap state.members) /\ Quorum(votes, state.members)

QueueOldAcquire ==
    /\ state.view.active = 1
    /\ ~state.prepare /\ ~state.cancel /\ ~state.settled
    /\ state' = [state EXCEPT !.prepare = TRUE]

ReceiveAcquire(votes) ==
    /\ Writable(votes) /\ state.prepare
    /\ LET admits == state.view.active = 1 /\ state.view.floor = 0 /\ ~state.view.spent /\
                      state.view.gate = "open"
           advanced == IF admits THEN Commit([state.view EXCEPT !.grant = TRUE], votes) ELSE state
       IN state' = [advanced EXCEPT !.prepare = FALSE, !.ref_outstanding = @ \/ admits,
          !.refused_after_recovery = @ \/
            (Observe /\ state.recovered /\ state.compacted_before_crash /\
              state.settled /\ state.view.floor = 1 /\ ~admits)]

CancelIntent ==
    /\ ~state.cancel /\ ~state.settled
    /\ state.prepare \/ state.view.grant
    /\ state' = [state EXCEPT !.cancel = TRUE]

Release(votes) ==
    /\ Writable(votes) /\ state.cancel /\ ~state.settled
    /\ LET marks == state.view.active = 1 /\ state.view.floor = 0 /\
                   (state.view.grant \/ Variant # "release_absence_without_fence")
           advanced == Commit([state.view EXCEPT !.grant = FALSE, !.spent = @ \/ marks], votes)
       IN state' = [advanced EXCEPT !.settled = TRUE, !.ref_outstanding = FALSE]

Compact(votes) ==
    /\ Writable(votes) /\ state.view.active = 1 /\ state.settled /\ state.view.floor = 0
    /\ state' = Commit([state.view EXCEPT !.floor = 1, !.spent = FALSE], votes)

Retire(votes) ==
    /\ Writable(votes) /\ state.view.active # 0
    /\ LET advanced == Commit([state.view EXCEPT !.active = 0, !.floor = 0, !.spent = FALSE], votes)
       IN state' = [advanced EXCEPT !.retired = @ \cup {state.view.active}]

Mint(votes) ==
    /\ Writable(votes) /\ state.view.active = 0 /\ state.view.issued < MaxNonce
    /\ state' = Commit([state.view EXCEPT !.issued = @ + 1, !.active = state.view.issued + 1], votes)

Borrow(votes) ==
    /\ Writable(votes) /\ state.view.grant /\ state.view.gate = "open" /\ ~state.view.borrow
    /\ state' = [Commit([state.view EXCEPT !.borrow = TRUE], votes) EXCEPT !.io_outstanding = TRUE]

Finish(votes) ==
    /\ Writable(votes) /\ state.provider /\ state.view.borrow
    /\ state' = [Commit([state.view EXCEPT !.borrow = FALSE], votes) EXCEPT !.io_outstanding = FALSE]

Fence(votes) ==
    /\ Writable(votes) /\ state.view.gate = "open"
    /\ ~state.view.grant /\ ~state.view.borrow
    /\ state' = Commit([state.view EXCEPT !.gate = "deleting"], votes)

Dispatch ==
    /\ Ready /\ ~state.delete_packet /\ state.physical
    /\ state.view.gate = "deleting" \/ Variant = "early_provider_effect"
    /\ state' = [state EXCEPT !.delete_packet = TRUE]

DeliverErase ==
    /\ state.delete_packet /\ state.provider /\ state.physical
    /\ state' = [state EXCEPT !.physical = FALSE, !.deleted_while_down = Observe /\ ~state.online]

Attest(votes) ==
    /\ Writable(votes) /\ state.view.gate = "deleting" /\ ~state.physical
    /\ state' = [Commit([state.view EXCEPT !.gate = "gone"], votes) EXCEPT !.delete_packet = FALSE]

Copy(replica) ==
    /\ Ready /\ replica \in Alive \ state.copies /\ (state.copies \cap Alive \cap state.members) # {}
    /\ state' = [state EXCEPT !.copies = @ \cup {replica}]

ReplaceMembership ==
    /\ Ready /\ state.members = Old
    /\ Quorum(state.copies, New) \/ Variant = "switch_without_copy"
    /\ state' = [state EXCEPT !.members = New, !.old_fenced = (Variant # "switch_without_fence"),
        !.protected_at_replacement = Observe /\ state.lost_zone # 0 /\ state.view.grant /\ state.view.borrow]

StaleDecision ==
    /\ state.members = New /\ ~state.old_fenced /\ Quorum(Alive, Old)
    /\ state' = [state EXCEPT !.stale_acted = TRUE]

Lose(zone) ==
    /\ state.lost_zone = 0
    /\ state' = [state EXCEPT !.lost_zone = zone]

Crash ==
    /\ state.online /\ ~state.crashed
    /\ state' = [state EXCEPT !.online = FALSE, !.crashed = TRUE,
        !.compacted_before_crash = Observe /\ state.settled /\ state.view.floor = 1,
        !.fence_before_crash = Observe /\ state.view.gate = "deleting" /\ state.delete_packet]

Restore(view) ==
    CASE Variant = "forget_grant" -> [view EXCEPT !.grant = FALSE]
      [] Variant = "forget_borrow" -> [view EXCEPT !.borrow = FALSE]
      [] Variant = "forget_issuance" /\ view.active = 0 -> [view EXCEPT !.issued = 0]
      [] Variant = "forget_spent" -> [view EXCEPT !.spent = FALSE]
      [] Variant = "forget_floor" -> [view EXCEPT !.floor = 0]
      [] Variant = "forget_delete_fence" -> [view EXCEPT !.gate = "open"]
      [] OTHER -> view

Recover ==
    /\ ~state.online /\ Available
    /\ (state.copies \cap Alive \cap state.members) # {}
    /\ state' = [state EXCEPT !.online = TRUE, !.view = Restore(state.view), !.recovered = TRUE,
        !.resumed_with_pin = Observe /\ state.protected_at_replacement /\
          state.view.grant /\ state.view.borrow /\ state.members = New]

ToggleProvider ==
    /\ state.provider \/ Variant # "permanent_provider_loss"
    /\ state' = [state EXCEPT !.provider = ~@]

Next ==
    \/ QueueOldAcquire \/ CancelIntent \/ Dispatch \/ DeliverErase
    \/ ReplaceMembership \/ StaleDecision \/ Crash \/ Recover \/ ToggleProvider
    \/ \E replica \in Replicas : Copy(replica)
    \/ \E zone \in 1..3 : Lose(zone)
    \/ \E votes \in SUBSET Replicas : ReceiveAcquire(votes) \/ Release(votes) \/ Compact(votes) \/
          Retire(votes) \/ Mint(votes) \/ Borrow(votes) \/ Finish(votes) \/ Fence(votes) \/ Attest(votes)

Spec == Init /\ [][Next]_state
FairSpec ==
    /\ Spec /\ WF_state(Recover) /\ WF_state(Dispatch) /\ WF_state(DeliverErase)
    /\ WF_state(\E votes \in SUBSET Replicas : Attest(votes))

ExactImageCovered == Quorum(state.copies, state.members)
RetiredHandleCannotReopen == state.view.active \notin state.retired
AcknowledgedGrantRemains == state.ref_outstanding => state.view.grant
AdmittedBorrowRemains == state.io_outstanding => state.view.borrow
SettledCannotReacquire == state.settled => ~state.view.grant
EffectsHaveCommittedFence == state.delete_packet => state.view.gate = "deleting"
PinnedBytesRemain == (state.ref_outstanding \/ state.io_outstanding) => state.physical
NoStaleConfigurationDecision == ~state.stale_acted

RestartsWithQuorum == (<>[]Available) => ((~state.online) ~> state.online)
DisposalSettlesWithAccess ==
    (<>[](state.provider /\ Available)) => ((state.view.gate = "deleting") ~> (state.view.gate = "gone"))
DisposalSettlesWithoutProvider ==
    (<>[]Available) => ((state.view.gate = "deleting") ~> (state.view.gate = "gone"))

NeverRefusesAfterRecovery == ~state.refused_after_recovery
NeverSettlesPreCrashDisposal ==
    ~(state.fence_before_crash /\ state.deleted_while_down /\ state.recovered /\ state.view.gate = "gone")
NeverRecoversLivePinAfterReplacement == ~state.resumed_with_pin
=============================================================================
