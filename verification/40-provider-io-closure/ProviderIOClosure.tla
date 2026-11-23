----------------------------- MODULE ProviderIOClosure -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Tickets, Policy, Variant, Scenario
VARIABLE s

Ids == 1..Tickets
Issued == {id \in Ids : s.status[id] # "unused"}
ProviderUp == Scenario \notin {"provider_down", "provider_down_no_room"}
Pending == {id \in Ids : s.status[id] = "pending"}
CanStillWrite == IF s.providerClosed THEN {} ELSE Pending
AfterClose == ~s.admitOpen

Init ==
    s = [admitOpen |-> TRUE, status |-> [id \in Ids |-> "unused"],
         attempts |-> [id \in Ids |-> 0], observed |-> {},
         providerClosed |-> FALSE, observedFence |-> FALSE, present |-> FALSE,
         custodian |-> FALSE, covered |-> {}, coversBytes |-> FALSE,
         target |-> TRUE, erased |-> FALSE, restarted |-> FALSE, custodyReleased |-> FALSE,
         refusedPendingAfterErase |-> FALSE, refusedDoneAfterErase |-> FALSE]

Admit(id) ==
    /\ s.admitOpen /\ s.status[id] = "unused"
    /\ s' = [s EXCEPT !.status[id] = "pending"]

CloseAdmission ==
    /\ s.admitOpen
    /\ s' = [s EXCEPT !.admitOpen = FALSE,
                     !.observedFence = Variant = "local_close_is_fence"]

CanEnterProvider(id) ==
    /\ ~s.providerClosed \/ Variant = "check_only_at_admission"
    /\ s.status[id] = "pending" \/ (Variant = "replay_writes_again" /\ s.status[id] = "done")

Deliver(id) ==
    /\ ProviderUp /\ id \in Issued /\ s.attempts[id] < 2
    /\ Scenario # "ticket_stalled" \/ id # 1
    /\ LET applies == CanEnterProvider(id)
       IN s' = [s EXCEPT !.attempts[id] = @ + 1,
                          !.status[id] = IF applies THEN "done" ELSE @,
                          !.present = @ \/ applies,
                          !.refusedPendingAfterErase = @ \/ (s.erased /\ ~applies /\ s.status[id] = "pending"),
                          !.refusedDoneAfterErase = @ \/ (s.erased /\ ~applies /\ s.status[id] = "done")]

CloseProvider ==
    /\ ProviderUp /\ Policy = "effect_fence" /\ AfterClose /\ ~s.providerClosed
    /\ s' = [s EXCEPT !.providerClosed = TRUE]

ObserveProviderFence ==
    /\ s.providerClosed /\ ~s.observedFence
    /\ s' = [s EXCEPT !.observedFence = TRUE]

Observe(id) ==
    /\ id \in Issued /\ id \notin s.observed
    /\ s.status[id] = "done"
       \/ (Variant = "timeout_is_stop" /\ AfterClose)
       \/ (Variant = "wrong_receipt" /\ \E other \in Ids : other # id /\ s.status[other] = "done")
    /\ s' = [s EXCEPT !.observed = @ \cup {id}]

ReadyToRemove == AfterClose /\ (s.observedFence \/ Issued \subseteq s.observed)

Delete ==
    /\ ProviderUp /\ ReadyToRemove /\ s.present
    /\ s' = [s EXCEPT !.present = FALSE]

ConfirmAbsence ==
    /\ ProviderUp /\ ReadyToRemove /\ ~s.present /\ ~s.erased
    /\ s' = [s EXCEPT !.erased = TRUE]

TakeCustody ==
    /\ Policy # "erase_only" /\ AfterClose /\ ~s.custodian /\ ~s.erased
    /\ Scenario # "provider_down_no_room"
    /\ s' = [s EXCEPT !.custodian = TRUE,
                     !.covered = IF Variant = "charge_visible_only" THEN {} ELSE Issued,
                     !.coversBytes = s.present \/ Variant # "charge_visible_only"]

ReleaseTarget ==
    /\ s.target /\ (s.erased \/ s.custodian \/ (Variant = "release_before_charge" /\ AfterClose))
    /\ s' = [s EXCEPT !.target = FALSE]

ReleaseCustodian ==
    /\ s.erased /\ s.custodian
    /\ Variant # "retain_custody_forever"
    /\ s' = [s EXCEPT !.custodian = FALSE, !.coversBytes = FALSE, !.covered = {}, !.custodyReleased = TRUE]

Restart ==
    /\ ~s.restarted
    /\ s' = [s EXCEPT !.restarted = TRUE,
                     !.providerClosed = IF Variant = "lose_provider_fence" THEN FALSE ELSE @,
                     !.custodian = IF Variant = "lose_custody" THEN FALSE ELSE @,
                     !.status = IF Variant = "lose_consumption"
                                THEN [id \in Ids |-> IF s.status[id] = "done" THEN "pending" ELSE s.status[id]]
                                ELSE @]

DeliverSome == \E id \in Ids : Deliver(id)
Next ==
    \/ CloseAdmission \/ CloseProvider \/ ObserveProviderFence \/ Delete \/ ConfirmAbsence
    \/ TakeCustody \/ ReleaseTarget \/ ReleaseCustodian \/ Restart
    \/ \E id \in Ids : Admit(id) \/ Deliver(id) \/ Observe(id)

Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(CloseProvider) /\ WF_s(ObserveProviderFence) /\ WF_s(DeliverSome)
             /\ WF_s(Delete) /\ WF_s(ConfirmAbsence)
             /\ WF_s(TakeCustody) /\ WF_s(ReleaseTarget) /\ WF_s(ReleaseCustodian)
             /\ \A id \in Ids : WF_s(Observe(id))

ErasureIsStable == s.erased => AfterClose /\ ~s.present /\ CanStillWrite = {}
ErasedBytesDoNotReturn == s.erased => ~s.present
NoUnchargedPhysicalWork ==
    s.target \/ (s.custodian /\ CanStillWrite \subseteq s.covered
                 /\ ((s.present \/ CanStillWrite # {}) => s.coversBytes))
    \/ (s.erased /\ ~s.present /\ CanStillWrite = {})

ErasesAfterClose == AfterClose ~> s.erased
CanReleaseAfterClose == AfterClose ~> ~s.target
ReclaimsBothCharges == s.erased ~> (~s.target /\ ~s.custodian)

NeverRejectsPendingAfterErasure == ~s.refusedPendingAfterErase
NeverRejectsDuplicateAfterErasure == ~s.refusedDoneAfterErase
NeverReleasesWhileProviderCannotStop ==
    ~(~s.target /\ s.custodian /\ CanStillWrite # {} /\ ~s.erased)
NeverFreesBothChargesAfterCustody ==
    ~(~s.target /\ ~s.custodian /\ s.custodyReleased /\ \E id \in Ids : s.status[id] = "done")
=============================================================================
