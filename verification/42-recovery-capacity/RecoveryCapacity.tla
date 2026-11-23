------------------------------- MODULE RecoveryCapacity -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Normal, Workspace, Envelope, Policy, Variant, Scenario
VARIABLE s

Final(phase, credit, resident) == IF phase = "installed" THEN resident ELSE credit
FinalCharge == Final(s.phase, s.credit, s.resident)
WorkCharge == s.incumbent + s.candidate + s.borrowed
ProviderUp == Scenario # "provider_down"

Init ==
    s = [phase |-> "open", ordinary |-> IF Scenario = "no_residency_room" THEN Normal ELSE 0,
         credit |-> 0, borrowed |-> 0, acceptedAtReserve |-> 0,
         accepted |-> 1, learned |-> 1, cut |-> 0, incumbent |-> 0, candidate |-> 0,
         resident |-> 0, oldPossible |-> FALSE, disposed |-> FALSE, restarted |-> FALSE,
         restartedWhileSealed |-> FALSE]

FillOrdinary ==
    /\ s.ordinary + FinalCharge < Normal
    /\ s' = [s EXCEPT !.ordinary = @ + 1]

LendWorkspace ==
    /\ Policy = "borrow" /\ s.phase = "reserved" /\ s.incumbent = 0 /\ s.borrowed = 0
    /\ s' = [s EXCEPT !.borrowed = Workspace]

Accept ==
    /\ s.phase \in {"open", "reserved"}
    /\ s.accepted < Envelope + (IF Variant = "accepted_over_envelope" THEN 1 ELSE 0)
    /\ s' = [s EXCEPT !.accepted = @ + 1]

Learn ==
    /\ s.phase \in {"open", "reserved"} /\ s.learned < s.accepted
    /\ s' = [s EXCEPT !.learned = s.accepted]

Reserve ==
    /\ s.phase = "open"
    /\ LET amount == CASE Policy = "staging_only" -> 0
                          [] Policy = "learned" -> s.learned
                          [] OTHER -> Envelope
       IN /\ s.ordinary + amount <= Normal
          /\ (IF Policy = "one_image" THEN Envelope ELSE 2 * Envelope) <= Workspace
          /\ s' = [s EXCEPT !.phase = "reserved", !.credit = amount, !.acceptedAtReserve = s.accepted]

Seal ==
    /\ s.phase = "reserved"
    /\ s' = [s EXCEPT !.phase = "sealed",
                     !.cut = IF Variant = "learned_cut" THEN s.learned ELSE s.accepted]

StageIncumbent ==
    /\ s.phase = "sealed" /\ WorkCharge + s.cut <= Workspace
    /\ s' = [s EXCEPT !.phase = "held", !.incumbent = s.cut, !.oldPossible = TRUE]

StageReplacement ==
    /\ s.phase = "held" /\ WorkCharge + s.cut <= Workspace
    /\ s' = [s EXCEPT !.phase = "ready", !.candidate = s.cut]

Activate ==
    /\ s.phase = "ready"
    /\ IF Policy = "staging_only" THEN s.ordinary + s.candidate <= Normal ELSE s.candidate <= s.credit
    /\ Variant # "charge_install_again" \/ s.ordinary + FinalCharge + s.candidate <= Normal
    /\ s' = [s EXCEPT !.phase = "installed", !.credit = 0,
                     !.resident = IF Variant = "install_wrong_cut" THEN s.candidate - 1 ELSE s.candidate,
                     !.candidate = 0,
                     !.incumbent = IF Variant = "drop_old_charge" THEN 0 ELSE @]

ObserveStableAbsence ==
    /\ ProviderUp /\ s.phase = "installed" /\ s.oldPossible
    /\ s' = [s EXCEPT !.oldPossible = FALSE, !.disposed = TRUE]

ReleaseOld ==
    /\ s.phase = "installed" /\ s.incumbent > 0
    /\ s.disposed \/ Variant = "release_on_timeout"
    /\ s' = [s EXCEPT !.incumbent = 0]

EraseIncumbentEarly ==
    /\ Variant = "erase_early" /\ s.phase \in {"held", "ready"} /\ s.oldPossible
    /\ s' = [s EXCEPT !.oldPossible = FALSE, !.disposed = TRUE]

Restart ==
    /\ ~s.restarted
    /\ s' = [s EXCEPT !.restarted = TRUE, !.credit = IF Variant = "forget_credit" THEN 0 ELSE @,
                     !.restartedWhileSealed = s.phase \in {"sealed", "held", "ready"}]

Next ==
    \/ FillOrdinary \/ LendWorkspace \/ Accept \/ Learn \/ Reserve \/ Seal \/ StageIncumbent
    \/ StageReplacement \/ Activate \/ ObserveStableAbsence \/ ReleaseOld \/ EraseIncumbentEarly \/ Restart

Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(StageIncumbent) /\ WF_s(StageReplacement) /\ WF_s(Activate)
             /\ WF_s(ObserveStableAbsence) /\ WF_s(ReleaseOld)

Bounds == s.ordinary + FinalCharge <= Normal /\ WorkCharge <= Workspace
SealProtected ==
    s.phase \in {"sealed", "held", "ready"} => s.credit >= s.cut /\ s.cut >= s.accepted
ExactInstall == s.phase = "installed" => s.resident = s.accepted
RetainsPhysicalCharge == s.oldPossible => s.incumbent > 0
AcceptedMediaStaysPinned == s.phase \in {"held", "ready"} => s.oldPossible
WaitsBeforeSeal == s.phase = "open"

SealedCompletes == (s.phase = "sealed") ~> (s.phase = "installed")
ReturnsOldWorkspace == (s.phase = "installed") ~> (s.incumbent = 0)

NeverInstallsHiddenCutAtCapacity ==
    ~(s.phase = "installed" /\ s.ordinary + s.resident = Normal /\ s.accepted > s.learned
      /\ s.accepted > s.acceptedAtReserve /\ s.incumbent > 0 /\ s.restartedWhileSealed)
NeverReleasesOldCustody ==
    ~(s.phase = "installed" /\ s.disposed /\ s.incumbent = 0)
=============================================================================
