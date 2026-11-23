------------------------------ MODULE Lifecycle ------------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS MaxLsn, Mutation
VARIABLE state

Source == 1
Target == 2
Locations == {Source, Target, 3}

Init ==
    state = [
        source_mode |-> "serving",
        target_mode |-> "inactive",
        plan |-> FALSE,
        installed |-> FALSE,
        source_end |-> 0,
        target_end |-> 0,
        cut |-> 0,
        source_custody |-> {Source},
        target_custody |-> {},
        retire_reply |-> 0,
        after_retire_append |-> FALSE,
        redirected |-> FALSE,
        resident |-> {Source},
        fenced |-> {},
        complete |-> FALSE
    ]

SourceWritable == state.source_mode = "serving"
TargetWritable == state.target_mode = "serving"
SourceSealed == state.source_mode = "sealed"
Retired == state.source_mode = "retired" \/ state.target_mode = "retired"
KnownCustody == IF state.target_mode = "retired" THEN state.target_custody
                ELSE state.source_custody

ReserveMove ==
    /\ SourceWritable
    /\ ~state.plan
    /\ state' = [state EXCEPT !.plan = TRUE, !.source_custody = @ \cup {Target}]

ReserveCopy(location) ==
    /\ SourceWritable
    /\ location \in Locations \ (state.source_custody \cup {Target})
    /\ state' = [state EXCEPT !.source_custody = @ \cup {location}]

DeliverCopy(location) ==
    /\ location \in (state.source_custody \cup state.target_custody) \ state.resident
    /\ location \notin state.fenced
    /\ state' = [state EXCEPT !.resident = @ \cup {location}]

AppendSource ==
    /\ SourceWritable
    /\ state.source_end < MaxLsn
    /\ state' = [state EXCEPT !.source_end = @ + 1,
        !.after_retire_append = @ \/ state.retire_reply # 0]

AppendTarget ==
    /\ TargetWritable
    /\ state.target_end < MaxLsn
    /\ state' = [state EXCEPT !.target_end = @ + 1,
        !.after_retire_append = @ \/ state.retire_reply # 0]

Seal ==
    /\ state.plan
    /\ ~SourceSealed
    /\ SourceWritable \/ Mutation = "seal_after_retire"
    /\ state' = [state EXCEPT !.source_mode = "sealed", !.cut = state.source_end]

Install ==
    /\ SourceSealed
    /\ ~state.installed
    /\ state' = [state EXCEPT
        !.installed = TRUE, !.target_end = state.cut,
        !.target_custody = IF Mutation = "forget_custody" THEN {Target} ELSE state.source_custody]

Activate ==
    /\ state.installed
    /\ state.target_mode = "inactive"
    /\ state' = [state EXCEPT !.target_mode = "serving"]

RetireAtSource ==
    /\ SourceWritable
    /\ state' = [state EXCEPT !.source_mode = "retired", !.retire_reply = Source]

RetireAtTarget ==
    /\ TargetWritable
    /\ state' = [state EXCEPT !.target_mode = "retired", !.retire_reply = Target]

ReceiveStaleRetire ==
    /\ SourceSealed
    /\ ~state.redirected
    /\ state' = [state EXCEPT !.redirected = TRUE,
        !.retire_reply = IF Mutation = "sealed_claims_retired" THEN Source ELSE @]

Dispose(location) ==
    /\ Retired
    /\ location \in KnownCustody \ state.fenced
    /\ state' = [state EXCEPT !.fenced = @ \cup {location}, !.resident = @ \ {location}]

Complete ==
    /\ Retired
    /\ ~state.complete
    /\ KnownCustody \subseteq state.fenced
    /\ state' = [state EXCEPT !.complete = TRUE]

Next ==
    \/ ReserveMove \/ AppendSource \/ AppendTarget \/ Seal \/ Install \/ Activate
    \/ RetireAtSource \/ RetireAtTarget \/ ReceiveStaleRetire \/ Complete
    \/ \E location \in Locations :
         ReserveCopy(location) \/ DeliverCopy(location) \/ Dispose(location)

Spec == Init /\ [][Next]_state

OneAuthority == ~(SourceWritable /\ TargetWritable)
ExactCut == state.installed => state.target_end >= state.cut /\ state.cut = state.source_end
AcknowledgedRetirementIsTerminal ==
    state.retire_reply # 0 => Retired /\ ~SourceWritable /\ ~TargetWritable
NoPostRetirementCommit == ~state.after_retire_append
CompleteCoversCustody == state.complete => state.resident = {} /\
    (state.source_custody \cup state.target_custody) \subseteq state.fenced

NeverRetiresAfterRedirect ==
    ~(state.redirected /\ state.retire_reply = Target /\ state.complete)

NeverRetiresBeforeSeal ==
    ~(state.plan /\ state.retire_reply = Source /\ state.complete)
=============================================================================
