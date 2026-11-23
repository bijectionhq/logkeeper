---------------------------- MODULE Eligibility -----------------------------
EXTENDS Naturals

CONSTANTS Variant, Scenario
VARIABLES issued, roster, holder, epoch, enrollment, retired, withdrawalMatched

Workers == {"old", "candidate", "unrelated"}
Vacant == "vacant"
FirstSerial == 3
LastSerial == 6
Original == [worker \in Workers |->
    CASE worker = "candidate" -> 1
      [] worker = "old" -> 2
      [] OTHER -> FirstSerial]

Init ==
    /\ issued = IF Scenario = "exhausted" THEN LastSerial ELSE FirstSerial
    /\ roster = Original
    /\ holder = "old"
    /\ epoch = 0
    /\ enrollment = Original["old"]
    /\ retired = FALSE
    /\ withdrawalMatched = TRUE

Withdraw(worker, binding) ==
    /\ ~retired
    /\ roster[worker] # 0
    /\ Variant # "needs-new-serial" \/ issued < LastSerial
    /\ Variant = "ignore-binding" \/ binding = roster[worker]
    /\ roster' = [roster EXCEPT ![worker] = 0]
    /\ withdrawalMatched' = (binding = roster[worker])
    /\ IF holder = worker /\ Variant # "leave-grant"
       THEN /\ holder' = Vacant /\ enrollment' = 0
       ELSE UNCHANGED <<holder, enrollment>>
    /\ UNCHANGED <<issued, epoch, retired>>

Enroll(worker) ==
    /\ ~retired
    /\ issued < LastSerial
    /\ roster[worker] = 0
    /\ issued' = issued + 1
    /\ roster' = [roster EXCEPT ![worker] = issued']
    /\ UNCHANGED <<holder, epoch, enrollment, retired, withdrawalMatched>>

Replace(binding) ==
    /\ ~retired
    /\ epoch = 0
    /\ Variant = "trust-ticket" \/ roster["candidate"] # 0
    /\ Variant \in {"trust-ticket", "match-id-only"} \/ roster["candidate"] = binding
    /\ holder' = "candidate"
    /\ enrollment' = binding
    /\ epoch' = epoch + 1
    /\ UNCHANGED <<issued, roster, retired, withdrawalMatched>>

Retire ==
    /\ ~retired
    /\ holder = Vacant
    /\ Variant # "need-holder"
    /\ retired' = TRUE
    /\ UNCHANGED <<issued, roster, holder, epoch, enrollment, withdrawalMatched>>

Edit ==
    \/ \E worker \in Workers : Enroll(worker)
    \/ \E worker \in Workers : Withdraw(worker, Original[worker]) \/ Withdraw(worker, roster[worker])

Vars == <<issued, roster, holder, epoch, enrollment, retired, withdrawalMatched>>
Closing == Scenario \in {"retire-vacant", "exhausted"}
OldNomination == Replace(Original["candidate"])
OldWithdrawal == Withdraw("old", Original["old"])
Next ==
    \/ UNCHANGED Vars
    \/ CASE Closing -> (OldWithdrawal \/ Retire)
      [] Scenario = "unrelated-churn" ->
          Withdraw("unrelated", roster["unrelated"]) \/ Enroll("unrelated") \/ OldNomination
      [] OTHER -> Edit \/ OldNomination \/
                  (roster["candidate"] # 0 /\ Replace(roster["candidate"])) \/ Retire

Spec == Init /\ [][Next]_Vars
Fair ==
    /\ Spec
    /\ IF Closing
        THEN WF_Vars(Retire) /\ WF_Vars(OldWithdrawal)
        ELSE WF_Vars(OldNomination)

GrantHasEnrollment == holder = Vacant \/
    (roster[holder] # 0 /\ roster[holder] = enrollment)
ExactWithdrawal == withdrawalMatched
EnrollmentCountersOrdered ==
    /\ \A worker \in Workers : roster[worker] <= issued
    /\ \A first, second \in Workers :
           roster[first] # 0 /\ roster[first] = roster[second] => first = second
RetirementCompletes == <>retired
UnrelatedChangesKeepNominationLive == <>(holder = "candidate")
=============================================================================
