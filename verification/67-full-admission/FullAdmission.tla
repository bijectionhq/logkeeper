----------------------------- MODULE FullAdmission ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Variant
AZ == {1, 2, 3}
Objects == 1..7
Copies(object) ==
    CASE object = 5 -> {1, 3} [] object = 6 -> {2, 3} [] object = 7 -> {1, 2} [] OTHER -> AZ

VARIABLES scope, outline, missing, outage, mode, revalidated, cached, unsafe, degradedAdmitted, renewedUnsafe
vars == <<scope, outline, missing, outage, mode, revalidated, cached, unsafe, degradedAdmitted, renewedUnsafe>>

Init ==
    /\ scope = 1 /\ outline = 0 /\ missing = {}
    /\ outage = 0 /\ mode = 0 /\ revalidated = FALSE
    /\ cached = <<0, 0, {}, 0, 0, FALSE>>
    /\ unsafe = FALSE /\ degradedAdmitted = FALSE /\ renewedUnsafe = FALSE

Available == IF outage = 0 \/ revalidated THEN AZ ELSE AZ \ {outage}
Stamp == <<scope, outline, missing, outage, mode, revalidated>>
Cases(faultMode) == IF faultMode = 0 THEN AZ \cup {0} ELSE {faultMode}
Required == {1, 2, 3, 4, 7} \cup (IF outline < 2 THEN {5} ELSE {}) \cup (IF outline > 0 THEN {6} ELSE {})
Remaining(failure) == Available \ {failure}
Complete(objects, cases) ==
    \A failed \in cases :
      /\ Cardinality(Remaining(failed)) >= 2
      /\ \A object \in objects : object \notin missing /\ Copies(object) \intersect Remaining(failed) # {}
WindowReady == 2 \in Available
ExactReady == WindowReady /\ Complete(Required, Cases(mode))
CheckedObjects ==
    CASE Variant = "visible_only" /\ outline = 1 -> Required \ {5}
      [] Variant = "ignore_tail" -> Required \ {7}
      [] OTHER -> Required
CheckedCases == IF Variant = "reset_fault_allowance" THEN Cases(0) ELSE Cases(mode)

Observe ==
    /\ WindowReady
    /\ Variant = "window_only" \/ Complete(CheckedObjects, CheckedCases)
    /\ cached' = Stamp
    /\ UNCHANGED <<scope, outline, missing, outage, mode, revalidated, unsafe, degradedAdmitted, renewedUnsafe>>

Admit ==
    /\ cached[1] # 0
    /\ cached = Stamp \/ Variant = "stale_scope"
    /\ unsafe' = (unsafe \/ cached # Stamp \/ ~ExactReady)
    /\ degradedAdmitted' = (degradedAdmitted \/ (mode # 0 /\ ~revalidated))
    /\ UNCHANGED <<scope, outline, missing, outage, mode, revalidated, cached, renewedUnsafe>>

PublishSelector ==
    /\ outline < 2
    /\ outline' = outline + 1
    /\ UNCHANGED <<scope, missing, outage, mode, revalidated, cached, unsafe, degradedAdmitted, renewedUnsafe>>

ReplaceFamily ==
    /\ scope = 1 /\ scope' = 2
    /\ UNCHANGED <<outline, missing, outage, mode, revalidated, cached, unsafe, degradedAdmitted, renewedUnsafe>>

Unavailable(input) ==
    /\ input \in {5, 7}
    /\ missing' = missing \cup {input}
    /\ UNCHANGED <<scope, outline, outage, mode, revalidated, cached, unsafe, degradedAdmitted, renewedUnsafe>>

LoseZone(zone) ==
    /\ outage = 0
    /\ outage' = zone /\ mode' = zone
    /\ UNCHANGED <<scope, outline, missing, revalidated, cached, unsafe, degradedAdmitted, renewedUnsafe>>

ValidateReturn ==
    /\ mode # 0
    /\ revalidated' = TRUE
    /\ UNCHANGED <<scope, outline, missing, outage, mode, cached, unsafe, degradedAdmitted, renewedUnsafe>>

RenewHealthy ==
    /\ mode # 0
    /\ Complete(Required, Cases(0)) \/ Variant = "early_healthy"
    /\ mode' = 0
    /\ renewedUnsafe' = (renewedUnsafe \/ ~Complete(Required, Cases(0)))
    /\ UNCHANGED <<scope, outline, missing, outage, revalidated, cached, unsafe, degradedAdmitted>>

Next ==
    \/ Observe \/ Admit \/ PublishSelector \/ ReplaceFamily \/ ValidateReturn \/ RenewHealthy
    \/ \E input \in Objects : Unavailable(input)
    \/ \E zone \in AZ : LoseZone(zone)
Spec == Init /\ [][Next]_vars
SafeAdmission == ~unsafe
HealthyRenewalSound == ~renewedUnsafe
NeverAdmitDuringOutage == ~degradedAdmitted

ObserveDegraded == outage = 1 /\ Observe
AdmitDegraded == outage = 1 /\ Admit
DegradedNext == LoseZone(1) \/ ObserveDegraded \/ AdmitDegraded
StableDegraded ==
    Init /\ [][DegradedNext]_vars
    /\ WF_vars(LoseZone(1)) /\ WF_vars(ObserveDegraded) /\ WF_vars(AdmitDegraded)
EventuallyAdmitDegraded == <>degradedAdmitted
=============================================================================
