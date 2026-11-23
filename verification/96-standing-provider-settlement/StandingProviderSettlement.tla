----------------------- MODULE StandingProviderSettlement --------------------
EXTENDS Naturals

CONSTANT Scenario, Variant

VARIABLES phase, active, issued, chosen, locallySeen, frozen, stopped, present, charged,
          effects, reused, rejected, records, complete

vars == <<phase, active, issued, chosen, locallySeen, frozen, stopped, present, charged,
          effects, reused, rejected, records, complete>>
Rounds == 3
Hidden == Scenario \in {"hidden", "retained"}
Capacity == 1

Init ==
  /\ phase = "install"
  /\ active = 0
  /\ issued = 0
  /\ chosen = FALSE
  /\ locallySeen = FALSE
  /\ frozen = FALSE
  /\ stopped = FALSE
  /\ present = FALSE
  /\ charged = 0
  /\ effects = 0
  /\ reused = FALSE
  /\ rejected = FALSE
  /\ records = 0
  /\ complete = FALSE

Install ==
  /\ phase = "install"
  /\ charged < Capacity
  /\ issued < Rounds
  /\ phase' = "choose"
  /\ active' = issued + 1
  /\ issued' = active'
  /\ charged' = charged + 1
  /\ present' = TRUE
  /\ chosen' = FALSE
  /\ locallySeen' = FALSE
  /\ frozen' = FALSE
  /\ stopped' = FALSE
  /\ effects' = 0
  /\ UNCHANGED <<reused, rejected, records, complete>>

Choose ==
  /\ phase = "choose"
  /\ phase' = "seal"
  /\ chosen' = Hidden
  /\ locallySeen' = (Scenario = "retained")
  /\ UNCHANGED <<active, issued, frozen, stopped, present, charged, effects,
                 reused, rejected, records, complete>>

InstallFence ==
  /\ phase = "seal"
  /\ phase' = "transfer"
  /\ frozen' = IF Variant = "fence-local-seen" THEN locallySeen ELSE chosen
  /\ UNCHANGED <<active, issued, chosen, locallySeen, stopped, present, charged, effects,
                 reused, rejected, records, complete>>

TryExisting ==
  /\ phase = "transfer"
  /\ phase' = "stop"
  /\ effects' = IF frozen \/ Variant = "fence-not-exact" THEN effects + 1 ELSE effects
  /\ UNCHANGED <<active, issued, chosen, locallySeen, frozen, stopped, present, charged,
                 reused, rejected, records, complete>>

Stop ==
  /\ phase = "stop"
  /\ phase' = "close"
  /\ stopped' = frozen
  /\ UNCHANGED <<active, issued, chosen, locallySeen, frozen, present, charged, effects,
                 reused, rejected, records, complete>>

TryAfterStop ==
  /\ phase = "close"
  /\ phase' = "delete"
  /\ effects' = IF frozen /\ Variant = "ignore-terminal" THEN effects + 1 ELSE effects
  /\ reused' = (effects' > effects)
  /\ UNCHANGED <<active, issued, chosen, locallySeen, frozen, stopped, present, charged,
                 rejected, records, complete>>

Delete ==
  /\ phase = "delete"
  /\ ~frozen \/ stopped
  /\ phase' = "refund"
  /\ present' = (Variant = "refund-with-data")
  /\ UNCHANGED <<active, issued, chosen, locallySeen, frozen, stopped, charged, effects,
                 reused, rejected, records, complete>>

Refund ==
  /\ phase = "refund"
  /\ (Variant # "need-spare-to-refund" \/ charged < Capacity)
  /\ (Variant = "refund-with-data" \/ ~present)
  /\ phase' = "delayed"
  /\ active' = 0
  /\ charged' = charged - 1
  /\ records' = IF Variant = "keep-tombstones" THEN records + 1 ELSE records
  /\ UNCHANGED <<issued, chosen, locallySeen, frozen, stopped, present, effects, reused, rejected, complete>>

TryRetired ==
  /\ phase = "delayed"
  /\ phase' = IF issued = Rounds THEN "done" ELSE "install"
  /\ complete' = (issued = Rounds)
  /\ IF Variant = "permit-absent-issued"
        THEN (reused' = TRUE /\ rejected' = FALSE)
        ELSE (reused' = reused /\ rejected' = TRUE)
  /\ UNCHANGED <<active, issued, chosen, locallySeen, frozen, stopped, present, charged,
                 effects, records>>

HeldExactly == (chosen /\ ~stopped) => (charged = 1 /\ present)
CanStartOnlyAdmitted == effects > 0 => chosen
NoReuse == ~reused
ChargedUntilAbsent == present => charged = 1
Fits == charged <= Capacity
BoundedEvidence == records <= Capacity
EventuallyRotates == <> (complete /\ rejected /\ charged = 0)

Next == Install \/ Choose \/ InstallFence \/ TryExisting \/ Stop \/ TryAfterStop \/ Delete \/ Refund \/ TryRetired
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Next)

=============================================================================
