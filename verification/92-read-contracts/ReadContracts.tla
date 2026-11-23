------------------------------ MODULE ReadContracts ---------------------------
EXTENDS Naturals

CONSTANT Path, Scenario, Variant

VARIABLES phase, chosen, data, retiredAt, applied, appliedData, gate, route, scope,
          originalClosed, original, reusable, requested, needed, sampled, seenScope,
          protected, selected, gateAtUse, routeAtUse, returned, refused, writes

vars == <<phase, chosen, data, retiredAt, applied, appliedData, gate, route, scope,
          originalClosed, original, reusable, requested, needed, sampled, seenScope,
          protected, selected, gateAtUse, routeAtUse, returned, refused, writes>>

Exact == Scenario \in {"lost-exact", "close-reissue"}
Lost == (Scenario = "lost-fresh") \/ Exact
KeepsOriginal == Path = "ordered" \/ (Path = "split" /\ Exact)
Positive == returned # 0
FirstPhase == IF Lost THEN "first" ELSE IF Scenario = "terminal-before" THEN "retire" ELSE "begin"

Init ==
  /\ phase = FirstPhase
  /\ chosen = 1
  /\ data = 1
  /\ retiredAt = 0
  /\ applied = 1
  /\ appliedData = 1
  /\ gate = TRUE
  /\ route = TRUE
  /\ scope = 1
  /\ originalClosed = FALSE
  /\ original = 0
  /\ reusable = 0
  /\ requested = 0
  /\ needed = 0
  /\ sampled = 0
  /\ seenScope = 0
  /\ protected = FALSE
  /\ selected = 0
  /\ gateAtUse = FALSE
  /\ routeAtUse = FALSE
  /\ returned = 0
  /\ refused = FALSE
  /\ writes = 0

LoseReply ==
  /\ phase = "first"
  /\ phase' = "advance"
  /\ original' = data
  /\ reusable' = IF KeepsOriginal THEN data ELSE 0
  /\ writes' = IF KeepsOriginal THEN writes + 1 ELSE writes
  /\ UNCHANGED <<chosen, data, retiredAt, applied, appliedData, gate, route, scope,
                 requested, needed, sampled, seenScope, protected, selected,
                 gateAtUse, routeAtUse, returned, refused, originalClosed>>

ReplaceAuthority ==
  /\ phase = "advance"
  /\ phase' = "begin"
  /\ chosen' = chosen + 1
  /\ data' = data + 1
  /\ scope' = scope + 1
  /\ reusable' = IF Variant = "lose-handle" THEN 0 ELSE reusable
  /\ UNCHANGED <<retiredAt, applied, appliedData, gate, route, originalClosed, original,
                 requested, needed, sampled, seenScope, protected, selected,
                 gateAtUse, routeAtUse, returned, refused, writes>>

RetireFirst ==
  /\ phase = "retire"
  /\ phase' = "begin"
  /\ chosen' = chosen + 1
  /\ retiredAt' = chosen'
  /\ UNCHANGED <<data, applied, appliedData, gate, route, scope, originalClosed, original, reusable,
                 requested, needed, sampled, seenScope, protected, selected,
                 gateAtUse, routeAtUse, returned, refused, writes>>

Begin ==
  /\ phase = "begin"
  /\ phase' = "round"
  /\ requested' = chosen
  /\ UNCHANGED <<chosen, data, retiredAt, applied, appliedData, gate, route, scope,
                 originalClosed, original, reusable, needed, sampled, seenScope, protected, selected,
                 gateAtUse, routeAtUse, returned, refused, writes>>

Probe ==
  /\ phase = "round"
  /\ route
  /\ phase' = IF Scenario \in {"overlap", "gate-race", "scope-race", "close-reissue"} THEN "race" ELSE "admit"
  /\ needed' = IF Variant = "data-floor" THEN data ELSE chosen
  /\ sampled' = data
  /\ seenScope' = scope
  /\ UNCHANGED <<chosen, data, retiredAt, applied, appliedData, gate, route, scope,
                 originalClosed, original, reusable, requested, protected, selected,
                 gateAtUse, routeAtUse, returned, refused, writes>>

Race ==
  /\ phase = "race"
  /\ phase' = "admit"
  /\ chosen' = chosen + 1
  /\ retiredAt' = IF Scenario = "overlap" THEN chosen' ELSE retiredAt
  /\ gate' = (Scenario # "gate-race")
  /\ scope' = IF Scenario = "scope-race" THEN scope + 1 ELSE scope
  /\ originalClosed' = (Scenario = "close-reissue")
  /\ UNCHANGED <<data, applied, appliedData, route, original, reusable, requested,
                 needed, sampled, seenScope, protected, selected, gateAtUse, routeAtUse,
                 returned, refused, writes>>

CatchUp ==
  /\ phase = "admit"
  /\ applied < chosen
  /\ applied' = chosen
  /\ appliedData' = data
  /\ UNCHANGED <<phase, chosen, data, retiredAt, gate, route, scope, originalClosed, original, reusable,
                 requested, needed, sampled, seenScope, protected, selected,
                 gateAtUse, routeAtUse, returned, refused, writes>>

ValidLatest ==
  /\ applied >= needed
  /\ retiredAt = 0 \/ applied < retiredAt
  /\ seenScope = scope \/ Variant = "stale-scope"
  /\ gate \/ Variant = "cached-gate"

Ready ==
  IF Exact THEN applied >= needed /\ reusable # 0 /\ gate /\ seenScope = scope /\
          (~originalClosed \/ Variant = "probe-allows-closed")
  ELSE ValidLatest

Admit ==
  /\ phase = "admit"
  /\ Ready
  /\ phase' = IF Scenario = "lose-after-admit" THEN "lose-route" ELSE "finish"
  /\ protected' = TRUE
  /\ selected' = IF Exact THEN reusable ELSE appliedData
  /\ gateAtUse' = gate
  /\ routeAtUse' = route
  /\ writes' = IF Path = "ordered" \/ Exact THEN writes + 1 ELSE writes
  /\ UNCHANGED <<chosen, data, retiredAt, applied, appliedData, gate, route, scope,
                 originalClosed, original, reusable, requested, needed, sampled, seenScope,
                 returned, refused>>

Refuse ==
  /\ phase = "admit"
  /\ applied >= needed
  /\ ~Ready
  /\ phase' = "done"
  /\ refused' = TRUE
  /\ UNCHANGED <<chosen, data, retiredAt, applied, appliedData, gate, route, scope,
                 originalClosed, original, reusable, requested, needed, sampled, seenScope,
                 protected, selected, gateAtUse, routeAtUse, returned, writes>>

LoseRoute ==
  /\ phase = "lose-route"
  /\ phase' = "finish"
  /\ route' = FALSE
  /\ UNCHANGED <<chosen, data, retiredAt, applied, appliedData, gate, scope,
                 originalClosed, original, reusable, requested, needed, sampled, seenScope,
                 protected, selected, gateAtUse, routeAtUse, returned, refused, writes>>

Finish ==
  /\ phase = "finish"
  /\ protected
  /\ Variant # "recontact" \/ route
  /\ phase' = "done"
  /\ returned' = selected
  /\ UNCHANGED <<chosen, data, retiredAt, applied, appliedData, gate, route, scope,
                 originalClosed, original, reusable, requested, needed, sampled, seenScope,
                 protected, selected, gateAtUse, routeAtUse, refused, writes>>

ResampleExact ==
  /\ phase = "admit"
  /\ Exact
  /\ Variant = "exact-as-fresh"
  /\ applied >= needed
  /\ phase' = "done"
  /\ returned' = appliedData
  /\ UNCHANGED <<chosen, data, retiredAt, applied, appliedData, gate, route, scope,
                 originalClosed, original, reusable, requested, needed, sampled, seenScope,
                 protected, selected, gateAtUse, routeAtUse, refused, writes>>

OriginalAnswer == (Exact /\ Positive) => returned = original
FreshAnswer == (~Exact /\ Positive) => (returned >= sampled /\ needed >= requested)
AdmittedUnderGate == protected => gateAtUse /\ routeAtUse /\ seenScope = scope
NoClosedReissue == (Exact /\ originalClosed) => ~Positive
NoPostTerminal == (retiredAt # 0 /\ requested >= retiredAt) => ~Positive
NoLogWriteForSplitObservation == (Path = "split" /\ ~Exact) => writes = 0
OldAnswer == <> (returned = 1)
NewAnswer == <> (returned = 2)
Refusal == <> refused

Next == LoseReply \/ ReplaceAuthority \/ RetireFirst \/ Begin \/ Probe \/ Race \/ CatchUp \/
        Admit \/ Refuse \/ LoseRoute \/ Finish \/ ResampleExact
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Next)

=============================================================================
