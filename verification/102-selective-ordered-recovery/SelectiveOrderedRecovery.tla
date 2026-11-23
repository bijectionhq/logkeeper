----------------------- MODULE SelectiveOrderedRecovery ---------------------
EXTENDS Naturals, Sequences

CONSTANTS Scenario, Variant, Select

Nonces == {1, 2}
Epochs == {1, 2}
Start == [epoch |-> 1, sealed |-> FALSE, spent |-> {}, live |-> {}, delivery |-> FALSE]

VARIABLES image, chosen, alternate, restored, seen, duplicate, stale, gapResolved, completed
vars == <<image, chosen, alternate, restored, seen, duplicate, stale, gapResolved, completed>>

Init ==
  /\ image = Start
  /\ chosen = <<Start>>
  /\ alternate = 0
  /\ restored = FALSE
  /\ seen = {}
  /\ duplicate = FALSE
  /\ stale = FALSE
  /\ gapResolved = FALSE
  /\ completed = FALSE

Apply(next) ==
  /\ image' = next
  /\ chosen' = Append(chosen, next)

Arrived(epoch, nonce) ==
  CASE epoch = 2 -> Scenario = "handoff" /\ image.epoch = 2
    [] nonce = 2 -> TRUE
    [] OTHER -> restored /\ Scenario = "same-scope"

Open(epoch, nonce) ==
  /\ Arrived(epoch, nonce)
  /\ ~image.sealed
  /\ Variant = "ignore-grant" \/ image.epoch = epoch
  /\ nonce \notin image.spent
  /\ image.live = {}
  /\ Variant # "next-only" \/ nonce = 1 \/ 1 \in image.spent
  /\ Apply([image EXCEPT !.spent = @ \cup {nonce}, !.live = {nonce}])
  /\ duplicate' = (duplicate \/ <<epoch, nonce>> \in seen)
  /\ stale' = (stale \/ image.epoch # epoch \/ image.sealed)
  /\ seen' = seen \cup {<<epoch, nonce>>}
  /\ gapResolved' = (gapResolved \/ (epoch = 1 /\ nonce = 1 /\ restored))
  /\ UNCHANGED <<alternate, restored, completed>>

RegisterDelivery ==
  /\ Scenario = "handoff"
  /\ image.epoch = 1
  /\ image.live = {2}
  /\ ~image.delivery
  /\ Apply([image EXCEPT !.delivery = TRUE])
  /\ UNCHANGED <<alternate, restored, seen, duplicate, stale, gapResolved, completed>>

Close ==
  /\ image.live # {}
  /\ Scenario # "handoff" \/ image.epoch = 2 \/ image.delivery
  /\ Apply([image EXCEPT !.live = {},
        !.spent = IF Variant = "clear-window-on-close" THEN {} ELSE @,
        !.delivery = IF Variant = "drop-delivery-on-close" THEN FALSE ELSE @])
  /\ UNCHANGED <<alternate, restored, seen, duplicate, stale, gapResolved, completed>>

Capture ==
  /\ alternate = 0
  /\ <<1, 2>> \in seen
  /\ image.live = {}
  /\ alternate' = Len(chosen)
  /\ UNCHANGED <<image, chosen, restored, seen, duplicate, stale, gapResolved, completed>>

Restore ==
  /\ ~restored
  /\ alternate # 0
  /\ restored' = TRUE
  /\ LET root == IF Select = "old" THEN 1 ELSE alternate
         exact == chosen[Len(chosen)]
     IN image' = CASE Variant = "omit-suffix" -> chosen[root]
                    [] Variant = "drop-sparse-marks" ->
                        [exact EXCEPT !.spent = IF 1 \in @ THEN @ ELSE {}]
                    [] OTHER -> exact
  /\ UNCHANGED <<chosen, alternate, seen, duplicate, stale, gapResolved, completed>>

Seal ==
  /\ Scenario = "handoff"
  /\ restored
  /\ image.epoch = 1
  /\ ~image.sealed
  /\ Apply([image EXCEPT !.sealed = TRUE])
  /\ UNCHANGED <<alternate, restored, seen, duplicate, stale, gapResolved, completed>>

Activate ==
  /\ image.sealed
  /\ image.epoch = 1
  /\ Apply([image EXCEPT !.epoch = 2, !.sealed = FALSE, !.spent = {}])
  /\ UNCHANGED <<alternate, restored, seen, duplicate, stale, gapResolved, completed>>

FinishDelivery ==
  /\ image.delivery
  /\ image.epoch = 2
  /\ Apply([image EXCEPT !.delivery = FALSE])
  /\ completed' = TRUE
  /\ UNCHANGED <<alternate, restored, seen, duplicate, stale, gapResolved>>

Next ==
  \/ \E epoch \in Epochs, nonce \in Nonces : Open(epoch, nonce)
  \/ RegisterDelivery \/ Close \/ Capture \/ Restore \/ Seal \/ Activate \/ FinishDelivery

Spec == Init /\ [][Next]_vars
Fair ==
  /\ Spec
  /\ \A epoch \in Epochs, nonce \in Nonces : WF_vars(Open(epoch, nonce))
  /\ WF_vars(RegisterDelivery) /\ WF_vars(Close) /\ WF_vars(Capture) /\ WF_vars(Restore)
  /\ WF_vars(Seal) /\ WF_vars(Activate) /\ WF_vars(FinishDelivery)

NoDuplicate == ~duplicate
CurrentGrantOnly == ~stale
ClosesKeepDelivery == (Scenario = "handoff" /\ alternate # 0 /\ ~completed) => image.delivery
Progress ==
  IF Scenario = "same-scope" THEN <>gapResolved ELSE <>(completed /\ <<2, 1>> \in seen)

=============================================================================
