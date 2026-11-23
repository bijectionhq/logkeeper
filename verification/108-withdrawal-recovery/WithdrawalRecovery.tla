------------------------------ MODULE WithdrawalRecovery ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Scenario, Policy
VARIABLES history, stable, visible, applied, online, crashed, staged, dispatched, fenced, copies, lost

vars == <<history, stable, visible, applied, online, crashed, staged, dispatched, fenced, copies, lost>>
InPrefix(event, cut) == \E i \in 1..cut : history[i] = event
Chosen(event) == InPrefix(event, Len(history))
At(cut) ==
  [oldRoot |-> ~InPrefix("release-root", cut),
   read |-> ~InPrefix("finish-read", cut),
   delivery |-> Scenario # "ordinary-read" /\ ~InPrefix("finish-delivery", cut),
   a |-> IF InPrefix("settle-A", cut) THEN "gone"
         ELSE IF InPrefix("reserve-A", cut) THEN "withdrawing" ELSE "open",
   c |-> IF InPrefix("reserve-C", cut) THEN "withdrawing" ELSE "open"]
Current == At(Len(history))

Init ==
  /\ history = <<>>
  /\ stable = 0
  /\ visible = 0
  /\ applied = Current
  /\ online = TRUE
  /\ crashed = FALSE
  /\ staged = FALSE
  /\ dispatched = FALSE
  /\ fenced = FALSE
  /\ copies = {"A", "B", "C"}
  /\ lost = "none"

Release(action, field) ==
  /\ online
  /\ applied[field]
  /\ ~Chosen(action)
  /\ history' = Append(history, action)
  /\ applied' = [applied EXCEPT ![field] = FALSE]
  /\ UNCHANGED <<stable, visible, online, crashed, staged, dispatched, fenced, copies, lost>>

ReleaseRoot == Release("release-root", "oldRoot")
FinishRead == Release("finish-read", "read")
FinishDelivery == Scenario # "pinned-delivery" /\ Release("finish-delivery", "delivery")

Stage ==
  /\ Scenario = "staging"
  /\ ~staged
  /\ staged' = TRUE
  /\ UNCHANGED <<history, stable, visible, applied, online, crashed, dispatched, fenced, copies, lost>>

ReserveA ==
  /\ online
  /\ applied.a = "open"
  /\ ~Chosen("reserve-A")
  /\ ~applied.oldRoot \/ Policy = "visible-only"
  /\ ~applied.read \/ Policy = "drop-read"
  /\ ~applied.delivery \/ Policy = "drop-delivery"
  /\ applied.c = "open"
  /\ history' = Append(history, "reserve-A")
  /\ applied' = [applied EXCEPT !.a = "withdrawing"]
  /\ UNCHANGED <<stable, visible, online, crashed, staged, dispatched, fenced, copies, lost>>

ReserveC ==
  /\ Scenario = "recovery-race"
  /\ online
  /\ crashed
  /\ applied.a = "open"
  /\ applied.c = "open"
  /\ history' = Append(history, "reserve-C")
  /\ applied' = [applied EXCEPT !.c = "withdrawing"]
  /\ UNCHANGED <<stable, visible, online, crashed, staged, dispatched, fenced, copies, lost>>

Dispatch ==
  /\ online
  /\ ~dispatched
  /\ applied.a = "withdrawing" \/ (staged /\ Policy = "send-staged")
  /\ dispatched' = TRUE
  /\ UNCHANGED <<history, stable, visible, applied, online, crashed, staged, fenced, copies, lost>>

FenceProvider ==
  /\ dispatched
  /\ ~fenced
  /\ fenced' = TRUE
  /\ UNCHANGED <<history, stable, visible, applied, online, crashed, staged, dispatched, copies, lost>>

EffectA ==
  /\ dispatched
  /\ fenced
  /\ "A" \in copies
  /\ Scenario # "offline-effect" \/ ~online
  /\ Policy # "needs-live-authority" \/ online
  /\ copies' = copies \ {"A"}
  /\ UNCHANGED <<history, stable, visible, applied, online, crashed, staged, dispatched, fenced, lost>>

EffectC ==
  /\ Chosen("reserve-C")
  /\ "C" \in copies
  /\ copies' = copies \ {"C"}
  /\ UNCHANGED <<history, stable, visible, applied, online, crashed, staged, dispatched, fenced, lost>>

Settle ==
  /\ online
  /\ applied.a = "withdrawing"
  /\ ("A" \notin copies /\ fenced) \/ Policy = "probe-is-receipt"
  /\ history' = Append(history, "settle-A")
  /\ applied' = [applied EXCEPT !.a = "gone"]
  /\ UNCHANGED <<stable, visible, online, crashed, staged, dispatched, fenced, copies, lost>>

Publish ==
  /\ online
  /\ Scenario \in {"recovery-race", "offline-effect", "settlement"}
  /\ Chosen("reserve-A")
  /\ visible = 0
  /\ visible' = Len(history)
  /\ UNCHANGED <<history, stable, applied, online, crashed, staged, dispatched, fenced, copies, lost>>

Crash ==
  /\ Scenario \in {"recovery-race", "offline-effect"}
  /\ online
  /\ ~crashed
  /\ dispatched
  /\ \E root \in {stable, visible} : /\ stable' = root
                                      /\ visible' = root
  /\ online' = FALSE
  /\ crashed' = TRUE
  /\ UNCHANGED <<history, applied, staged, dispatched, fenced, copies, lost>>

Recover ==
  /\ ~online
  /\ Scenario # "offline-effect" \/ "A" \notin copies
  /\ applied' =
    CASE Policy = "base-only" -> At(visible)
      [] Policy = "scan-physical" /\ "A" \in copies -> [Current EXCEPT !.a = "open"]
      [] OTHER -> Current
  /\ online' = TRUE
  /\ UNCHANGED <<history, stable, visible, crashed, staged, dispatched, fenced, copies, lost>>

LoseB ==
  /\ Scenario = "recovery-race"
  /\ lost = "none"
  /\ lost' = "B"
  /\ UNCHANGED <<history, stable, visible, applied, online, crashed, staged, dispatched, fenced, copies>>

Next ==
  ReleaseRoot \/ FinishRead \/ FinishDelivery \/ Stage \/ ReserveA \/ ReserveC \/ Dispatch \/
  FenceProvider \/ EffectA \/ EffectC \/ Settle \/ Publish \/ Crash \/ Recover \/ LoseB
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(ReleaseRoot) /\ WF_vars(FinishRead) /\ WF_vars(FinishDelivery) /\
  WF_vars(ReserveA) /\ WF_vars(Dispatch) /\ WF_vars(FenceProvider) /\ WF_vars(Crash) /\
  WF_vars(EffectA) /\ WF_vars(Recover) /\ WF_vars(Settle)

ExactReplay == online => applied = Current
ExactHolds == (Current.oldRoot \/ Current.read \/ Current.delivery) => "A" \in copies
AuthorizedEffect == "A" \notin copies => Chosen("reserve-A")
ChargedUntilAbsent == Chosen("settle-A") => "A" \notin copies /\ fenced
SurvivesB == copies \ {lost} # {}
EventuallySettled == <>Chosen("settle-A")
NeverSettlesFromNewerSelector == ~(crashed /\ stable > 0 /\ Chosen("settle-A"))
NeverSettlesFromOlderSelector == ~(crashed /\ stable = 0 /\ Chosen("settle-A"))
NeverDeletesAfterFinishingRead == ~(Chosen("finish-read") /\ "A" \notin copies)
======================================================================================
