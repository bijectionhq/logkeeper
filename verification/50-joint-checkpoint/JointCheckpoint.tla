----------------------------- MODULE JointCheckpoint -----------------------------
EXTENDS Naturals

CONSTANTS Variant, Policy, Scenario
VARIABLE s

ResultAt(cut, outcome) ==
    CASE cut = 0 -> "unused"
      [] cut <= 2 -> outcome
      [] OTHER -> "closed"

Image(cut, outcome, witness) == [cut |-> cut, result |-> ResultAt(cut, outcome), witness |-> witness]
Genesis == Image(0, "unused", FALSE)

Init ==
    s = [head |-> 0, outcome |-> "unused", commands |-> {}, evidence |-> {},
         stable |-> Genesis, shown |-> Genesis, staged |-> Genesis, pendingRoot |-> FALSE,
         consumed |-> FALSE, running |-> TRUE, restarted |-> FALSE, borrowed |-> {},
         emitted |-> "unused", emittedAfterTrimRestart |-> FALSE, crashCoverage |-> "other"]

Choices == {s.stable, s.shown}
StillOwed == s.head = 1
ExactImage(root) == root.cut <= s.head /\ root.result = ResultAt(root.cut, s.outcome)
CanReissue(root) == root.cut = 1 /\ root.witness /\ root.result = s.outcome

ReplayCovered(root) ==
    /\ ExactImage(root)
    /\ \A index \in 1..s.head : root.cut < index => index \in s.commands
    /\ \A index \in 1..2 : root.cut < index /\ index <= s.head => index \in s.evidence

Choose(outcome) ==
    /\ s.running /\ s.head = 0
    /\ s' = [s EXCEPT !.head = 1, !.outcome = outcome, !.commands = {1}, !.evidence = {1}]

ApplyAtConsumer ==
    /\ Scenario # "offline" /\ StillOwed /\ ~s.consumed
    /\ 1 \in s.evidence \/ CanReissue(s.shown)
    /\ s' = [s EXCEPT !.consumed = TRUE]

Acknowledge ==
    /\ s.running /\ StillOwed /\ s.consumed
    /\ s' = [s EXCEPT !.head = 2, !.commands = @ \cup {2}, !.evidence = @ \cup {2}]

Compact ==
    /\ s.running /\ s.head = 2
    /\ s' = [s EXCEPT !.head = 3, !.commands = @ \cup {3}]

Stage ==
    /\ s.running /\ ~s.pendingRoot /\ s.shown.cut < s.head
    /\ s' = [s EXCEPT !.pendingRoot = TRUE,
         !.staged = IF Variant = "drop_result_row" /\ s.head = 1
                     THEN [Image(s.head, s.outcome, TRUE) EXCEPT !.result = "unused"]
                     ELSE Image(s.head, s.outcome, s.head = 1 /\ Policy = "certified" /\ Variant # "omit_witness")]

Publish ==
    /\ s.running /\ s.pendingRoot /\ s.stable = s.shown
    /\ s' = [s EXCEPT !.shown = s.staged, !.pendingRoot = FALSE]

Sync ==
    /\ s.running /\ s.shown # s.stable
    /\ s' = [s EXCEPT !.stable = s.shown]

ReclaimViews == IF Variant = "visible_only" THEN {s.shown} ELSE Choices

Trim(index) ==
    /\ index \in s.commands
    /\ \A root \in ReclaimViews : index <= root.cut
    /\ s' = [s EXCEPT !.commands = @ \ {index}]

Forget(index) ==
    /\ index \in s.evidence
    /\ index \notin s.borrowed \/ Variant = "ignore_borrow"
    /\ \A root \in ReclaimViews : index <= root.cut
    /\ index # 1 \/ ~StillOwed \/ Variant = "forget_live" \/ Variant = "omit_witness" \/
         (Policy = "certified" /\ \A root \in Choices : CanReissue(root))
    /\ s' = [s EXCEPT !.evidence = @ \ {index}]

Borrow(index) ==
    /\ index \in s.evidence /\ index \notin s.borrowed
    /\ s' = [s EXCEPT !.borrowed = @ \cup {index}]

Return(index) ==
    /\ index \in s.borrowed
    /\ s' = [s EXCEPT !.borrowed = @ \ {index}]

Crash(root) ==
    /\ s.running /\ ~s.restarted /\ root \in Choices
    /\ s' = [s EXCEPT !.running = FALSE, !.restarted = TRUE,
         !.crashCoverage = CASE StillOwed /\ 1 \notin s.commands /\ 1 \notin s.evidence -> "awaiting"
                             [] s.head = 3 /\ s.commands = {} /\ s.evidence = {} -> "settled"
                             [] OTHER -> "other",
         !.stable = root, !.shown = root, !.pendingRoot = FALSE]

Open ==
    /\ ~s.running /\ ReplayCovered(s.shown)
    /\ s' = [s EXCEPT !.running = TRUE]

Emit ==
    /\ s.running /\ StillOwed /\ s.emitted = "unused"
    /\ CanReissue(s.shown)
    /\ s' = [s EXCEPT !.emitted = s.shown.result,
         !.emittedAfterTrimRestart = s.crashCoverage = "awaiting"]

Next ==
    \/ \E outcome \in {"abort", "seal"} : Choose(outcome)
    \/ ApplyAtConsumer \/ Acknowledge \/ Compact \/ Stage \/ Publish \/ Sync \/ Open \/ Emit
    \/ \E root \in Choices : Crash(root)
    \/ \E index \in 1..3 : Trim(index) \/ Forget(index) \/ Borrow(index) \/ Return(index)

Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(Open)

EveryBaseCanReplay == \A root \in Choices : ReplayCovered(root)
StillOwedHasEvidence == StillOwed => 1 \in s.evidence \/ \A root \in Choices : CanReissue(root)
BorrowsRetainEvidence == s.borrowed \subseteq s.evidence
IssuedResultExact == s.emitted = "unused" \/ s.emitted = s.outcome
Reopens == ~s.running ~> s.running

NeverReissuesAfterTrimAndRestart ==
    ~(s.emittedAfterTrimRestart /\ s.emitted = s.outcome /\ StillOwed /\ Scenario = "offline")
NeverCompactsAcknowledgmentAfterRecovery ==
    ~(s.crashCoverage = "settled" /\ s.running /\ s.head = 3 /\ s.stable.cut = 3 /\
      s.commands = {} /\ s.evidence = {})
=============================================================================
