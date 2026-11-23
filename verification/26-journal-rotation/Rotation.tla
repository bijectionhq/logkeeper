------------------------------- MODULE Rotation -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Variant, MaxGeneration, MaxRecord, MaxPowerLosses
VARIABLE s

Generations == 0..MaxGeneration

Init ==
    s = [issued |-> 0, cut |-> [g \in Generations |-> 0],
         parent |-> [g \in Generations |-> 0], bases |-> {0},
         selected |-> 0, stable |-> 0, possible |-> {0},
         tail |-> {1}, ack |-> 1,
         pinned |-> [kind |-> "none", id |-> 0],
         running |-> TRUE, warmDuringSwitch |-> FALSE, powerLosses |-> 0,
         stableRoots |-> {0}, lostAt |-> {},
         stalePublished |-> FALSE, reopenedUnstable |-> FALSE,
         votedAfterWarmOpen |-> FALSE]

Recoverable(g) ==
    /\ g \in s.bases
    /\ (s.cut[g] + 1)..s.ack \subseteq s.tail

AppendDurably ==
    /\ s.ack < MaxRecord
    /\ s' = [s EXCEPT !.ack = @ + 1, !.tail = @ \cup {s.ack + 1},
                      !.votedAfterWarmOpen = @ \/ (s.reopenedUnstable /\ s.selected # s.stable)]

Stage(cut) ==
    /\ s.issued < MaxGeneration
    /\ s.cut[s.selected] < cut /\ cut <= s.ack
    /\ LET g == s.issued + 1 IN
       s' = [s EXCEPT !.issued = g, !.cut[g] = cut,
                      !.parent[g] = s.selected, !.bases = @ \cup {g}]

Publish(g) ==
    /\ g \in s.bases /\ s.selected < g
    /\ s.selected = s.stable \/ Variant = "stack_unstable"
    /\ Variant # "drain_before_publish" \/ s.pinned.kind = "none"
    /\ CASE Variant = "revalidate" -> s.cut[s.selected] < s.cut[g] /\ Recoverable(g)
         [] Variant = "stale_base" -> TRUE
         [] OTHER -> s.parent[g] = s.selected
    /\ s' = [s EXCEPT !.selected = g, !.possible = @ \cup {g},
                      !.stalePublished = @ \/ s.parent[g] # s.selected]

SyncSelector ==
    /\ s.selected # s.stable
    /\ s' = [s EXCEPT !.stable = s.selected, !.possible = {s.selected},
                      !.stableRoots = @ \cup {s.selected}]

WarmRestart ==
    /\ s.running
    /\ s' = [s EXCEPT !.running = FALSE,
                      !.warmDuringSwitch = @ \/ s.selected # s.stable]

PowerLoss(g) ==
    /\ g \in s.possible /\ s.powerLosses < MaxPowerLosses
    /\ s' = [s EXCEPT !.selected = g, !.stable = g, !.possible = {g},
                      !.running = FALSE, !.powerLosses = @ + 1,
                      !.stableRoots = @ \cup {g}, !.lostAt = @ \cup {g}]

Open ==
    /\ ~s.running /\ Recoverable(s.selected)
    /\ Variant # "stable_open" \/ s.selected = s.stable
    /\ s' = [s EXCEPT !.running = TRUE,
                      !.reopenedUnstable = @ \/ s.selected # s.stable]

PinBase ==
    /\ s.pinned.kind = "none" /\ Recoverable(s.selected)
    /\ s' = [s EXCEPT !.pinned = [kind |-> "base", id |-> s.selected]]

PinTail(position) ==
    /\ s.pinned.kind = "none"
    /\ position \in (s.cut[s.selected] + 1)..s.ack
    /\ position \in s.tail
    /\ s' = [s EXCEPT !.pinned = [kind |-> "tail", id |-> position]]

Finish ==
    /\ s.pinned.kind # "none"
    /\ s' = [s EXCEPT !.pinned = [kind |-> "none", id |-> 0]]

ProtectedSelectors ==
    IF Variant = "trust_warm_name" /\ s.warmDuringSwitch
    THEN {s.selected}
    ELSE {s.stable, s.selected}

ProtectedBorrow(kind, id) ==
    /\ s.pinned = [kind |-> kind, id |-> id]
    /\ ~(Variant = "forget_borrow_after_restart" /\ s.warmDuringSwitch)

ReclaimBase(g) ==
    /\ g \in s.bases \ ProtectedSelectors
    /\ ~ProtectedBorrow("base", g)
    /\ s' = [s EXCEPT !.bases = @ \ {g}]

ReclaimTail(position) ==
    /\ position \in s.tail
    /\ \A g \in ProtectedSelectors : position <= s.cut[g]
    /\ ~ProtectedBorrow("tail", position)
    /\ s' = [s EXCEPT !.tail = @ \ {position}]

Next ==
    \/ WarmRestart \/ Open \/ SyncSelector \/ Finish
    \/ \E g \in s.possible : PowerLoss(g)
    \/ s.running /\
       (\/ AppendDurably \/ PinBase
        \/ \E cut \in 1..MaxRecord : Stage(cut)
        \/ \E g \in Generations : Publish(g) \/ ReclaimBase(g)
        \/ \E position \in 1..MaxRecord : PinTail(position) \/ ReclaimTail(position))

Spec == Init /\ [][Next]_s

EveryCrashRootRecovers == \A g \in s.possible : Recoverable(g)

VisibleRootRecovers == Recoverable(s.selected)

ExactBorrowSurvives ==
    CASE s.pinned.kind = "base" -> s.pinned.id \in s.bases
      [] s.pinned.kind = "tail" -> s.pinned.id \in s.tail
      [] OTHER -> TRUE

TwoPossibleRoots == Cardinality(s.possible) <= 2

NeverWarmServesBeforeSync == ~s.reopenedUnstable

NeverRecoversWarmVoteOnPredecessor ==
    ~(s.votedAfterWarmOpen /\ s.powerLosses > 0 /\ s.selected = 0 /\ s.running)

NeverStaleCandidatePublishes == ~s.stalePublished

NeverPinsOldWhileReclaimsMiddle ==
    ~(s.stable = 2 /\ 1 \in s.stableRoots /\ s.powerLosses > 0
      /\ s.pinned = [kind |-> "base", id |-> 0]
      /\ 0 \in s.bases /\ 1 \notin s.bases /\ s.cut[1] < s.cut[2])

NeverRecoversTwoSuccessiveLosses ==
    ~(s.powerLosses = 2 /\ s.lostAt = {1, 2} /\ s.running /\ s.stable = 2 /\ s.cut[1] < s.cut[2]
      /\ 0 \notin s.bases /\ 1 \notin s.bases /\ 1 \notin s.tail)
=============================================================================
