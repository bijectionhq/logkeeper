------------------------- MODULE StandingCustody -------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS MaxRecords, MaxWindows, MaxReads, MaxRestarts, Capacity, Variant, Policy, Link, Rotation
VARIABLE s

Windows == 1..MaxWindows
Readers == 1..MaxReads
Root(cut) == cut
Tail(position) == MaxRecords + position
Dependencies(base, cut) == {Root(base)} \cup {Tail(i) : i \in (base + 1)..cut}
EmptyRead == [state |-> "empty", invoked |-> 0, floor |-> 0, window |-> 0,
              entered |-> 0, completed |-> 0, received |-> 0, session |-> 0, stopped |-> FALSE]
EmptyWindow == [phase |-> "unused", root |-> 0, cut |-> 0,
                session |-> 0, fenced |-> FALSE]
WindowAt(base, cut, session) ==
    [EmptyWindow EXCEPT !.phase = "open", !.root = base, !.cut = cut, !.session = session]
Charged(w) == w.phase \in {"staged", "open", "sealed"}
Expenses == {i \in Windows : Charged(s.windows[i])}
AtOpen == {i \in Windows : s.windows[i].phase = "open"}
Staged == {i \in Windows : s.windows[i].phase = "staged"}
InUse(i) == {r \in Readers : s.reads[r].state = "using" /\ s.reads[r].window = i}
LiveView(position) == s.terminal = 0 \/ position < s.terminal
JournalHead == IF s.terminal = 0 THEN s.committed ELSE s.terminal

Init ==
    s = [committed |-> 0, applied |-> 0, terminal |-> 0, requested |-> FALSE,
         root |-> 0, present |-> {0}, session |-> 0, up |-> TRUE, issued |-> 1, admissionGap |-> FALSE,
         windows |-> [i \in Windows |-> IF i = 1 THEN WindowAt(0, 0, 0) ELSE EmptyWindow],
         reads |-> [r \in Readers |-> EmptyRead]]

Append ==
    /\ s.terminal = 0 /\ s.committed < MaxRecords
    /\ s' = [s EXCEPT !.committed = @ + 1, !.present = @ \cup {Tail(s.committed + 1)}]

Apply ==
    /\ s.up /\ s.applied < JournalHead
    /\ s' = [s EXCEPT !.applied = JournalHead]

Publish ==
    /\ LiveView(s.applied) /\ s.root < s.applied
    /\ s' = [s EXCEPT !.root = s.applied, !.present = @ \cup {Root(s.applied)}]

Register ==
    /\ s.up /\ s.terminal = 0 /\ ~s.requested /\ s.issued < MaxWindows
    /\ IF Rotation = "stage_first" THEN Staged = {} ELSE AtOpen = {}
    /\ Cardinality(IF Variant = "count_open_only" THEN AtOpen ELSE Expenses) < Capacity
    /\ Dependencies(s.root, s.applied) \subseteq s.present
    /\ LET candidate == WindowAt(s.root, s.applied, s.session)
       IN s' = [s EXCEPT !.issued = @ + 1, !.windows[s.issued + 1] =
                   IF Rotation = "stage_first" THEN [candidate EXCEPT !.phase = "staged"] ELSE candidate]

Activate(i) ==
    /\ i \in Staged /\ s.up /\ s.windows[i].session = s.session
    /\ \A other \in AtOpen : s.windows[other].session = s.session
    /\ s' = [s EXCEPT !.windows = [j \in Windows |->
                          IF j = i THEN [@[j] EXCEPT !.phase = "open"]
                          ELSE IF j \in AtOpen THEN [@[j] EXCEPT !.phase = "sealed"] ELSE @[j]]]

Invoke(reader) ==
    /\ s.reads[reader].state = "empty"
    /\ s' = [s EXCEPT !.reads[reader].state = "invoked", !.reads[reader].invoked = JournalHead]

Observe(reader) ==
    /\ s.reads[reader].state = "invoked"
    /\ s' = [s EXCEPT !.reads[reader].state = "ready", !.reads[reader].floor = JournalHead]

Eligible(reader, i) ==
    LET w == s.windows[i]
        r == s.reads[reader]
    IN /\ s.up /\ w.phase = "open"
       /\ w.session = s.session \/ Variant = "reuse_after_restart"
       /\ r.floor <= w.cut \/
           (Variant = "stream_lsn_floor" /\ r.floor = s.terminal /\ w.cut = s.committed)

Inspect(reader, i) ==
    /\ Variant = "cached_gate" /\ s.reads[reader].state = "ready" /\ Eligible(reader, i)
    /\ s' = [s EXCEPT !.reads[reader].state = "looked", !.reads[reader].window = i]

Admit(reader, i) ==
    /\ IF Variant = "cached_gate" THEN
           s.reads[reader].state = "looked" /\ s.reads[reader].window = i
       ELSE s.reads[reader].state = "ready" /\ Eligible(reader, i)
    /\ s' = [s EXCEPT !.reads[reader].state = "using", !.reads[reader].window = i,
                       !.reads[reader].entered = JournalHead, !.reads[reader].session = s.session]

Finish(reader) ==
    /\ s.reads[reader].state = "using"
       \/ (Variant = "late_success" /\ s.reads[reader].state = "stopped")
    /\ s' = [s EXCEPT !.reads[reader].state = "finished", !.reads[reader].completed = JournalHead]

Deliver(reader) ==
    /\ s.reads[reader].state = "finished"
    /\ Variant # "deliver_after_release" \/ s.windows[s.reads[reader].window].phase = "released"
    /\ s' = [s EXCEPT !.reads[reader].state = "answered", !.reads[reader].received = JournalHead]

Request ==
    /\ ~s.requested
    /\ s' = [s EXCEPT !.requested = TRUE]

Retire ==
    /\ s.requested /\ s.terminal = 0
    /\ Policy # "before_terminal" \/
       (AtOpen = {} /\ (Staged = {} \/ Variant = "ignore_staged_gate"))
    /\ s' = [s EXCEPT !.terminal = s.committed + 1]

Seal(i) ==
    /\ Link /\ i \in AtOpen \cup Staged
    /\ s' = [s EXCEPT !.windows[i].phase = "sealed", !.admissionGap = @ \/ i \in AtOpen]

Fence(i) ==
    /\ Link /\ s.windows[i].phase = "sealed" /\ ~s.windows[i].fenced
    /\ s' = [s EXCEPT !.windows[i].fenced = TRUE,
                       !.reads = [r \in Readers |-> IF r \in InUse(i)
                           THEN [@[r] EXCEPT !.state = "stopped", !.stopped = TRUE] ELSE @[r]]]

Release(i) ==
    /\ s.windows[i].phase = "sealed"
    /\ s.windows[i].fenced \/
        (InUse(i) = {} /\ s.up /\ s.windows[i].session = s.session) \/
        (Variant = "forget_restart" /\ s.up /\ s.windows[i].session # s.session)
    /\ s' = [s EXCEPT !.windows[i].phase = "released"]

Kill ==
    /\ s.up /\ s.session < MaxRestarts
    /\ s' = [s EXCEPT !.up = FALSE, !.session = @ + 1, !.admissionGap = TRUE]

Restart ==
    /\ ~s.up
    /\ s' = [s EXCEPT !.up = TRUE]

Reclaim(extent) ==
    /\ extent \in s.present
    /\ s.terminal > 0 \/ extent < Root(s.root) \/
        (extent > MaxRecords /\ extent <= Tail(s.root))
    /\ \A i \in Windows :
        LET w == s.windows[i] IN
           (~Charged(w) \/ (Variant = "omit_suffix" /\ extent > MaxRecords)
             \/ (Variant = "unprotected_stage" /\ w.phase = "staged")
             \/ extent \notin Dependencies(w.root, w.cut))
    /\ s' = [s EXCEPT !.present = @ \ {extent}]

SealSome == \E i \in Windows : Seal(i)
FenceSome == \E i \in Windows : Fence(i)
ReleaseSome == \E i \in Windows : Release(i)
Next ==
    \/ Append \/ Apply \/ Publish \/ Register \/ Request \/ Retire \/ Kill \/ Restart \/ SealSome
    \/ FenceSome \/ ReleaseSome
    \/ \E i \in Windows : Activate(i)
    \/ \E r \in Readers : Invoke(r) \/ Observe(r) \/ Finish(r) \/ Deliver(r)
        \/ \E i \in Windows : Inspect(r, i) \/ Admit(r, i)
    \/ \E extent \in s.present : Reclaim(extent)

Spec == Init /\ [][Next]_s
FairClose == Spec /\ WF_s(Request) /\ WF_s(SealSome) /\ WF_s(Retire)
FairSettle == FairClose /\ WF_s(FenceSome) /\ WF_s(ReleaseSome)

ExactBorrowProtected ==
    \A r \in Readers : s.reads[r].state = "using" =>
        LET w == s.windows[s.reads[r].window] IN
            Charged(w) /\ Dependencies(w.root, w.cut) \subseteq s.present

ChargedCoverage ==
    \A i \in Expenses : Dependencies(s.windows[i].root, s.windows[i].cut) \subseteq s.present

FreshLiveCut ==
    \A r \in Readers : s.reads[r].state \in {"using", "finished", "answered"} =>
        LET w == s.windows[s.reads[r].window] IN
            s.reads[r].invoked <= w.cut /\ w.cut <= JournalHead /\ LiveView(w.cut)

OriginalSession ==
    \A r \in Readers : s.reads[r].state \in {"using", "finished", "answered", "stopped"} =>
        s.reads[r].session = s.windows[s.reads[r].window].session

StoppedWorkCannotFinish ==
    \A r \in Readers : s.reads[r].stopped => s.reads[r].state = "stopped"

BoundedCustodyCapacity == Cardinality(Expenses) <= Capacity
OnlyOneOpenGate == Cardinality(AtOpen) <= 1
NoAdmissionAfterTerminal ==
    \A r \in Readers : s.reads[r].state \in {"using", "finished", "answered", "stopped"} =>
        LiveView(s.reads[r].entered)

NeverAdmitsOverlapAfterTerminal ==
    ~(s.terminal > 0 /\ \E r \in Readers : s.reads[r].state = "answered"
        /\ s.reads[r].invoked < s.terminal /\ s.reads[r].entered >= s.terminal)

NeverFinishesAfterReplacement ==
    ~ (\E r \in Readers : s.reads[r].state = "finished" /\
         LET w == s.windows[s.reads[r].window] IN w.root < s.root /\ w.root < w.cut)

NeverSharesWindow ==
    ~ (\E i \in Windows : Cardinality(InUse(i)) > 1 /\ Cardinality(Expenses) = 1)

NeverServesSuccessorWhileOldCharged ==
    ~ (s.issued = MaxWindows /\ \E i, j \in Expenses : i # j /\
         InUse(i) # {} /\ InUse(j) # {} /\ s.windows[i].session < s.windows[j].session)

NeverServesBothCutsWithoutGateGap ==
    ~(~s.admissionGap /\ \E i \in AtOpen, j \in Expenses :
         i # j /\ InUse(i) # {} /\ InUse(j) # {}
         /\ s.windows[j].cut < s.windows[i].cut)

NeverSettlesCrashedBorrow ==
    ~(\E r \in Readers : s.reads[r].state = "stopped" /\
       LET w == s.windows[s.reads[r].window] IN
          w.session < s.session /\ w.phase = "released" /\ Root(w.root) \notin s.present)

NeverDeliversPreterminalFinishAfterRelease ==
    ~(s.terminal > 0 /\ \E r \in Readers : s.reads[r].state = "answered"
        /\ s.reads[r].completed < s.terminal /\ s.reads[r].received >= s.terminal
        /\ s.windows[s.reads[r].window].phase = "released")

TerminalEventually == <>(s.terminal > 0)
RightsEventuallySettled == <>(s.terminal > 0 /\ Expenses = {})

=============================================================================
