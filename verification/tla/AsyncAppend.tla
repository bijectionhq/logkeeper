----------------------------- MODULE AsyncAppend ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Leader, Followers, CountOverlay, RecoverTip, MaxCrashes, FlushIdleMarker

Voters == {Leader} \cup Followers
Last == 3
ASSUME Cardinality(Voters) = 3

VARIABLES requested, staged, durable, learned, applied, noted, marked,
          chosen, replied, down, crashes, recovery

vars == <<requested, staged, durable, learned, applied, noted, marked,
          chosen, replied, down, crashes, recovery>>
local == <<staged, durable, learned, applied, noted, marked>>

Init ==
    /\ requested = 1 /\ chosen = 1 /\ replied = 1
    /\ staged = [p \in Voters |-> 1] /\ durable = staged
    /\ learned = staged /\ applied = staged /\ noted = staged /\ marked = staged
    /\ down = {} /\ crashes = 0
    /\ recovery = [writer |-> Leader, cut |-> 0, active |-> FALSE]

Running(p) == ~recovery.active /\ p \notin down
Min(a, b) == IF a <= b THEN a ELSE b
DurableCopies(i) == {p \in Voters : durable[p] >= i}
CountedCopies(i) ==
    DurableCopies(i) \cup (IF CountOverlay /\ staged[Leader] >= i THEN {Leader} ELSE {})

Submit ==
    /\ ~recovery.active /\ requested < Last /\ requested' = requested + 1
    /\ UNCHANGED <<local, chosen, replied, down, crashes, recovery>>

Queue ==
    /\ Running(Leader) /\ staged[Leader] < requested
    /\ staged' = [staged EXCEPT ![Leader] = @ + 1]
    /\ UNCHANGED <<requested, durable, learned, applied, noted, marked,
                   chosen, replied, down, crashes, recovery>>

(* Delivery can use the in-memory overlay. The follower's WAL completion
   is a separate action, so delivery alone provides no quorum evidence. *)
Send(p) ==
    /\ Running(Leader) /\ Running(p) /\ p \in Followers
    /\ staged[p] < staged[Leader]
    /\ staged' = [staged EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<requested, durable, learned, applied, noted, marked,
                   chosen, replied, down, crashes, recovery>>

Flush(p) ==
    /\ Running(p) /\ durable[p] < staged[p]
    /\ durable' = [durable EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<requested, staged, learned, applied, noted, marked,
                   chosen, replied, down, crashes, recovery>>

Choose ==
    /\ Running(Leader) /\ chosen < requested
    /\ Cardinality(CountedCopies(chosen + 1)) >= 2
    /\ chosen' = chosen + 1
    /\ UNCHANGED <<requested, local, replied, down, crashes, recovery>>

Learn(p) ==
    /\ Running(p)
    /\ learned[p] < (IF p = Leader THEN chosen ELSE Min(durable[p], chosen))
    /\ learned' = [learned EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<requested, staged, durable, applied, noted, marked,
                   chosen, replied, down, crashes, recovery>>

Apply(p) ==
    /\ Running(p) /\ applied[p] < Min(learned[p], durable[p])
    /\ applied' = [applied EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<requested, staged, durable, learned, noted, marked,
                   chosen, replied, down, crashes, recovery>>

Reply ==
    /\ Running(Leader) /\ replied < applied[Leader] /\ replied' = replied + 1
    /\ UNCHANGED <<requested, local, chosen, down, crashes, recovery>>

Note(p) ==
    /\ Running(p) /\ noted[p] < learned[p]
    /\ noted' = [noted EXCEPT ![p] = learned[p]]
    /\ UNCHANGED <<requested, staged, durable, learned, applied, marked,
                   chosen, replied, down, crashes, recovery>>

(* save_committed only notes the index; the WAL writer adds
   Record::Committed to a later round once the local log holds the exact ID
   (stage_committed), so the marker never runs ahead of local bytes. A crash
   before that round lands leaves the old marker: staging and landing are one
   step here, since a crash between them changes nothing. *)
Mark(p) ==
    /\ Running(p) /\ marked[p] < noted[p]
    /\ noted[p] <= durable[p]
    /\ marked' = [marked EXCEPT ![p] = noted[p]]
    /\ UNCHANGED <<requested, staged, durable, learned, applied, noted,
                   chosen, replied, down, crashes, recovery>>

Crash(p) ==
    /\ Running(p) /\ crashes < MaxCrashes
    /\ down' = down \cup {p} /\ crashes' = crashes + 1
    /\ staged' = [staged EXCEPT ![p] = durable[p]]
    /\ learned' = [learned EXCEPT ![p] = marked[p]]
    /\ applied' = [applied EXCEPT ![p] = 0]
    /\ noted' = [noted EXCEPT ![p] = marked[p]]
    /\ UNCHANGED <<requested, durable, marked, chosen, replied, recovery>>

Restart(p) ==
    /\ ~recovery.active /\ p \in down
    /\ down' = down \ {p}
    /\ UNCHANGED <<requested, local, chosen, replied, crashes, recovery>>

Recover(p) ==
    /\ ~recovery.active /\ p \in down /\ Cardinality(down) >= 2
    /\ recovery' = [writer |-> p, cut |-> IF RecoverTip THEN durable[p] ELSE marked[p],
                    active |-> TRUE]
    /\ UNCHANGED <<requested, local, chosen, replied, down, crashes>>

Next ==
    \/ Submit \/ Queue \/ Choose \/ Reply
    \/ \E p \in Followers: Send(p)
    \/ \E p \in Voters:
        Flush(p) \/ Learn(p) \/ Apply(p) \/ Note(p) \/ Mark(p)
        \/ Crash(p) \/ Restart(p) \/ Recover(p)

(* FlushIdleMarker: a keeper idle since its last commit still writes the
   noted index within COMMITTED_FLUSH, in a round of its own. *)
Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(Queue) /\ WF_vars(Choose) /\ WF_vars(Reply)
    /\ \A p \in Followers: WF_vars(Send(p))
    /\ \A p \in Voters:
        /\ WF_vars(Flush(p)) /\ WF_vars(Learn(p)) /\ WF_vars(Apply(p))
        /\ WF_vars(Restart(p)) /\ WF_vars(Note(p))
        /\ (FlushIdleMarker => WF_vars(Mark(p)))

ChosenHasDurableQuorum == Cardinality(DurableCopies(chosen)) >= 2
AppliedHasLocalBytes == \A p \in Voters: applied[p] <= Min(durable[p], chosen)
MarkerHasLocalCommittedBytes == \A p \in Voters: marked[p] <= Min(durable[p], chosen)
(* The recovery keeps only records known committed: no uncommitted record of
   the writer survives into the recovered history (fc4855ed, finding 5). *)
RecoveryKeepsOnlyCommitted == recovery.active => recovery.cut <= chosen

(* The fixed leader can resume after a finite crash budget. The recovery
   alternative may report the acknowledged suffix beyond the selected cut
   lost, including when a crash preceded a lazy marker flush. *)
RequestsSettle == \A i \in 1..Last: (requested >= i) ~> (replied >= i \/ recovery.active)
MarkersCatchUp == \A p \in Voters: \A i \in 1..Last:
    (learned[p] >= i /\ durable[p] >= i) ~> (marked[p] >= i \/ recovery.active)

=============================================================================
