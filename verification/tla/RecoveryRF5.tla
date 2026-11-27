---------------------------- MODULE RecoveryRF5 ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS First, Second, Lost, Replacements, ExcludeById, CommitFirst, WaitOut

Survivors == {First, Second}
Old == Survivors \cup Lost
New == Survivors \cup Replacements
Members == Old \cup New
ASSUME /\ Cardinality(Old) = 5 /\ Cardinality(New) = 5
       /\ Cardinality(Members) = 8

Majority(voters, acks) == Cardinality(voters \cap acks) >= 3
Other(s) == IF s = First THEN Second ELSE First
Max(a, b) == IF a >= b THEN a ELSE b

(* Start after the old quorum chose positions 1 and 2. Both survivors have
   them, but only one may have persisted knowledge of commit 2. A longer
   speculative tip at position 3 can rank ahead by either index or term. *)
Prefix == <<"base", "chosen">>
OldTail == Append(Prefix, "old")
OldTerm == 4
RecoveryTerm == 3
NoView == <<>>

VARIABLES logs, known, terms, writer, stage, probed, kept, cut, lease,
          connected, oldAcks, installed, newAcks, oldAfterNew, newSeen,
          lostAccepted, cutAtProbe

vars == <<logs, known, terms, writer, stage, probed, kept, cut, lease,
          connected, oldAcks, installed, newAcks, oldAfterNew, newSeen,
          lostAccepted, cutAtProbe>>

Init ==
    /\ \E better \in Survivors, peerCommit \in 1..2, longTip \in BOOLEAN:
        /\ logs = [p \in Members |->
            IF p \in Lost \/ p = better THEN Prefix
            ELSE IF p \in Survivors THEN IF longTip THEN Append(Prefix, "speculative") ELSE Prefix
            ELSE <<>>]
        /\ known = [p \in Members |->
            IF p \in Lost \/ p = better THEN 2 ELSE IF p \in Survivors THEN peerCommit ELSE 0]
        /\ terms = [p \in Members |-> IF p \in Lost THEN OldTerm
            ELSE IF p \in Survivors THEN IF longTip /\ p # better THEN 2 ELSE 1 ELSE 0]
    /\ writer = First /\ stage = "choose" /\ probed = 0 /\ kept = NoView /\ cut = 0
    /\ lease = 2 /\ connected = {}
    /\ oldAcks = {} /\ installed = {} /\ newAcks = {}
    /\ oldAfterNew = FALSE /\ newSeen = FALSE
    /\ lostAccepted = FALSE /\ cutAtProbe = 0

TipAhead(p, q) ==
    \/ terms[p] > terms[q]
    \/ /\ terms[p] = terms[q]
       /\ \/ Len(logs[p]) > Len(logs[q])
          \/ Len(logs[p]) = Len(logs[q]) /\ p = First

RanksFirst(p, q) ==
    IF CommitFirst /\ known[p] # known[q] THEN known[p] > known[q] ELSE TipAhead(p, q)

(* The writer is stopped; the other survivor may receive old traffic until
   its progress probe drains admitted appends and installs the identity fence.
   Select the eligible writer in one step with that successful probe. *)
Probe ==
    /\ stage = "choose"
    /\ \E p \in Survivors:
        /\ RanksFirst(p, Other(p))
        /\ writer' = p /\ probed' = known[Other(p)]
        /\ cutAtProbe' = Max(known[p], known[Other(p)])
    /\ stage' = "probed"
    /\ UNCHANGED <<logs, known, terms, kept, cut, lease, connected, oldAcks,
                   installed, newAcks, oldAfterNew, newSeen, lostAccepted>>

(* Lost members can form their own quorum even with both survivors absent.
   The link to either survivor can independently heal after the probe. *)
Heal(p) ==
    /\ stage # "choose" /\ p \notin connected
    /\ connected' = connected \cup {p}
    /\ UNCHANGED <<logs, known, terms, writer, stage, probed, kept, cut, lease,
                   oldAcks, installed, newAcks, oldAfterNew, newSeen, lostAccepted, cutAtProbe>>

PersistOld(p) ==
    /\ p \in Lost /\ lease > 0 /\ p \notin oldAcks
    /\ oldAcks' = oldAcks \cup {p}
    /\ logs' = [logs EXCEPT ![p] = OldTail]
    /\ UNCHANGED <<known, terms, writer, stage, probed, kept, cut, lease, connected,
                   installed, newAcks, oldAfterNew, newSeen, lostAccepted, cutAtProbe>>

(* Abstract a higher-term append or snapshot from the old leader. The
   secondary excludes it from the probe on, even while its log still
   carries the old membership; recovered copies exclude it after install. *)
OldMessage(p) ==
    /\ stage # "choose" /\ p \in connected /\ lease > 0
    /\ p # writer \/ p \in installed
    /\ ~ExcludeById
    /\ Majority(Old, oldAcks)
    /\ logs' = [logs EXCEPT ![p] = OldTail]
    /\ known' = [known EXCEPT ![p] = 3]
    /\ terms' = [terms EXCEPT ![p] = OldTerm]
    /\ lostAccepted' = TRUE
    /\ UNCHANGED <<writer, stage, probed, kept, cut, lease, connected, oldAcks,
                   installed, newAcks, oldAfterNew, newSeen, cutAtProbe>>

CatalogRecover ==
    /\ stage = "probed"
    /\ stage' = "waiting"
    /\ cut' = known[writer]
    /\ kept' = SubSeq(logs[writer], 1, cut')
    /\ UNCHANGED <<logs, known, terms, writer, probed, lease, connected, oldAcks,
                   installed, newAcks, oldAfterNew, newSeen, lostAccepted, cutAtProbe>>

Tick ==
    /\ lease > 0 /\ lease' = lease - 1
    /\ UNCHANGED <<logs, known, terms, writer, stage, probed, kept, cut, connected,
                   oldAcks, installed, newAcks, oldAfterNew, newSeen, lostAccepted, cutAtProbe>>

RecoveredLog == Append(kept, "recovery")
WriteRecovery ==
    /\ stage = "waiting" /\ (~WaitOut \/ lease = 0)
    /\ stage' = "written"
    /\ logs' = [logs EXCEPT ![writer] = RecoveredLog]
    /\ terms' = [terms EXCEPT ![writer] = RecoveryTerm]
    /\ installed' = {writer} /\ newAcks' = {writer}
    /\ UNCHANGED <<known, writer, probed, kept, cut, lease, connected, oldAcks,
                   oldAfterNew, newSeen, lostAccepted, cutAtProbe>>

Install(p) ==
    /\ stage = "written" /\ p \in New \ installed
    /\ RecoveryTerm >= terms[p]
    /\ logs' = [logs EXCEPT ![p] = RecoveredLog]
    /\ terms' = [terms EXCEPT ![p] = RecoveryTerm]
    /\ installed' = installed \cup {p} /\ newAcks' = newAcks \cup {p}
    /\ UNCHANGED <<known, writer, stage, probed, kept, cut, lease, connected, oldAcks,
                   oldAfterNew, newSeen, lostAccepted, cutAtProbe>>

ReadNew ==
    /\ stage = "written" /\ Majority(New, newAcks) /\ ~newSeen
    /\ logs[writer] = RecoveredLog
    /\ newSeen' = TRUE
    /\ UNCHANGED <<logs, known, terms, writer, stage, probed, kept, cut, lease,
                   connected, oldAcks, installed, newAcks, oldAfterNew, lostAccepted, cutAtProbe>>

ReadOld ==
    /\ Majority(Old, oldAcks) /\ lease > 0 /\ newSeen /\ ~oldAfterNew
    /\ oldAfterNew' = TRUE
    /\ UNCHANGED <<logs, known, terms, writer, stage, probed, kept, cut, lease,
                   connected, oldAcks, installed, newAcks, newSeen, lostAccepted, cutAtProbe>>

Next ==
    \/ Probe \/ CatalogRecover \/ Tick \/ WriteRecovery \/ ReadNew \/ ReadOld
    \/ \E p \in Lost: PersistOld(p)
    \/ \E p \in Survivors: Heal(p) \/ OldMessage(p)
    \/ \E p \in New: Install(p)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(Probe) /\ WF_vars(CatalogRecover) /\ WF_vars(Tick)
    /\ WF_vars(WriteRecovery) /\ WF_vars(ReadNew)
    /\ \A p \in New: WF_vars(Install(p))

TwoSurvivorsKeepTheirCommits ==
    stage \in {"waiting", "written"} =>
        /\ cut = cutAtProbe /\ cut >= probed
        /\ \A p \in Survivors: known[p] <= cut /\ SubSeq(logs[p], 1, known[p]) = SubSeq(Prefix, 1, known[p])

LostIdentitiesExcluded == ~lostAccepted
NoMixedHistory == ~oldAfterNew
ReadRequiresRecoveredQuorum ==
    newSeen => Majority(New, {p \in installed : logs[p] = RecoveredLog})
RecoveryServes == <>(newSeen /\ installed = New)

=============================================================================
