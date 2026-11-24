------------------------------- MODULE VoterWAL -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Layout, Fault
Groups == {1, 2}
Files == IF Layout = "shared" THEN {0} ELSE Groups
File(g) == IF Layout = "shared" THEN 0 ELSE g
Empty == [turn |-> 0, promise |-> 0, ballot |-> 0, prefix |-> <<>>]
NoFrame == [group |-> 0, image |-> Empty]

\* A frame contains the whole abstract acceptor image. The turn is a per-group
\* sequence number and the group is authenticated together with the image.
ImageAfter(g, image) ==
    CASE image.turn = 0 -> [Empty EXCEPT !.turn = 1, !.promise = 1]
      [] image.turn = 1 -> [image EXCEPT !.turn = 2, !.ballot = 1, !.prefix = <<g>>]
      [] image.turn = 2 -> [image EXCEPT !.turn = 3, !.promise = 2]
      [] image.turn = 3 -> [image EXCEPT !.turn = 4, !.ballot = 2, !.prefix = <<g, g>>]

VARIABLES log, fence, current, awaiting, replies, torn, batch, crashFacts, quarantined, full
vars == <<log, fence, current, awaiting, replies, torn, batch, crashFacts, quarantined, full>>

Init ==
    /\ log = [f \in Files |-> <<>>]
    /\ fence = [f \in Files |-> 0]
    /\ current = [g \in Groups |-> Empty]
    /\ awaiting = [g \in Groups |-> NoFrame]
    /\ replies = {}
    /\ torn = {}
    /\ batch = FALSE
    /\ crashFacts = {}
    /\ quarantined = {}
    /\ full = {}

RECURSIVE LastImage(_, _, _, _)
LastImage(frames, n, g, swap) ==
    IF n = 0 THEN Empty
    ELSE LET row == frames[n] IN
        IF (IF swap THEN 3 - row.group ELSE row.group) = g
        THEN row.image ELSE LastImage(frames, n - 1, g, swap)

Covered(row) ==
    LET f == File(row.group) IN
        \E i \in 1..fence[f] : log[f][i] = row

Write(g) ==
    /\ g \notin (quarantined \cup full)
    /\ current[g].turn < 4
    /\ awaiting[g] = NoFrame
    /\ LET image == ImageAfter(g, current[g])
           row == [group |-> g, image |-> image]
       IN /\ log' = [log EXCEPT ![File(g)] = Append(@, row)]
          /\ current' = [current EXCEPT ![g] = image]
          /\ awaiting' = [awaiting EXCEPT ![g] = row]
    /\ UNCHANGED <<fence, replies, torn, batch, crashFacts, quarantined, full>>

Sync(f) ==
    /\ fence[f] < Len(log[f])
    /\ fence' = [fence EXCEPT ![f] = Len(log[f])]
    /\ batch' = (batch \/
        (\A g \in Groups : \E i \in (fence[f]+1)..Len(log[f]) : log[f][i].group = g))
    /\ UNCHANGED <<log, current, awaiting, replies, torn, crashFacts, quarantined, full>>

IsPromise(row) == row.image.turn \in {1, 3}

Reply(g) ==
    /\ g \notin quarantined
    /\ awaiting[g] # NoFrame
    /\ LET row == awaiting[g] IN
        /\ Covered(row)
           \/ (Fault = "early-promise" /\ IsPromise(row))
           \/ (Fault = "early-accept" /\ ~IsPromise(row))
        /\ replies' = replies \cup {row}
    /\ awaiting' = [awaiting EXCEPT ![g] = NoFrame]
    /\ UNCHANGED <<log, fence, current, torn, batch, crashFacts, quarantined, full>>

BothReplied(wantsPromise) ==
    \A g \in Groups : \E row \in replies : row.group = g /\ IsPromise(row) = wantsPromise

Crash ==
    /\ torn = {}
    /\ \E f \in Files : fence[f] < Len(log[f])
    /\ LET cut == [f \in Files |->
           IF Fault = "cross-frontier" /\ Layout = "shared"
              /\ fence[f] \in 1..(Len(log[f])-1)
           THEN IF log[f][fence[f]].group # log[f][fence[f]+1].group
                THEN fence[f]-1 ELSE fence[f]
           ELSE fence[f]]
       IN /\ torn' = {g \in Groups : \E f \in Files :
                  \E i \in (cut[f]+1)..Len(log[f]) : log[f][i].group = g}
          /\ fence' = cut
          /\ log' = [f \in Files |-> SubSeq(log[f], 1, cut[f])]
          /\ current' = [g \in Groups |-> IF g \in quarantined THEN Empty
                ELSE LastImage(log[File(g)], cut[File(g)], g,
                               Fault = "wrong-group" /\ Layout = "shared")]
    /\ awaiting' = [g \in Groups |-> NoFrame]
    /\ crashFacts' = {fact \in {"accepted", "batched-promises"} :
          IF fact = "accepted" THEN BothReplied(FALSE) ELSE batch /\ BothReplied(TRUE)}
    /\ UNCHANGED <<replies, batch, quarantined, full>>

\* A scoped integrity or quota failure can make that scope unavailable.
\* With a trusted frame boundary, quarantine never truncates a neighbour.
ScopedFailure(g, reason) ==
    /\ g \notin (quarantined \cup full)
    /\ \E i \in 1..fence[File(g)] : log[File(g)][i].group = g
    /\ current' = IF reason = "corrupt" THEN [current EXCEPT ![g] = Empty] ELSE current
    /\ quarantined' = IF reason = "corrupt" THEN quarantined \cup {g} ELSE quarantined
    /\ full' = IF reason = "quota" THEN full \cup {g} ELSE full
    /\ fence' = IF Layout = "shared" /\
          ((reason = "corrupt" /\ Fault = "global-truncate") \/
           (reason = "quota" /\ Fault = "quota-evicts-neighbour"))
          THEN [f \in Files |-> 0] ELSE fence
    /\ UNCHANGED <<log, awaiting, replies, torn, batch, crashFacts>>

Next ==
    (\E g \in Groups : Write(g) \/ Reply(g) \/
        ScopedFailure(g, "corrupt") \/ ScopedFailure(g, "quota"))
    \/ (\E f \in Files : Sync(f))
    \/ Crash

Spec == Init /\ [][Next]_vars

PromiseDurable == \A row \in replies : IsPromise(row) => Covered(row)
AcceptDurable == \A row \in replies : ~IsPromise(row) => Covered(row)
ExactDemux == \A g \in Groups :
    current[g] = IF g \in quarantined THEN Empty
                 ELSE LastImage(log[File(g)], Len(log[File(g)]), g, FALSE)
IsolatedCoverage == LET blocked == quarantined \cup full IN
    \A row \in replies : row.group \notin blocked /\ blocked # {} => Covered(row)

\* Deliberately false invariants are reachability assertions.
WALWitness == ~("accepted" \in crashFacts)
TwoGroupTearWitness == ~(torn = Groups /\ "batched-promises" \in crashFacts)
HasLatestNeighbourReply ==
    \E row \in replies : row.group = 2 /\ row.image.turn = 4
QuotaWitness == ~(full = {1} /\ HasLatestNeighbourReply)
QuarantineWitness == ~(quarantined = {1} /\ HasLatestNeighbourReply)
=============================================================================
