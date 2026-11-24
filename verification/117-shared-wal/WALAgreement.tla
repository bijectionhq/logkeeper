------------------------------ MODULE WALAgreement ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Layout, Fault
Groups == {1, 2}
Voters == {1, 2, 3}
Lane == Voters \X Groups
Empty == [promise |-> 0, ballot |-> 0, prefix |-> <<>>]

VARIABLES phase, disk, queue, replies, proposal, chosen, down, erased, syncs, batchIntact
vars == <<phase, disk, queue, replies, proposal, chosen, down, erased, syncs, batchIntact>>

Init ==
    /\ phase = 1
    /\ disk = [i \in Lane |-> Empty]
    /\ queue = [v \in Voters |-> {}]
    /\ replies = {}
    /\ proposal = [g \in Groups |-> <<>>]
    /\ chosen = [g \in Groups |-> <<>>]
    /\ down = {}
    /\ erased = FALSE
    /\ syncs = 0
    /\ batchIntact = TRUE

Ballot == IF phase <= 2 THEN 1 ELSE 2
Preparing == phase \in {1, 3}
RoundVoters == IF Ballot = 1 THEN {1, 2} ELSE {2, 3}
Required == RoundVoters \X Groups

\* This schedule has at most one previous ballot with an accepted chain.
\* Its largest reported accepted rank is the only possible nonempty seed.
Seed(g) ==
    IF disk[<<2, g>>].ballot >= disk[<<3, g>>].ballot
    THEN disk[<<2, g>>].prefix ELSE disk[<<3, g>>].prefix

ProposeAt(v, g) ==
    IF Fault = "split-ballot" /\ Ballot = 2 /\ v = 3
    THEN <<g+2>> ELSE proposal[g]

Write(v, g) ==
    /\ phase \in 1..4
    /\ v \in RoundVoters \ down
    /\ <<v, g>> \notin replies
    /\ \A row \in queue[v] : row.group # g
    /\ LET saved == disk[<<v, g>>] IN
        /\ IF Preparing THEN saved.promise < Ballot
           ELSE saved.promise = Ballot /\ saved.ballot < Ballot
        /\ queue' = [queue EXCEPT ![v] = @ \cup
              {[group |-> g, image |-> IF Preparing
                   THEN [saved EXCEPT !.promise = Ballot]
                   ELSE [promise |-> Ballot, ballot |-> Ballot, prefix |-> ProposeAt(v, g)]]}]
    /\ UNCHANGED <<phase, disk, replies, proposal, chosen, down, erased, syncs, batchIntact>>

Sync(v, g) ==
    /\ \E row \in queue[v] : row.group = g
    /\ LET covered == IF Layout = "shared" /\ Fault # "no-coalesce" THEN queue[v]
                      ELSE {row \in queue[v] : row.group = g}
       IN /\ disk' = [i \in Lane |-> IF i[1] = v /\ (\E row \in covered : row.group = i[2])
                  THEN (CHOOSE row \in covered : row.group = i[2]).image ELSE disk[i]]
          /\ queue' = [queue EXCEPT ![v] = @ \ covered]
          /\ syncs' = syncs + (IF Fault = "double-barrier" THEN 2 ELSE 1)
          /\ batchIntact' = (batchIntact /\
              (Layout # "shared" \/ Cardinality(covered) = Cardinality(queue[v])))
    /\ UNCHANGED <<phase, replies, proposal, chosen, down, erased>>

Reply(v, g) ==
    /\ phase \in 1..4
    /\ v \in RoundVoters \ down
    /\ <<v, g>> \notin replies
    /\ IF Preparing THEN disk[<<v, g>>].promise = Ballot
       ELSE disk[<<v, g>>].ballot = Ballot
    /\ replies' = replies \cup {<<v, g>>}
    /\ UNCHANGED <<phase, disk, queue, proposal, chosen, down, erased, syncs, batchIntact>>

Advance ==
    /\ phase \in 1..4
    /\ replies = Required
    /\ phase' = phase + 1
    /\ replies' = {}
    /\ proposal' = IF Preparing THEN
        [g \in Groups |-> IF Ballot = 1 THEN <<g>> ELSE Append(Seed(g), g+2)]
        ELSE proposal
    /\ chosen' = IF Preparing THEN chosen ELSE
         [g \in Groups |-> Append(chosen[g], disk[<<2, g>>].prefix)]
    /\ UNCHANGED <<disk, queue, down, erased, syncs, batchIntact>>

LoseAZ ==
    /\ phase = 3 /\ down = {}
    /\ down' = {1}
    /\ UNCHANGED <<phase, disk, queue, replies, proposal, chosen, erased, syncs, batchIntact>>

\* Outside the one-failure premise. Voter 2 returns blank under its old identity.
EmptyRejoin ==
    /\ Fault = "empty-rejoin" /\ phase = 3 /\ down = {1}
    /\ ~erased /\ replies = {} /\ \A v \in Voters : queue[v] = {}
    /\ disk[<<2, 1>>].promise = 1 /\ disk[<<3, 1>>].promise = 0
    /\ disk' = [i \in Lane |-> IF i[1] = 2 THEN Empty ELSE disk[i]]
    /\ erased' = TRUE
    /\ UNCHANGED <<phase, queue, replies, proposal, chosen, down, syncs, batchIntact>>

Next == (\E v \in Voters, g \in Groups : Write(v,g) \/ Sync(v,g) \/ Reply(v,g))
        \/ Advance \/ LoseAZ \/ EmptyRejoin
Spec == Init /\ [][Next]_vars

Prefix(x,y) == Len(x) <= Len(y) /\ x = SubSeq(y, 1, Len(x))
PrefixAgreement == \A g \in Groups : \A i,j \in 1..Len(chosen[g]) :
    Prefix(chosen[g][i], chosen[g][j]) \/ Prefix(chosen[g][j], chosen[g][i])
QuorumAtOneBallot ==
    phase \notin {2,4} \/
    \A g \in Groups : \A v,w \in RoundVoters :
        <<v,g>> \in replies /\ <<w,g>> \in replies =>
            disk[<<v,g>>].prefix = disk[<<w,g>>].prefix

ChangedMajorityWitness == ~(phase = 5 /\ down = {1} /\
    \A g \in Groups : chosen[g] = << <<g>>, <<g, g+2>> >>)
OneCoveringSync == batchIntact
SyncCount == phase = 5 => syncs \in (IF Layout = "shared" THEN 8..16 ELSE {16})
BatchedQuorumWitness == ~(phase = 5 /\ down = {1} /\ syncs = 8)
=============================================================================
