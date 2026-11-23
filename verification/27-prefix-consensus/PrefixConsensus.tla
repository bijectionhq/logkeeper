---------------------------- MODULE PrefixConsensus ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Variant, Scenario, MaxBallot, MaxDepth
VARIABLE s

Voters == 1..3
Ballots == 1..MaxBallot
Quorums == {quorum \in SUBSET Voters : Cardinality(quorum) = 2}
EmptyVote == [ballot |-> 0, history |-> <<>>]
NoReply == [ready |-> FALSE, vote |-> EmptyVote]

Init ==
    s = [promised |-> [v \in Voters |-> 0],
         accepted |-> [v \in Voters |-> EmptyVote],
         replies |-> [b \in Ballots |-> [v \in Voters |-> NoReply]],
         elected |-> {}, issued |-> [b \in Ballots |-> <<>>],
         seeds |-> [b \in Ballots |-> <<>>],
         voted |-> [b \in Ballots |-> [v \in Voters |-> 0]],
         lostPromise |-> FALSE, receipt |-> 0]

Chosen(b, size) ==
    \E q \in Quorums : \A v \in q : s.voted[b][v] >= size

PrepareSchedule(ballot, voter) ==
    CASE Scenario = "general" -> TRUE
      [] Scenario = "forked_tail" ->
           (CASE ballot = 1 -> voter \in {1, 2}
             [] ballot = 2 -> s.voted[1][1] = 2 /\ voter \in {2, 3}
             [] ballot = 3 -> Chosen(2, 1) /\ voter \in {1, 2})
      [] OTHER ->
           (CASE ballot = 1 -> voter \in {1, 2}
             [] ballot = 2 -> s.voted[1][1] = 1 /\ voter \in {2, 3}
             [] ballot = 3 -> s.voted[2][2] = 1 /\ voter \in {1, 3}
             [] ballot = 4 -> s.voted[3][3] = 1 /\ voter \in {1, 2})

AppendSchedule(ballot, command) ==
    CASE Scenario = "general" -> TRUE
      [] Scenario = "forked_tail" ->
           (CASE ballot = 1 -> command = 1
             [] ballot = 2 -> command = 2 /\ Len(s.issued[2]) = 0
             [] ballot = 3 -> command = 2)
      [] OTHER -> (ballot = 1 /\ command = 1) \/ (ballot = 2 /\ command = 2)

VoteSchedule(ballot, voter) ==
    CASE Scenario = "general" -> TRUE
      [] Scenario = "forked_tail" ->
           (CASE ballot = 1 -> voter = 1
             [] ballot = 2 -> voter \in {2, 3}
             [] ballot = 3 -> voter \in {1, 2})
      [] OTHER ->
           (CASE ballot < 4 -> voter = ballot
             [] ballot = 4 -> voter \in {1, 2})

Prepare(ballot, voter) ==
    /\ PrepareSchedule(ballot, voter)
    /\ ballot \notin s.elected
    /\ s.promised[voter] < ballot
    /\ ~s.replies[ballot][voter].ready
    /\ s' = [s EXCEPT !.promised[voter] = ballot,
          !.replies[ballot][voter] = [ready |-> TRUE,
            vote |-> IF Variant = "promote_promise" /\ Len(s.accepted[voter].history) = 0
                      THEN [ballot |-> ballot, history |-> <<>>]
                      ELSE s.accepted[voter]]]

AtLeastAsRecent(best, other) ==
    CASE Variant = "length_only" -> Len(best.history) >= Len(other.history)
      [] Variant = "ballot_only" -> best.ballot >= other.ballot
      [] OTHER ->
          best.ballot > other.ballot \/
            (best.ballot = other.ballot /\ Len(best.history) >= Len(other.history))

Elect(ballot, quorum, source) ==
    /\ ballot \notin s.elected /\ source \in quorum
    /\ \A voter \in quorum : s.replies[ballot][voter].ready
    /\ LET picked == s.replies[ballot][source].vote IN
       /\ \A voter \in quorum : AtLeastAsRecent(picked, s.replies[ballot][voter].vote)
       /\ s' = [s EXCEPT !.elected = @ \cup {ballot},
             !.issued[ballot] = picked.history, !.seeds[ballot] = picked.history]

Extend(ballot, command) ==
    /\ AppendSchedule(ballot, command)
    /\ ballot \in s.elected /\ Len(s.issued[ballot]) < MaxDepth
    /\ s' = [s EXCEPT !.issued[ballot] = Append(@, command)]

Accept(ballot, voter, size) ==
    /\ VoteSchedule(ballot, voter)
    /\ ballot \in s.elected /\ ballot >= s.promised[voter]
    /\ Len(s.seeds[ballot]) <= size /\ size <= Len(s.issued[ballot])
    /\ s.voted[ballot][voter] < size
    /\ s' = [s EXCEPT !.promised[voter] = ballot,
          !.accepted[voter] = [ballot |-> ballot, history |-> SubSeq(s.issued[ballot], 1, size)],
          !.voted[ballot][voter] = size]

Restart(voter) ==
    /\ Variant = "lose_promise" /\ ~s.lostPromise
    /\ s.accepted[voter].ballot < s.promised[voter]
    /\ s' = [s EXCEPT !.promised[voter] = s.accepted[voter].ballot, !.lostPromise = TRUE]

FirstCommand(ballot) == IF Len(s.issued[ballot]) = 0 THEN 0 ELSE s.issued[ballot][1]

MixedValue(command) ==
    \E q \in Quorums :
        \A v \in q : \E b \in Ballots :
            s.voted[b][v] > 0 /\ FirstCommand(b) = command

Certify(command) ==
    /\ Scenario = "mixed_receipt" /\ s.receipt = 0
    /\ IF Variant = "aggregate_votes"
       THEN MixedValue(command) /\ \A b \in Ballots : ~Chosen(b, 1)
       ELSE \E b \in Ballots : Chosen(b, 1) /\ FirstCommand(b) = command
    /\ s' = [s EXCEPT !.receipt = command]

Next ==
    \/ \E b \in Ballots, v \in Voters : Prepare(b, v)
    \/ \E b \in Ballots, q \in Quorums : \E v \in q : Elect(b, q, v)
    \/ \E b \in Ballots, command \in {1, 2} : Extend(b, command)
    \/ \E b \in Ballots, v \in Voters, size \in 1..MaxDepth : Accept(b, v, size)
    \/ \E v \in Voters : Restart(v)
    \/ \E command \in {1, 2} : Certify(command)

Spec == Init /\ [][Next]_s

IsPrefix(earlier, later) ==
    Len(earlier) <= Len(later) /\ SubSeq(later, 1, Len(earlier)) = earlier

AllChosenPrefixesAgree ==
    \A first, second \in Ballots, n, m \in 1..MaxDepth :
        Chosen(first, n) /\ Chosen(second, m) =>
        LET x == SubSeq(s.issued[first], 1, n)
            y == SubSeq(s.issued[second], 1, m)
        IN IsPrefix(x, y) \/ IsPrefix(y, x)

NewBallotReinheritsChosen ==
    \A first, next \in Ballots, n \in 1..MaxDepth :
        first < next /\ Chosen(first, n) /\ next \in s.elected =>
        IsPrefix(SubSeq(s.issued[first], 1, n), s.seeds[next])

NeverFinishesWithLongerDivergentMinority ==
    ~(MaxBallot >= 3 /\ MaxDepth >= 2 /\ s.seeds[3] = <<2>> /\
      s.issued[1] = <<1, 1>> /\ s.issued[2] = <<2>> /\
      ~Chosen(1, 1) /\ Chosen(2, 1) /\ Chosen(3, 2))

NeverAdoptsMinority ==
    ~(MaxBallot >= 2 /\ \E ballot \in Ballots \ {1} :
        Len(s.seeds[ballot]) > 0 /\ \A older \in 1..(ballot - 1) : ~Chosen(older, 1))

NeverHasMixedWithoutSameBallot ==
    ~((\E command \in {1, 2} : MixedValue(command)) /\ \A ballot \in Ballots : ~Chosen(ballot, 1))

ReceiptAgreesWithDecisions ==
    s.receipt # 0 => \A b \in Ballots : Chosen(b, 1) => s.receipt = FirstCommand(b)

NeverCertifiesFinalDecision == s.receipt = 0
=============================================================================
