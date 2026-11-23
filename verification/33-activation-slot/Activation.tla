----------------------------- MODULE Activation -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Media, Variant, Ballots, Schedule, Capacity
VARIABLE s

Voters == 1..3
Terms == 1..Ballots
Seeds == 1..2
Empty == [ballot |-> 0, seed |-> 0]
Absent == [ballot |-> Ballots + 1, seed |-> 0]
Available == Voters \ {s.failed}
Enough(voters) == Cardinality(voters) >= 2
Focused == Schedule # "general"

Init ==
    s = [term |-> 0, failed |-> 0, restored |-> FALSE, requested |-> FALSE, learned |-> {},
         promises |-> [v \in Voters |-> 0], latest |-> [v \in Voters |-> Empty],
         replies |-> [b \in Terms |-> [v \in Voters |-> Absent]],
         proposed |-> [b \in Terms |-> 0],
         voted |-> [b \in Terms |-> [seed \in Seeds |-> {}]],
         copies |-> [v \in Voters |-> {}], ready |-> [v \in Voters |-> {}],
         backing |-> [seed \in Seeds |-> {}]]

Acceptors(ballot, seed) == s.voted[ballot][seed]
Chosen(seed) == \E b \in Terms : Enough(Acceptors(b, seed))
KnownChoices == {seed \in Seeds : Chosen(seed)}
Readable(seed) == seed = 2 \/ s.failed # 1 \/ \E v \in Available : seed \in s.copies[v]
LocalHolders(seed) == {v \in Available : s.latest[v].seed = seed /\ seed \in s.copies[v]}
Protected(seed) == Enough(s.backing[seed])

MayBegin(ballot) ==
    CASE ~Focused -> TRUE
      [] Schedule = "report_then_loss" -> ballot < 3 \/ s.failed > 0
      [] Schedule = "divergent_holders" ->
            ballot = 1 \/ (ballot = 2 /\ 1 \in Acceptors(1, 1)) \/ (ballot = 3 /\ s.failed > 0)
      [] OTHER -> ballot = 1 \/ s.failed > 0

Begin ==
    /\ s.term < Ballots
    /\ IF s.term = 0 THEN TRUE ELSE s.proposed[s.term] # 0
    /\ MayBegin(s.term + 1)
    /\ Variant # "no_new_ballot_after_loss" \/ s.term < 2
    /\ s' = [s EXCEPT !.term = @ + 1]

Prepare(ballot, voter) ==
    /\ voter \in Available /\ ballot <= s.term /\ s.promises[voter] < ballot
    /\ Schedule # "divergent_holders" \/ ballot # 2 \/ voter # 1
    /\ s' = [s EXCEPT !.promises[voter] = ballot, !.replies[ballot][voter] = s.latest[voter]]

Reports(ballot, voters) == {s.replies[ballot][v] : v \in voters}
Highest(reports, seed) ==
    LET real == reports \ {Empty} IN
    IF real = {} THEN Readable(seed)
    ELSE \E report \in real : report.seed = seed /\
          \A other \in real : other.ballot <= report.ballot

Select(ballot, voters, seed) ==
    /\ ballot = s.term /\ s.proposed[ballot] = 0
    /\ Enough(voters) /\ \A v \in voters : s.replies[ballot][v] # Absent
    /\ IF Variant = "ignore_accepted" THEN Readable(seed) ELSE Highest(Reports(ballot, voters), seed)
    /\ ~Focused \/ ballot # 1 \/ seed = 1
    /\ Schedule # "divergent_holders" \/ ballot # 2 \/ seed = 2
    /\ s' = [s EXCEPT !.proposed[ballot] = seed]

Stage(voter, seed) ==
    /\ voter \in Available /\ seed \notin s.copies[voter] /\ Readable(seed)
    /\ Cardinality(s.copies[voter]) < Capacity
    /\ \E b \in 1..s.term : s.proposed[b] = seed
    /\ IF s.failed > 0 \/ Schedule \in {"hidden", "general"}
       THEN TRUE ELSE voter = (IF Schedule = "divergent_holders" THEN seed ELSE 1)
    /\ s' = [s EXCEPT !.copies[voter] = @ \cup {seed},
            !.ready[voter] = IF Variant = "cached_ready" \/ Schedule = "divergent_holders"
                            THEN @ \cup {seed} ELSE @]

Protect(seed) ==
    /\ Media = "referent" /\ ~Protected(seed)
    /\ LET holders == {v \in Available : seed \in s.copies[v]}
       IN /\ Enough(holders) /\ s' = [s EXCEPT !.backing[seed] = holders]

CanHoldAtVote(voter, seed) ==
    CASE Media = "metadata" -> TRUE
      [] Media = "referent" -> Protected(seed)
      [] Variant = "cached_ready" -> seed \in s.ready[voter]
      [] OTHER -> seed \in s.copies[voter]

Accept(ballot, voter) ==
    LET seed == s.proposed[ballot] IN
    /\ voter \in Available /\ ballot <= s.term /\ seed # 0
    /\ s.promises[voter] <= ballot /\ voter \notin Acceptors(ballot, seed)
    /\ CanHoldAtVote(voter, seed)
    /\ IF Schedule = "hidden" /\ ballot = 1 THEN voter \in {1, 2}
       ELSE IF Schedule = "partial" /\ ballot = 1
            THEN voter = (IF Media = "metadata" THEN 2 ELSE 1)
       ELSE IF Schedule = "report_then_loss" /\ s.failed = 0 THEN voter = 1
       ELSE IF Schedule = "divergent_holders" /\ ballot < 3 THEN voter = ballot
       ELSE TRUE
    /\ s' = [s EXCEPT !.promises[voter] = ballot,
                       !.latest[voter] = [ballot |-> ballot, seed |-> seed],
                       !.voted[ballot][seed] = @ \cup {voter}]

Collect(voter, seed) ==
    /\ ~Focused \/ (Schedule = "divergent_holders" /\ s.learned # {})
    /\ voter \in Available /\ seed \in s.copies[voter]
    /\ Media # "referent" \/ voter \notin s.backing[seed]
    /\ Media # "local" \/ s.latest[voter].seed # seed \/
        (Variant = "promise_releases_vote" /\ s.latest[voter].ballot < s.promises[voter])
    /\ s' = [s EXCEPT !.copies[voter] = @ \ {seed}]

Lose(zone) ==
    /\ s.failed = 0
    /\ Schedule = "general" \/ zone = (IF Schedule = "divergent_holders" THEN 3 ELSE 1)
    /\ CASE Schedule = "hidden" -> Enough(Acceptors(1, 1))
         [] Schedule = "partial" -> Acceptors(1, 1) # {}
         [] Schedule = "report_then_loss" -> s.proposed[2] = 1 /\ Acceptors(1, 1) # {}
         [] Schedule = "divergent_holders" -> 2 \in Acceptors(2, 2)
         [] OTHER -> TRUE
    /\ s' = [s EXCEPT !.failed = zone]

Ask == /\ ~s.requested /\ s' = [s EXCEPT !.requested = TRUE]

ObserveDecision(ballot, seed) ==
    /\ seed \notin s.learned /\ seed \in Seeds /\ s.requested /\ Readable(seed)
    /\ IF Variant = "publish_readiness"
       THEN Enough({v \in Available : seed \in s.copies[v]})
       ELSE Enough(Acceptors(ballot, seed) \cap Available)
    /\ s' = [s EXCEPT !.learned = @ \cup {seed},
                       !.restored = @ \/ (Schedule = "hidden" /\ s.failed > 0 /\ ballot > 1)]

BeginSome == Begin
PrepareSome == \E b \in Terms, v \in Voters : Prepare(b, v)
SelectSome == \E b \in Terms, quorum \in SUBSET Voters, seed \in Seeds : Select(b, quorum, seed)
StageSome == \E v \in Voters, seed \in Seeds : Stage(v, seed)
ProtectSome == \E seed \in Seeds : Protect(seed)
AcceptSome == \E b \in Terms, v \in Voters : Accept(b, v)
ObserveSome == \E b \in Terms, seed \in Seeds : ObserveDecision(b, seed)
Next ==
    \/ BeginSome \/ PrepareSome \/ SelectSome \/ StageSome \/ ProtectSome \/ AcceptSome
    \/ Ask \/ ObserveSome
    \/ \E v \in Voters : Lose(v) \/ \E seed \in Seeds : Collect(v, seed)

Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(BeginSome) /\ WF_s(PrepareSome) /\ WF_s(SelectSome)
    /\ WF_s(StageSome) /\ WF_s(ProtectSome) /\ WF_s(AcceptSome) /\ WF_s(Ask) /\ WF_s(ObserveSome)

ChosenAgreement == Cardinality(KnownChoices) <= 1
PublishedIsChosen == s.learned \subseteq KnownChoices
EveryLiveAcceptedHasBytes ==
    \A v \in Available : s.latest[v].seed # 0 =>
      IF Media = "referent" THEN (s.backing[s.latest[v].seed] \cap Available # {})
      ELSE (s.latest[v].seed \in s.copies[v])
ChosenIsRecoverable ==
    \A seed \in KnownChoices :
      IF Media = "referent" THEN s.backing[seed] \cap Available # {}
      ELSE \A voters \in SUBSET Available : Enough(voters) => LocalHolders(seed) \cap voters # {}
StagingIsBounded == \A v \in Voters : Cardinality(s.copies[v]) <= Capacity

RecoversAfterFault == (s.failed > 0) ~> (s.learned # {})
NeverRelearnsHiddenChoice ==
    ~(s.failed > 0 /\ Enough(Acceptors(1, 1)) /\ s.restored /\ s.learned = {1})
NeverDiscardsLostSingleton ==
    ~(s.failed = 1 /\ Acceptors(1, 1) = {1} /\ ~Chosen(1) /\ ~Readable(1) /\ s.learned = {2})
NeverRetriesUnreadablePreparedValue ==
    ~(s.failed = 1 /\ s.proposed[2] = 1 /\ ~Chosen(1) /\ ~Readable(1) /\ s.learned = {2})
NeverReleasesReplacedBinding ==
    ~(s.failed = 3 /\ s.learned = {2} /\ s.latest[1].ballot = 3
      /\ 1 \in s.ready[1] /\ 1 \notin s.copies[1])

=============================================================================
