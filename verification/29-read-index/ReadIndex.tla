------------------------------ MODULE ReadIndex ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Variant, MaxDepth
VARIABLE s

Voters == 1..3
Quorums == {q \in SUBSET Voters : Cardinality(q) = 2}
NoSample == [present |-> FALSE, history |-> <<>>]

Init ==
    s = [ballot |-> 1, issued |-> <<>>, chosen |-> <<>>, applied |-> 0,
         voters |-> [v \in Voters |-> [promised |-> 1, ballot |-> 1, held |-> <<>>]],
         invoked |-> FALSE, invocationCut |-> 0, window |-> {},
         round |-> 0, fresh |-> FALSE, knownAtStart |-> 0, openedAfterFence |-> FALSE,
         samples |-> [v \in Voters |-> NoSample], captured |-> FALSE, target |-> <<>>,
         abandoned |-> <<>>, answered |-> FALSE, reply |-> <<>>]

Prefix(earlier, later) ==
    Len(earlier) <= Len(later) /\ SubSeq(later, 1, Len(earlier)) = earlier

WindowAfter(history) ==
    IF ~s.invoked THEN {}
    ELSE IF Variant \in {"atomic_batch", "sandwich"}
         THEN s.window \cup {Len(history)}
         ELSE s.window \cup (Len(s.chosen)..Len(history))

Stage(value) ==
    /\ Len(s.issued) < MaxDepth
    /\ s' = [s EXCEPT !.issued = Append(@, value)]

ChoiceAfter(voters) ==
    LET covered == {end \in 0..Len(s.issued) :
         \E q \in Quorums : \A v \in q :
             voters[v].ballot = s.ballot /\ Len(voters[v].held) >= end }
        tip == CHOOSE end \in covered : \A other \in covered : other <= end
    IN IF tip > Len(s.chosen) THEN SubSeq(s.issued, 1, tip) ELSE s.chosen

Vote(voter, end) ==
    /\ s.voters[voter].promised = s.ballot /\ s.voters[voter].ballot = s.ballot
    /\ Len(s.voters[voter].held) < end /\ end <= Len(s.issued)
    /\ LET voters == [s.voters EXCEPT ![voter].held = SubSeq(s.issued, 1, end)]
           chosen == ChoiceAfter(voters)
       IN s' = [s EXCEPT !.voters = voters, !.chosen = chosen, !.window = WindowAfter(chosen)]

Apply ==
    /\ s.applied < Len(s.chosen)
    /\ s' = [s EXCEPT !.applied = Len(s.chosen)]

Prepare(voter) ==
    /\ s.ballot = 1 /\ s.voters[voter].promised = 1
    /\ s' = [s EXCEPT !.voters[voter].promised = 2]

Activate(quorum, source) ==
    /\ s.ballot = 1 /\ source \in quorum
    /\ \A voter \in quorum :
         s.voters[voter].promised = 2 /\ Len(s.voters[voter].held) <= Len(s.voters[source].held)
    /\ LET seed == s.voters[source].held
           held == IF Variant = "open_before_coverage" THEN <<>> ELSE seed
           chosen == IF Variant = "open_before_coverage" THEN s.chosen ELSE seed
       IN /\ Prefix(s.chosen, seed)
          /\ s' = [s EXCEPT !.ballot = 2, !.issued = seed, !.chosen = chosen,
                  !.window = WindowAfter(chosen),
                  !.voters = [v \in Voters |-> IF v \in quorum
                      THEN [promised |-> 2, ballot |-> 2, held |-> held] ELSE s.voters[v]]]

Invoke ==
    /\ ~s.invoked
    /\ s' = [s EXCEPT !.invoked = TRUE, !.invocationCut = Len(s.chosen),
                       !.window = {Len(s.chosen)}]

StartRound ==
    /\ s.round = 0 /\ (s.invoked \/ Variant = "reuse_old_round")
    /\ s' = [s EXCEPT !.round = s.ballot, !.fresh = s.invoked, !.knownAtStart = s.applied,
         !.openedAfterFence = Cardinality({v \in Voters : s.voters[v].promised > s.ballot}) >= 2]

Sample(voter) ==
    /\ s.round > 0 /\ ~s.captured /\ ~s.samples[voter].present
    /\ s.voters[voter].ballot = s.round
    /\ s.voters[voter].promised = s.round \/ Variant = "ignore_promise"
    /\ s' = [s EXCEPT !.samples[voter] = [present |-> TRUE, history |-> s.voters[voter].held]]

Capture(quorum, source) ==
    /\ s.invoked /\ ~s.captured /\ source \in quorum
    /\ \A v \in quorum : s.samples[v].present /\
                          Len(s.samples[v].history) <= Len(s.samples[source].history)
    /\ LET greatest == s.samples[source].history
           target == IF Variant = "known_cut_only" THEN SubSeq(s.chosen, 1, s.knownAtStart)
                     ELSE greatest
       IN /\ Variant # "sandwich" \/ Len(greatest) = s.knownAtStart
          /\ s' = [s EXCEPT !.captured = TRUE, !.target = target]

Retry ==
    /\ s.round > 0 /\ ~s.answered
    /\ s.round # s.ballot \/ (Variant = "sandwich" /\ ~s.captured)
    /\ s' = [s EXCEPT !.round = 0, !.fresh = FALSE,
       !.samples = [v \in Voters |-> NoSample], !.captured = FALSE, !.target = <<>>,
       !.abandoned = IF s.captured /\ s.round # s.ballot THEN s.target ELSE @]

Deliver ==
    /\ s.captured /\ ~s.answered
    /\ IF Variant = "expose_candidate" THEN TRUE ELSE
         Len(s.target) <= s.applied /\
         (Variant \in {"apply_by_position", "certified_at_least"} \/ Prefix(s.target, s.chosen))
    /\ LET result == IF Variant = "certified_at_least" THEN SubSeq(s.chosen, 1, s.applied)
                     ELSE s.target
       IN s' = [s EXCEPT !.answered = TRUE, !.reply = result]

Next ==
    /\ ~s.answered
    /\ \/ \E value \in {1, 2} : Stage(value)
       \/ \E voter \in Voters : Prepare(voter) \/ Sample(voter)
       \/ \E voter \in Voters, end \in 1..MaxDepth : Vote(voter, end)
       \/ \E quorum \in Quorums : \E source \in quorum :
               Activate(quorum, source) \/ Capture(quorum, source)
       \/ Apply \/ Invoke \/ StartRound \/ Retry \/ Deliver

Spec == Init /\ [][Next]_s

FreshRound == s.answered => s.fresh

EarlierFenceBlocksRound == s.answered => ~s.openedAfterFence

IncludesPriorChoices == s.answered => s.invocationCut <= Len(s.reply)

ExactAppliedPrefix == s.answered =>
    Len(s.reply) <= s.applied /\ Prefix(s.reply, s.chosen)

ExactCutInWindow == s.answered => Len(s.reply) \in s.window

NeverRepliesBeyondStartingAppliedCut ==
    ~(s.answered /\ Len(s.reply) > s.knownAtStart)

NeverCoversChoiceAheadOfLearnerAtInvoke ==
    ~(s.answered /\ s.invocationCut > s.knownAtStart /\ Len(s.reply) >= s.invocationCut)

NeverConfirmsPrecertifiedPhysicalBatch ==
    ~(s.answered /\ s.knownAtStart = 2 /\ Len(s.reply) = 2 /\ s.window = {0, 2})

NeverFinishesAfterAbandoningCandidate ==
    ~(s.answered /\ s.round = 2 /\ Len(s.abandoned) > 0 /\ Len(s.abandoned) = Len(s.reply) /\
      s.abandoned # s.reply)

NeverServesDuringPartialFence ==
    ~(s.answered /\ s.round = 1 /\ s.ballot = 1 /\
      \E voter \in Voters : s.voters[voter].promised = 2)

NeverDeliversEarlierRoundAfterActivation ==
    ~(s.answered /\ s.round = 1 /\ s.ballot = 2)

NeverRevalidatesSamePositionWithDifferentBytes ==
    ~(s.answered /\ s.round = 1 /\ s.ballot = 2 /\ Len(s.target) > 0 /\
      Len(s.target) = Len(s.reply) /\ s.target # s.reply)
=============================================================================
