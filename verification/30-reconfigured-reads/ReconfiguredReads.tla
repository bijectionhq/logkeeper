-------------------------- MODULE ReconfiguredReads --------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Transition, ReadMode, Variant, MaxHead, Scenario
VARIABLE s

Replicas == 1..4
Old == {1, 2, 3}
New == {2, 3, 4}
Committees == Old \cup New
Majority(members, votes) ==
    2 * Cardinality(members \cap votes) > Cardinality(members)

Membership(phase) ==
    CASE phase = 1 -> Old
      [] phase = 2 -> Committees
      [] phase = 3 -> New

WriteQuorum(phase, votes) ==
    /\ votes \subseteq Membership(phase)
    /\ CASE phase = 1 -> Majority(Old, votes)
         [] phase = 2 -> Transition = "joint" /\ Majority(Old, votes) /\ Majority(New, votes)
         [] phase = 3 -> Majority(New, votes)

ReadQuorum(phase, votes) ==
    IF phase = 2 /\ Transition = "joint"
    THEN /\ votes \subseteq Committees
         /\ CASE ReadMode = "one_side" -> Majority(Old, votes) \/ Majority(New, votes)
              [] ReadMode = "successor" -> Majority(New, votes)
              [] OTHER -> WriteQuorum(phase, votes)
    ELSE WriteQuorum(phase, votes)

NoSample == [scope |-> 0, end |-> 0]
NoPin == [scope |-> 0, root |-> 0, cut |-> 0]

Init ==
    s = [phase |-> 1, localScope |-> [r \in Replicas |-> IF r \in Old THEN 1 ELSE 0],
         held |-> [r \in Replicas |-> 0], head |-> 0, applied |-> 0,
         root |-> 0, roots |-> {0}, floor |-> 0,
         invoked |-> FALSE, invocationCut |-> 0,
         round |-> 0, openedPhase |-> 0, samples |-> [r \in Replicas |-> NoSample],
         receipt |-> {}, observedEnd |-> 0, retriedAhead |-> FALSE,
         pin |-> NoPin, protected |-> FALSE, overtaken |-> FALSE,
         answered |-> FALSE, result |-> 0]

Enter(votes) ==
    /\ s.phase = 1
    /\ Scenario # "two_records" \/ votes = {2, 3}
    /\ Scenario # "prefinished_round" \/ s.receipt # {}
    /\ IF Transition = "joint" THEN WriteQuorum(2, votes) ELSE votes \subseteq Old /\ Majority(Old, votes)
    /\ \A voter \in votes \cap Old : s.held[voter] <= s.head
    /\ s' = [s EXCEPT !.phase = 2,
          !.localScope = [r \in Replicas |-> IF r \in votes THEN 2 ELSE @[r]],
          !.held = [r \in Replicas |-> IF r \in votes THEN s.head ELSE @[r]]]

Finish(votes) ==
    /\ s.phase = 2
    /\ Scenario # "two_records" \/ votes = {3, 4}
    /\ votes \subseteq Committees /\ Majority(New, votes)
    /\ ReadMode # "one_side" \/ Transition # "joint" \/ Variant = "fence_new_only" \/ Majority(Old, votes)
    /\ \A voter \in votes : s.localScope[voter] <= 2
    /\ s' = [s EXCEPT !.phase = 3,
          !.localScope = [r \in Replicas |-> IF r \in votes THEN 3 ELSE @[r]],
          !.held = [r \in Replicas |-> IF r \in votes THEN s.head ELSE @[r]],
          !.protected = IF Variant = "forget_hold" THEN FALSE ELSE @]

Sync(voter) ==
    /\ voter \in Membership(s.phase) /\ s.localScope[voter] < s.phase
    /\ s.phase # 2 \/ Transition = "joint"
    /\ s' = [s EXCEPT !.localScope[voter] = s.phase, !.held[voter] = s.head]

AppendOn(votes) ==
    /\ s.head < MaxHead /\ WriteQuorum(s.phase, votes)
    /\ Scenario # "two_records" \/ votes =
         (CASE s.phase = 1 -> {1, 2} [] s.phase = 2 -> {2, 3} [] s.phase = 3 -> {3, 4})
    /\ \A r \in votes : s.localScope[r] = s.phase
    /\ s' = [s EXCEPT !.head = @ + 1,
                       !.held = [r \in Replicas |-> IF r \in votes THEN s.head + 1 ELSE @[r]]]

Stage(voter) ==
    /\ s.phase = 1 /\ voter \in Old /\ s.localScope[voter] = 1
    /\ Scenario # "two_records" \/ voter = 1
    /\ s.head < MaxHead /\ s.held[voter] <= s.head
    /\ \A other \in Old \ {voter} : s.held[other] <= s.head
    /\ s' = [s EXCEPT !.held[voter] = s.head + 1]

Apply ==
    /\ s.applied < s.head
    /\ s' = [s EXCEPT !.applied = s.head]

Publish(root) ==
    /\ s.root < root /\ root <= s.applied
    /\ s' = [s EXCEPT !.root = root, !.roots = @ \cup {root}]

Trim ==
    /\ s.floor < s.root
    /\ (~s.protected \/ s.pin.root = s.pin.cut \/ s.root <= s.pin.root)
    /\ s' = [s EXCEPT !.floor = s.root]

Collect(root) ==
    /\ root \in s.roots \ {s.root}
    /\ (~s.protected \/ s.pin.root # root \/ Variant = "collect_pinned_root")
    /\ s' = [s EXCEPT !.roots = @ \ {root}]

Invoke ==
    /\ ~s.invoked
    /\ s' = [s EXCEPT !.invoked = TRUE, !.invocationCut = s.head]

Open(scope) ==
    /\ s.invoked /\ s.round = 0 /\ scope <= s.phase
    /\ scope # 2 \/ Transition = "joint"
    /\ s' = [s EXCEPT !.round = scope, !.openedPhase = s.phase]

Observe(voter) ==
    /\ s.round > 0 /\ s.receipt = {} /\ s.samples[voter].scope = 0
    /\ s.localScope[voter] = s.round \/ (Variant = "mix_scopes" /\ s.localScope[voter] > 0)
    /\ s' = [s EXCEPT !.samples[voter] = [scope |-> s.localScope[voter], end |-> s.held[voter]]]

Capture(votes, source) ==
    /\ s.round > 0 /\ s.receipt = {} /\ source \in votes
    /\ IF Variant = "mix_scopes"
       THEN Cardinality(votes) = 2 /\ \E r \in votes : s.samples[r].scope # s.round
       ELSE ReadQuorum(s.round, votes)
    /\ \A r \in votes : s.samples[r].scope > 0 /\ s.samples[r].end <= s.samples[source].end
    /\ s' = [s EXCEPT !.receipt = votes, !.observedEnd = s.samples[source].end]

Retry ==
    /\ s.round > 0 /\ s.round # s.phase /\ ~s.protected
    /\ s' = [s EXCEPT !.round = 0, !.receipt = {}, !.samples = [r \in Replicas |-> NoSample],
          !.retriedAhead = @ \/ (s.receipt # {} /\ s.head < s.observedEnd)]

Reserve ==
    /\ s.receipt # {} /\ s.pin.scope = 0
    /\ s.phase # 2 \/ Transition = "joint"
    /\ Variant # "current_scope_only" \/ s.round = s.phase
    /\ s.observedEnd <= s.applied \/ Variant = "ignore_observed_floor"
    /\ LET cut == IF Variant = "fixed_cut" THEN s.observedEnd ELSE s.applied
       IN /\ s.root <= cut
          /\ s' = [s EXCEPT !.pin = [scope |-> s.phase, root |-> s.root, cut |-> cut],
                            !.protected = TRUE, !.overtaken = s.observedEnd < s.root]

Deliver ==
    /\ s.pin.scope # 0
    /\ s' = [s EXCEPT !.answered = TRUE, !.result = s.pin.cut]

Next ==
    /\ ~s.answered
    /\ \/ \E votes \in SUBSET Replicas : Enter(votes) \/ Finish(votes) \/ AppendOn(votes)
       \/ \E r \in Replicas : Sync(r) \/ Stage(r) \/ Observe(r)
       \/ \E root \in 0..MaxHead : Publish(root) \/ Collect(root)
       \/ \E phase \in 1..3 : Open(phase)
       \/ \E votes \in SUBSET Replicas : \E source \in votes : Capture(votes, source)
       \/ Apply \/ Trim \/ Invoke \/ Retry \/ Reserve \/ Deliver

Spec == Init /\ [][Next]_s

OneExactQuorum ==
    s.receipt # {} => ReadQuorum(s.round, s.receipt) /\
      \A r \in s.receipt : s.samples[r].scope = s.round

CannotOpenAfterRetirementOfScope == s.receipt # {} => s.round = s.openedPhase

RoundCoversInvocation == s.receipt # {} => s.invocationCut <= s.observedEnd

ExactBasisProtected ==
    s.pin.scope # 0 => s.protected /\ s.pin.root \in s.roots /\
      s.pin.root <= s.pin.cut /\ (s.pin.root = s.pin.cut \/ s.floor <= s.pin.root)

ReturnedCutInInvocation ==
    s.answered => s.invocationCut <= s.result /\ s.result = s.pin.cut /\ s.result <= s.head

NeverUsesEarlierRoundAtLaterRoot ==
    ~(s.answered /\ s.pin.scope = 3 /\ s.round = 1 /\ s.overtaken)

NeverServesPinnedAcrossAdoption ==
    ~(s.answered /\ s.phase = 3 /\ s.pin.scope < 3 /\
      s.pin.root < s.pin.cut /\ s.pin.root < s.root)

NeverRetriesDiscardedFloor ==
    ~(s.answered /\ s.retriedAhead /\ s.pin.scope = 3 /\ s.result = 0)

NeverServesWithOnlyOneJointSide ==
    ~(s.answered /\ s.round = 2 /\ ReadQuorum(2, s.receipt) /\ ~WriteQuorum(2, s.receipt))
=============================================================================
