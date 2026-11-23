-------------------------- MODULE PendingActivation --------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Protocol, Variant, Scenario, InitialLostZone
VARIABLE s

Old == {1, 2, 3}
Target == {2, 3, 4}
Members == Old \cup Target
Seeds == {1, 2}
Zone(voter) == IF voter = 4 THEN 1 ELSE voter
Up == {v \in Members : Zone(v) # s.lost}
Majority(family, voters) == 2 * Cardinality(family \cap voters) > Cardinality(family)
PreexistingChoice == Scenario \in {"hidden", "settled_hidden", "ready"}

Init ==
    s = [revision |-> 1, lost |-> InitialLostZone, sourceLink |-> Scenario = "general",
         oldProposal |-> IF PreexistingChoice THEN 1 ELSE 0,
         oldVotes |-> IF PreexistingChoice THEN {1, 2} ELSE {},
         frozen |-> {}, reported |-> {}, closed |-> FALSE, recovered |-> 0, carried |-> 0,
         newProposal |-> 0, copies |-> [seed \in Seeds |-> {}], newVotes |-> {},
         settled |-> FALSE, visible |-> 0, serving |-> 0]

OldDecision(seed) == seed = s.oldProposal /\ Majority(Old, s.oldVotes)
NewDecision(seed) == seed = s.newProposal /\ Majority(Target, s.newVotes)
Decided(seed) == OldDecision(seed) \/ NewDecision(seed)
OldReadable(seed) == ~s.settled /\ seed = s.oldProposal /\ s.oldVotes \cap Up # {}
Readable(seed) == s.sourceLink \/ OldReadable(seed) \/ s.copies[seed] \cap Up # {}

ProposeOld(seed) ==
    /\ s.revision = 1 /\ ~s.closed /\ s.oldProposal = 0 /\ s.sourceLink
    /\ s' = [s EXCEPT !.oldProposal = seed]

VoteOld(voter) ==
    /\ voter \in Old \cap Up /\ voter \notin s.frozen \cup s.oldVotes
    /\ s.oldProposal # 0 /\ Readable(s.oldProposal)
    /\ s' = [s EXCEPT !.oldVotes = @ \cup {voter}]

Freeze(voter) ==
    /\ s.revision = 1 /\ ~s.closed /\ voter \in Old \cap Up /\ voter \notin s.frozen
    /\ s' = [s EXCEPT !.frozen = @ \cup {voter},
                      !.reported = IF voter \in s.oldVotes THEN @ \cup {voter} ELSE @]

Close ==
    /\ s.revision = 1 /\ ~s.closed /\ Majority(Old, s.frozen)
    /\ Protocol # "wait" \/ s.visible # 0
    /\ s' = [s EXCEPT !.closed = TRUE, !.recovered =
           CASE Variant = "learned_only" -> s.visible
             [] s.reported # {} -> s.oldProposal
             [] OTHER -> 0]

Copy(voter, seed) ==
    /\ s.closed /\ voter \in Target \cap Up /\ voter \notin s.copies[seed]
    /\ IF s.revision = 1 THEN seed = s.recovered ELSE seed = s.newProposal
    /\ Readable(seed)
    /\ s' = [s EXCEPT !.copies[seed] = @ \cup {voter}]

Change ==
    /\ s.revision = 1 /\ s.closed /\ Majority(Target, Up)
    /\ LET seed == s.recovered IN
           IF seed = 0 \/ Variant = "skip_install_copy" THEN TRUE
           ELSE Majority(Target, s.copies[seed] \cap Up)
    /\ LET seed == IF Variant = "forget_slot" THEN 0 ELSE s.recovered
       IN s' = [s EXCEPT !.revision = 2, !.carried = seed, !.newProposal = seed,
               !.newVotes = IF Protocol # "carry" /\ seed # 0 THEN s.copies[seed] ELSE {}]

ProposeNew(seed) ==
    /\ s.revision = 2 /\ s.newProposal = 0
    /\ IF s.carried = 0 THEN TRUE ELSE seed = s.carried
    /\ Readable(seed)
    /\ s' = [s EXCEPT !.newProposal = seed]

VoteNew(voter) ==
    /\ s.revision = 2 /\ voter \in Target \cap Up /\ voter \notin s.newVotes
    /\ s.newProposal # 0
    /\ voter \in s.copies[s.newProposal]
       \/ (Variant = "stale_ready" /\ s.newProposal = s.oldProposal /\ s.oldVotes # {})
    /\ s' = [s EXCEPT !.newVotes = @ \cup {voter}]

Publish(seed) ==
    /\ Decided(seed)
    /\ IF s.revision = 1
       THEN Scenario \notin {"hidden", "settled_hidden"} /\ s.visible # seed /\ OldReadable(seed)
       ELSE /\ s.serving # seed
            /\ Scenario # "settled_hidden" \/ s.settled
            /\ IF Variant = "publish_stale" THEN Readable(seed)
               ELSE NewDecision(seed) /\ s.copies[seed] \cap Up # {}
    /\ s' = [s EXCEPT !.visible = seed,
                      !.serving = IF s.revision = 2 THEN seed ELSE @]

SettleOld ==
    /\ s.revision = 2 /\ ~s.settled
    /\ LET seed == s.recovered IN
           IF seed = 0 \/ Variant = "skip_install_copy" THEN TRUE
           ELSE Majority(Target, s.copies[seed])
    /\ s' = [s EXCEPT !.settled = TRUE]

Lose(zone) ==
    /\ s.lost = 0 /\ Scenario = "general"
    /\ s' = [s EXCEPT !.lost = zone]

LoseSource ==
    /\ s.sourceLink /\ Scenario = "general"
    /\ s' = [s EXCEPT !.sourceLink = FALSE]

ProposeOldSome == \E seed \in Seeds : ProposeOld(seed)
VoteOldSome == \E voter \in Members : VoteOld(voter)
FreezeSome == \E voter \in Members : Freeze(voter)
CopySome == \E voter \in Members, seed \in Seeds : Copy(voter, seed)
ProposeNewSome == \E seed \in Seeds : ProposeNew(seed)
VoteNewSome == \E voter \in Members : VoteNew(voter)
PublishSome == \E seed \in Seeds : Publish(seed)

Next ==
    \/ ProposeOldSome \/ VoteOldSome \/ FreezeSome \/ Close \/ CopySome \/ Change
    \/ ProposeNewSome \/ VoteNewSome \/ PublishSome \/ SettleOld \/ LoseSource
    \/ \E zone \in 1..3 : Lose(zone)

Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(FreezeSome) /\ WF_s(Close) /\ WF_s(CopySome) /\ WF_s(Change)
    /\ WF_s(VoteNewSome) /\ WF_s(PublishSome)

OneDecision == Cardinality({seed \in Seeds : Decided(seed)}) <= 1
RetainsOldChoice == s.closed => \A seed \in Seeds : OldDecision(seed) => s.recovered = seed
NewScopeCarriesExactBinding == s.revision = 2 => s.recovered = s.carried
HasCurrentCopies == s.revision = 2 =>
    \A seed \in Seeds : (s.carried = seed \/ Decided(seed)) =>
        \A voters \in SUBSET Up : Majority(Target, voters) => s.copies[seed] \cap voters # {}
PublishedHasDecision == s.visible # 0 => Decided(s.visible)
ServingHasCurrentDecision == s.serving # 0 => NewDecision(s.serving)
NeverMovesUnready ==
    ~(s.revision = 2 /\ s.oldProposal = 0 /\ ~s.sourceLink /\ s.visible = 0)
NeverMovesOnlyAccepted ==
    ~(s.revision = 2 /\ s.carried # 0 /\ ~OldDecision(s.carried) /\ s.serving = s.carried)
NeverRecoversHiddenChoice ==
    ~(s.revision = 2 /\ OldDecision(1) /\ s.serving = 1 /\ s.settled /\ ~s.sourceLink)

EventuallyChanges == <>(s.revision = 2)
EventuallyPublishes == <>(s.revision = 2 /\ s.serving = 1)

=============================================================================
