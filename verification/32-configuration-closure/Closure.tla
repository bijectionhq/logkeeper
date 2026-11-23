------------------------------ MODULE Closure ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Mode, Variant, LastScope, Records, FailedZone, Schedule
VARIABLE s

Scopes == 1..LastScope
Replicas == IF LastScope <= (IF Mode = "joint" THEN 3 ELSE 2) THEN 1..4 ELSE 1..5
Commands == {"a", "b"}
Zone(replica) == ((replica - 1) % 3) + 1
Online == {replica \in Replicas : Zone(replica) # FailedZone}
Ensemble(index) == (index..(index + 2))
Joint(scope) == Mode = "joint" /\ scope % 2 = 0
Old(scope) == Ensemble(IF Mode = "joint" THEN (scope + 1) \div 2 ELSE scope)
New(scope) == IF Joint(scope) THEN Ensemble(scope \div 2 + 1) ELSE Old(scope)
Members(scope) == Old(scope) \cup New(scope)

Majority(members, votes) == 2 * Cardinality(members \cap votes) > Cardinality(members)
WriteQuorum(scope, votes) ==
    Majority(Old(scope), votes) /\ (~Joint(scope) \/ Majority(New(scope), votes))
FenceQuorum(scope, votes) ==
    IF Variant = "wrong_membership"
    THEN Majority(New(scope + 1), votes)
    ELSE IF Variant = "all_voters" THEN Members(scope) \subseteq votes
    ELSE Majority(New(scope), votes)

Prefix(history, length) == SubSeq(history, 1, length)
IsPrefix(first, second) == Len(first) <= Len(second) /\ first = Prefix(second, Len(first))
Comparable(first, second) == IsPrefix(first, second) \/ IsPrefix(second, first)
MaxOf(values) == CHOOSE maximum \in values : \A position \in values : position <= maximum
AbsentReport == Records + 1
EmptyCertificate == [ready |-> FALSE, history |-> <<>>, chosen |-> 0, visible |-> 0]
EmptyCopy == [ready |-> FALSE, history |-> <<>>]
HiddenStart == Schedule \in {"hidden", "late_delivery"}
FocusedJoint == Schedule \in {"joint_focused", "joint_write"}
JointCohort == IF FailedZone = 0 THEN {2, 3} ELSE Online

Init ==
    s = [active |-> 1, base |-> [scope \in Scopes |-> <<>>],
         issued |-> [scope \in Scopes |-> IF scope = 1 /\ HiddenStart THEN <<"a">> ELSE <<>>],
         accepted |-> [scope \in Scopes |-> [r \in Replicas |->
                        IF scope = 1 /\ HiddenStart /\ r \in {1, 2} THEN 1 ELSE 0]],
         learned |-> [scope \in Scopes |-> 0],
         reports |-> [scope \in Scopes |-> [r \in Replicas |-> AbsentReport]],
         fenced |-> [scope \in Scopes |-> {}],
         seals |-> [scope \in Scopes |-> EmptyCertificate],
         copies |-> [scope \in Scopes |-> [r \in Replicas |-> EmptyCopy]],
         installed |-> [scope \in Scopes |-> {}]]

AcceptedAt(scope, length) == {r \in Members(scope) : s.accepted[scope][r] >= length}
ChosenEnd(scope) ==
    MaxOf({0} \cup {length \in 1..Len(s.issued[scope]) : WriteQuorum(scope, AcceptedAt(scope, length))})

Extend(command) ==
    /\ Schedule # "hidden"
    /\ Schedule # "joint_write" \/ s.active > 1
    /\ Len(s.issued[s.active]) < Records
    /\ s' = [s EXCEPT !.issued[s.active] = Append(@, command)]

Accept(scope, replica, length) ==
    /\ scope <= s.active /\ replica \in Members(scope) \cap Online
    /\ Schedule # "late_vote" \/ scope # 1 \/ replica = 1 \/ s.active > 1
    /\ replica \notin s.fenced[scope]
    /\ s.accepted[scope][replica] < length /\ Len(s.base[scope]) <= length
    /\ s' = [s EXCEPT !.accepted[scope][replica] = length]

Learn(scope) ==
    /\ scope <= s.active /\ s.learned[scope] < ChosenEnd(scope)
    /\ ~FocusedJoint
    /\ Schedule # "late_delivery" \/ scope < s.active
    /\ s' = [s EXCEPT !.learned[scope] = ChosenEnd(scope)]

Fence(replica) ==
    LET scope == s.active IN
    /\ scope < LastScope /\ ~s.seals[scope].ready
    /\ replica \in Online
    /\ ~FocusedJoint \/ replica \in JointCohort
    /\ replica \in Members(scope) \/ Variant = "wrong_membership"
    /\ s.reports[scope][replica] = AbsentReport
    /\ s' = [s EXCEPT !.reports[scope][replica] = s.accepted[scope][replica],
                       !.fenced[scope] = IF Variant = "sample_only" THEN @ ELSE @ \cup {replica}]

ForgetFence(scope, replica) ==
    /\ Variant = "volatile_fence" /\ replica \in s.fenced[scope]
    /\ s' = [s EXCEPT !.fenced[scope] = @ \ {replica}]

Reporters(scope) == {r \in Replicas : s.reports[scope][r] # AbsentReport}
Seal ==
    LET scope == s.active
        reports == Reporters(scope)
        finish == MaxOf({Len(s.base[scope])} \cup {s.reports[scope][r] : r \in reports})
        selected == IF Variant = "learned_only" THEN s.learned[scope]
                    ELSE IF Variant = "drop_inherited_base"
                            /\ \A r \in reports : s.reports[scope][r] <= Len(s.base[scope])
                         THEN 0 ELSE finish
    IN /\ scope < LastScope /\ ~s.seals[scope].ready
       /\ FenceQuorum(scope, reports)
       /\ s' = [s EXCEPT !.seals[scope] =
                    [ready |-> TRUE, history |-> Prefix(s.issued[scope], selected),
                     chosen |-> ChosenEnd(scope), visible |-> s.learned[scope]]]

Corrupt(history) ==
    IF history = <<>> THEN <<>>
    ELSE <<IF history[1] = "a" THEN "b" ELSE "a">> \o SubSeq(history, 2, Len(history))

Stage(replica) ==
    LET scope == s.active + 1
        history == s.seals[s.active].history
    IN /\ s.active < LastScope /\ s.seals[s.active].ready
       /\ replica \in Members(scope) \cap Online /\ ~s.copies[scope][replica].ready
       /\ ~FocusedJoint \/ replica \in JointCohort
       /\ s' = [s EXCEPT !.copies[scope][replica] =
                  [ready |-> TRUE, history |-> IF Variant = "install_by_length" THEN Corrupt(history) ELSE history]]

Activate(votes) ==
    LET scope == s.active + 1
        history == s.seals[s.active].history
    IN /\ s.active < LastScope /\ s.seals[s.active].ready
       /\ votes \subseteq Members(scope) \cap Online /\ WriteQuorum(scope, votes)
       /\ \A r \in votes : s.copies[scope][r].ready /\
             (IF Variant = "install_by_length" THEN Len(s.copies[scope][r].history) = Len(history)
              ELSE s.copies[scope][r].history = history)
       /\ s' = [s EXCEPT !.active = scope, !.base[scope] = history, !.issued[scope] = history,
                  !.installed[scope] = votes,
                  !.accepted[scope] = [r \in Replicas |->
                    IF r \in votes /\ s.copies[scope][r].history = history THEN Len(history) ELSE 0]]

FenceSome == \E replica \in Replicas : Fence(replica)
StageSome == \E replica \in Replicas : Stage(replica)
ActivateSome == \E votes \in SUBSET Replicas : Activate(votes)

Next ==
    \/ \E command \in Commands : Extend(command)
    \/ \E scope \in Scopes, r \in Replicas :
          ForgetFence(scope, r) \/ \E length \in 1..Len(s.issued[scope]) : Accept(scope, r, length)
    \/ \E scope \in Scopes : Learn(scope)
    \/ FenceSome \/ Seal \/ StageSome \/ ActivateSome

Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(FenceSome) /\ WF_s(Seal) /\ WF_s(StageSome) /\ WF_s(ActivateSome)

SealCoversUnlearnedChoices ==
    \A scope \in Scopes : s.seals[scope].ready =>
        IsPrefix(Prefix(s.issued[scope], s.seals[scope].chosen), s.seals[scope].history)

SealedScopeCannotExtendRecoveredPrefix ==
    \A scope \in Scopes : s.seals[scope].ready =>
        IsPrefix(Prefix(s.issued[scope], ChosenEnd(scope)), s.seals[scope].history)

NoChoiceAfterFence ==
    \A scope \in Scopes : s.seals[scope].ready => ChosenEnd(scope) = s.seals[scope].chosen

PreservesInheritedBase ==
    \A scope \in 2..s.active : IsPrefix(s.base[scope - 1], s.base[scope])

ExactInstalledQuorum ==
    \A scope \in 2..s.active :
        WriteQuorum(scope, {r \in s.installed[scope] : s.copies[scope][r].history = s.base[scope]})

AllChoicesAgree ==
    \A left, right \in 1..s.active :
        Comparable(Prefix(s.issued[left], ChosenEnd(left)), Prefix(s.issued[right], ChosenEnd(right)))

CurrentCanRecover ==
    ChosenEnd(s.active) > 0 => AcceptedAt(s.active, ChosenEnd(s.active)) \cap Online # {}

NeverRecoversHiddenChoice ==
    ~(s.active > 1 /\ s.seals[1].visible = 0 /\ s.seals[1].chosen > 0
        /\ ChosenEnd(2) >= s.seals[1].chosen /\ s.learned[1] > 0)

NeverCompletesOldQuorumLate ==
    ~(s.active > 1 /\ s.seals[1].chosen = 0 /\ ChosenEnd(1) > 0
        /\ IsPrefix(Prefix(s.issued[1], ChosenEnd(1)), s.base[2]))

NeverCarriesAcrossTwoChanges ==
    ~(s.active = LastScope /\ LastScope > 2 /\ s.seals[1].visible = 0 /\ s.seals[1].chosen > 0
        /\ s.seals[1].chosen <= ChosenEnd(LastScope))

NeverChoosesInBothJointAndFinal ==
    ~(s.active = LastScope /\ Len(s.base[2]) < ChosenEnd(2) /\ Len(s.base[LastScope]) < ChosenEnd(LastScope))

Finish == <>(s.active = LastScope)

=============================================================================
