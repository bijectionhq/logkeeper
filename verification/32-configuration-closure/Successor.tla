---------------------------- MODULE Successor ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Authority, Policy, FailedZone
VARIABLE s

Old == {1, 2, 3}
New == {2, 3, 4}
Replicas == Old \cup New
Targets == 1..3
Zone(replica) == ((replica - 1) % 3) + 1
Online == {replica \in Replicas : Zone(replica) # FailedZone}
Majority(members, votes) == 2 * Cardinality(members \cap votes) > Cardinality(members)

Init ==
    s = [selected |-> 0, fencedFor |-> [r \in Replicas |-> 0], sealed |-> {}, active |-> {}]

Choose(target) ==
    /\ Authority = "ordered" /\ s.selected = 0
    /\ s' = [s EXCEPT !.selected = target]

Authorized(target) == Authority # "ordered" \/ s.selected = target

Fence(replica, target) ==
    /\ replica \in Online /\ s.fencedFor[replica] = 0 /\ Authorized(target)
    /\ s' = [s EXCEPT !.fencedFor[replica] = target]

Seal(target) ==
    LET votes == {r \in Replicas : s.fencedFor[r] = target}
    IN /\ target \notin s.sealed /\ Authorized(target)
       /\ Majority(New, votes) \/ (Policy = "either" /\ Majority(Old, votes))
       /\ s' = [s EXCEPT !.sealed = @ \cup {target}]

Activate(target) ==
    /\ target \in s.sealed \ s.active /\ Authorized(target)
    /\ s' = [s EXCEPT !.active = @ \cup {target}]

ChooseSome == \E target \in Targets : Choose(target)
FenceSome == \E target \in Targets, replica \in Replicas : Fence(replica, target)
SealSome == \E target \in Targets : Seal(target)
ActivateSome == \E target \in Targets : Activate(target)
Next == ChooseSome \/ FenceSome \/ SealSome \/ ActivateSome
Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(ChooseSome) /\ WF_s(FenceSome) /\ WF_s(SealSome) /\ WF_s(ActivateSome)

UniqueSuccessor == Cardinality(s.active) <= 1
EventuallyActivates == <>(s.active # {})

=============================================================================
