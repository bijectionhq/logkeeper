---------------------------- MODULE JointProtection ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Variant, Policy, Topology

Zones == 1..3
Nodes == 1..4
Views == {0, 1}
Zone(node) == IF node = 4 THEN (IF Topology = "colocated" THEN 2 ELSE 1) ELSE node
Members(family) == IF family = 0 THEN {1, 2, 3} ELSE {2, 3, 4}
Inputs(view) == {1, 2} \cup (IF view = 0 THEN {3} ELSE {4})

VARIABLES family, staged, cached, decision, stable, visible, copies, down
vars == <<family, staged, cached, decision, stable, visible, copies, down>>

Installed(revision) == IF revision = 0 THEN {1, 2} ELSE staged
Online(nodes, failure) == {node \in nodes : Zone(node) # failure}
Majority(revision, nodes) == 2 * Cardinality(nodes \cap Members(revision)) > Cardinality(Members(revision))
Recovering(revision, fault) == Online(Members(revision), fault)

JournalOK(revision, fault) ==
    /\ Majority(revision, Recovering(revision, fault))
    /\ \A quorum \in SUBSET Recovering(revision, fault) :
        Majority(revision, quorum) => quorum \cap Installed(revision) # {}

ObjectsOK(view, physical, fault) ==
    \A object \in Inputs(view) : Online(physical[object], fault) # {}

LocalOK(view, revision, physical, fault) ==
    \A quorum \in SUBSET Recovering(revision, fault) :
        Majority(revision, quorum) =>
            \E node \in quorum \cap Installed(revision) :
                \A object \in Inputs(view) : node \in physical[object]

CheckedObjects(view) == IF Variant = "skip_tail_inputs" THEN {1, 2} ELSE Inputs(view)
PlacementOK(revision, selectors, physical) ==
    \A fault \in Zones :
        /\ JournalOK(revision, IF Variant = "ignore_voter_domains" THEN 0 ELSE fault)
        /\ \A view \in selectors :
             /\ \A object \in CheckedObjects(view) : Online(physical[object], fault) # {}
             /\ Policy # "local" \/ LocalOK(view, revision, physical, fault)

DropSelectors == IF Variant = "visible_only" THEN {visible} ELSE {stable, visible}

Init ==
    /\ family = 0 /\ staged = {} /\ cached = 2 /\ decision = <<2, 2>>
    /\ stable = 0 /\ visible = 0 /\ down = 0
    /\ copies = [o \in 1..4 |-> CASE o = 1 -> {1, 2}
                                 [] o = 2 -> {1, 3}
                                 [] o = 3 -> {2, 3}
                                 [] OTHER -> {1}]

CopyTail ==
    /\ down = 0 /\ 2 \notin copies[4]
    /\ copies' = [copies EXCEPT ![4] = @ \cup {2}]
    /\ UNCHANGED <<family, staged, cached, decision, stable, visible, down>>

StageVoter(node) ==
    /\ down = 0 /\ node \in Members(1) \ staged
    /\ staged' = staged \cup {node}
    /\ UNCHANGED <<family, cached, decision, stable, visible, copies, down>>

InstallFamily ==
    /\ down = 0 /\ family = 0 /\ Majority(1, staged)
    /\ PlacementOK(1, {stable, visible}, copies)
    /\ family' = 1
    /\ UNCHANGED <<staged, cached, decision, stable, visible, copies, down>>

Observe ==
    /\ down = 0 /\ cached # family
    /\ cached' = family
    /\ UNCHANGED <<family, staged, decision, stable, visible, copies, down>>

Certify ==
    /\ down = 0 /\ cached # 2
    /\ cached = family \/ Variant = "stale_family"
    /\ PlacementOK(cached, {stable, visible}, copies)
    /\ decision' = <<cached, family>>
    /\ UNCHANGED <<family, staged, cached, stable, visible, copies, down>>

Publish ==
    /\ down = 0 /\ visible = 0
    /\ PlacementOK(family, {stable, 1}, copies)
    /\ visible' = 1
    /\ UNCHANGED <<family, staged, cached, decision, stable, copies, down>>

SyncSelector ==
    /\ down = 0 /\ stable # visible
    /\ stable' = visible
    /\ UNCHANGED <<family, staged, cached, decision, visible, copies, down>>

WithdrawOldTail ==
    /\ down = 0 /\ copies[3] # {}
    /\ PlacementOK(family, DropSelectors, [copies EXCEPT ![3] = {}])
    /\ copies' = [copies EXCEPT ![3] = {}]
    /\ UNCHANGED <<family, staged, cached, decision, stable, visible, down>>

Fault(zone) ==
    /\ down = 0
    /\ down' = zone
    /\ UNCHANGED <<family, staged, cached, decision, stable, visible, copies>>

Next ==
    \/ CopyTail
    \/ \E node \in Nodes : StageVoter(node)
    \/ InstallFamily \/ Observe \/ Certify \/ Publish \/ SyncSelector \/ WithdrawOldTail
    \/ \E zone \in Zones : Fault(zone)

Spec == Init /\ [][Next]_vars

ExactClosure == \A view \in {stable, visible} : ObjectsOK(view, copies, down)
CurrentMajority == JournalOK(family, down)
ExactFamilyAtDecision == decision[1] = decision[2]

NeverMixedViewsOnSuccessorAfterFault ==
    ~(family = 1 /\ stable = 0 /\ visible = 1 /\ down = 1)
NeverCollectOldTailAndRecover ==
    ~(family = 1 /\ stable = 1 /\ copies[3] = {} /\ down = 1 /\ decision = <<1, 1>>)
NeverCertifyTheDistributedLayout == decision = <<2, 2>>
=============================================================================
