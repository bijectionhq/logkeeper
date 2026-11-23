----------------------------- MODULE CheckpointEnvelope -----------------------------
EXTENDS Naturals

CONSTANT Variant
VARIABLE s

Cuts == 1..3
DataIds == 1..3
Proofs == 1..3
EvidenceIds == 1..3
Scope(cut) == IF cut = 3 THEN 2 ELSE 1
Position(cut) == IF cut = 3 THEN 2 ELSE cut
DataEnd(cut) == 1
DataRoot(cut) == IF cut = 3 THEN 2 ELSE 1
Dependencies(manifest) ==
    CASE manifest = 1 -> {1}
      [] manifest = 2 -> {1, 2}
      [] manifest = 3 -> {3}
DataLsn(root) == IF root \in DataIds THEN 1 ELSE 0

Init ==
    s = [proofs |-> {}, pins |-> {}, staged |-> 0, selected |-> 0,
         control |-> 0, data |-> 0, manifest |-> 0, opened |-> FALSE]

Put(proof) ==
    /\ proof \notin s.proofs
    /\ s' = [s EXCEPT !.proofs = @ \cup {proof}]

Register(manifest) ==
    /\ manifest \notin s.pins
    /\ Dependencies(manifest) \subseteq s.proofs \/ Variant = "manifest_only"
    /\ s' = [s EXCEPT !.pins = @ \cup {manifest}]

Reclaim(proof) ==
    /\ proof \in s.proofs
    /\ (\A manifest \in s.pins : proof \notin Dependencies(manifest)) \/ Variant = "lost_pin"
    /\ s' = [s EXCEPT !.proofs = @ \ {proof}]

Stage(cut) ==
    /\ s.staged = 0
    /\ s' = [s EXCEPT !.staged = cut]

Select ==
    /\ s.staged # 0 /\ s.selected = 0
    /\ Scope(s.staged) = 1 \/ Variant = "ignore_lineage"
    /\ Position(s.staged) = 2 \/ (Variant = "frontier_only" /\ DataEnd(s.staged) = 1)
    /\ s.staged \in s.pins
    /\ s' = [s EXCEPT !.selected = s.staged]

Open(control, data, manifest) ==
    /\ s.selected # 0 /\ ~s.opened
    /\ control = s.selected \/
         (Variant = "control_by_frontier" /\ Scope(control) = Scope(s.selected) /\
          DataEnd(control) = DataEnd(s.selected))
    /\ data = DataRoot(s.selected) \/
         (Variant = "data_by_frontier" /\ DataLsn(data) = DataEnd(s.selected))
    /\ manifest = s.selected \/ (Variant = "weak_evidence_binding" /\ Scope(manifest) = Scope(s.selected))
    /\ manifest \in s.pins
    /\ s' = [s EXCEPT !.control = control, !.data = data, !.manifest = manifest, !.opened = TRUE]

Next ==
    \/ \E proof \in Proofs : Put(proof) \/ Reclaim(proof)
    \/ \E manifest \in EvidenceIds : Register(manifest)
    \/ \E cut \in Cuts : Stage(cut)
    \/ Select
    \/ \E control \in Cuts, data \in DataIds, manifest \in EvidenceIds : Open(control, data, manifest)

Spec == Init /\ [][Next]_s
CorrectSelection == s.selected # 0 => Scope(s.selected) = 1 /\ Position(s.selected) = 2
ExactComponents == s.opened => s.control = 2 /\ s.data = DataRoot(2) /\ s.manifest = 2
SelectedEvidenceExists == s.selected # 0 => Dependencies(s.selected) \subseteq s.proofs
AllOpenEvidenceExists == s.opened => Dependencies(s.manifest) \subseteq s.proofs
NeverReusesTheDataRootAtANewCut ==
    ~(s.opened /\ s.control = 2 /\ s.manifest = 2 /\ s.data = DataRoot(1) /\ Position(1) < Position(2))
=============================================================================
