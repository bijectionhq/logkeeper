------------------------- MODULE AttemptCompaction -------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Attempts, Width, PinLimit, Policy, Variant
VARIABLE s

IDs == 1..Attempts

Init ==
    s = [issued |-> 0, floor |-> 0, offered |-> 0, selected |-> 0, family |-> 1,
         rows |-> [id \in IDs |-> "absent"], closed |-> {}, held |-> {}, cleanup |-> {},
         settledAfterReplacement |-> {}]

Issue ==
    /\ s.issued < Attempts /\ s.selected = 0
    /\ s.issued - (IF Variant = "offer_is_credit" THEN s.offered ELSE s.floor) < Width
    /\ s' = [s EXCEPT !.issued = @ + 1]

Register(id) ==
    /\ id <= s.issued /\ s.rows[id] = "absent" /\ s.selected = 0
    /\ id > s.floor \/ Variant = "ignore_floor"
    /\ Cardinality(s.held) < PinLimit \/ Variant = "unmetered"
    /\ s' = [s EXCEPT !.rows[id] = "ready", !.held = @ \cup {id}]

Select(id) ==
    /\ s.rows[id] = "ready" /\ s.selected = 0
    /\ s' = [s EXCEPT !.selected = id]

Discard(id) ==
    /\ id <= s.issued /\ s.selected # id
    /\ s.rows[id] = "ready" \/ (s.rows[id] = "absent" /\ id > s.floor)
    /\ s' = [s EXCEPT !.rows[id] = IF id <= s.floor THEN "absent" ELSE "spent",
                      !.closed = @ \cup {id},
                      !.cleanup = IF id \in s.held THEN @ \cup {id} ELSE @]

Release(id) ==
    /\ id \in s.cleanup
    /\ s' = [s EXCEPT !.cleanup = @ \ {id}, !.held = @ \ {id},
                      !.settledAfterReplacement =
                        IF s.family = 2 /\ id <= s.floor THEN @ \cup {id} ELSE @]

CertifiedThrough(through) ==
    \A id \in (s.floor + 1)..through :
        s.rows[id] = "spent" \/ (Policy = "ready_or_spent" /\ s.rows[id] = "ready")

Offer(through) ==
    /\ s.offered < through /\ s.floor < through /\ through <= s.issued
    /\ CertifiedThrough(through) \/ Variant = "skip_unresolved"
    /\ s' = [s EXCEPT !.offered = through]

Advance ==
    /\ s.floor < s.offered
    /\ s' = [s EXCEPT !.floor = s.offered,
            !.rows = [id \in IDs |->
                IF id <= s.offered /\ (@[id] = "spent" \/ Variant = "forget_live")
                THEN "absent" ELSE @[id]],
            !.cleanup = IF Variant = "forget_cleanup"
                THEN {id \in s.cleanup : id > s.offered} ELSE @]

Replace ==
    /\ s.family = 1
    /\ s' = [s EXCEPT !.family = 2,
                      !.floor = IF Variant = "forget_floor" THEN 0 ELSE @]

Next ==
    \/ Issue \/ Advance \/ Replace
    \/ \E id \in IDs : Register(id) \/ Select(id) \/ Discard(id) \/ Release(id) \/ Offer(id)

Spec == Init /\ [][Next]_s

NoReopenClosed == \A id \in s.closed : s.rows[id] # "ready"
NoStrandedPreparation ==
    \A id \in 1..s.floor : id \in s.closed \/ s.rows[id] = "ready"
RecordedPhysicalObligations ==
    s.held = {id \in IDs : s.rows[id] = "ready"} \cup s.cleanup
PreservesSelection == s.selected = 0 \/ s.rows[s.selected] = "ready"
BoundedCredit == s.floor <= s.issued /\ s.issued - s.floor <= Width
BoundedMarkers ==
    {id \in IDs : s.rows[id] = "spent"} \subseteq (s.floor + 1)..s.issued
BoundedPins == Cardinality(s.held) <= PinLimit

NeverIssuesPastWidthWhileOldChoiceHeld ==
    ~(s.selected = 1 /\ s.rows[1] = "ready" /\ s.floor >= 1 /\ s.issued > Width)
NeverKeepsCleanupThroughCompactionAndReplacement ==
    ~(s.family = 2 /\ \E id \in s.cleanup : id <= s.floor /\ s.rows[id] = "absent" /\ id \in s.held)
NeverSettlesAfterCompactionAndReplacement ==
    ~(s.settledAfterReplacement # {} /\ s.selected # 0)

=============================================================================
