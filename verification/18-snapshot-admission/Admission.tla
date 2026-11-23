------------------------------- MODULE Admission ----------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS MaxHead, Capacity, Variant
VARIABLE state

Cuts == 0..MaxHead
Init ==
    state = [head |-> 0, root |-> 0, floor |-> 0, custody |-> {0}, deleting |-> {},
        disposed |-> {}, phase |-> "idle", cut |-> 0, basis |-> 0,
        link |-> TRUE, placement |-> "source", reserved_at_source |-> FALSE,
        answered |-> 0, floor_at_fetch |-> 0, served_old_on_target |-> FALSE]

Serving == state.placement # "sealed"
Held == state.phase = "reserved"

Commit ==
    /\ Serving
    /\ state.head < MaxHead
    /\ state.head - state.floor < Capacity
    /\ state' = [state EXCEPT !.head = @ + 1]

Register(new) ==
    /\ new \in (state.root + 1)..state.head
    /\ new \notin (state.custody \cup state.disposed)
    /\ state' = [state EXCEPT !.custody = @ \cup {new}]

Publish(new) ==
    /\ Serving
    /\ new \in (state.root + 1)..state.head
    /\ new \in state.custody \/ Variant = "before_custody"
    /\ new \notin state.deleting \/ Variant = "accept_old_receipt"
    /\ state' = [state EXCEPT !.root = new]

Request ==
    /\ state.phase = "idle"
    /\ state' = [state EXCEPT !.phase = "pending",
        !.cut = IF Variant = "fixed_then_reserve" THEN state.head ELSE 0]

Reserve ==
    /\ Serving
    /\ state.phase = "pending"
    /\ state.root <= state.cut \/ Variant # "fixed_then_reserve"
    /\ state' = [state EXCEPT !.phase = "reserved", !.basis = state.root,
        !.reserved_at_source = (state.placement = "source"),
        !.cut = IF Variant = "fixed_then_reserve" THEN state.cut ELSE state.head]

Trim(new) ==
    /\ Serving
    /\ new \in (state.floor + 1)..state.root
    /\ ~Held \/ state.basis = state.cut \/ new <= state.basis \/ Variant = "split_wal_hold"
    /\ state' = [state EXCEPT !.floor = new]

StartDisposal(old) ==
    /\ Serving
    /\ old \in state.custody \ state.deleting
    /\ old # state.root
    /\ ~Held \/ old # state.basis \/ Variant = "split_root_hold"
    /\ state' = [state EXCEPT !.deleting = @ \cup {old}]

FinishDisposal(old) ==
    /\ old \in state.deleting
    /\ state' = [state EXCEPT !.custody = @ \ {old}, !.deleting = @ \ {old},
        !.disposed = @ \cup {old}]

Fetch ==
    /\ Held
    /\ Serving
    /\ state.link
    /\ state.basis \in state.custody
    /\ state.basis = state.cut \/ state.floor <= state.basis
    /\ state' = [state EXCEPT !.phase = "finished",
        !.answered = IF Variant = "read_live_head" THEN state.head ELSE state.cut,
        !.floor_at_fetch = state.floor,
        !.served_old_on_target = (state.reserved_at_source /\ state.placement = "target" /\
          state.basis < state.root /\ state.basis < state.cut /\ state.cut < state.head)]

ToggleLink ==
    /\ state.link \/ Variant # "permanent_link_loss"
    /\ state' = [state EXCEPT !.link = ~@]

Seal ==
    /\ state.placement = "source"
    /\ state' = [state EXCEPT !.placement = "sealed"]

Install ==
    /\ state.placement = "sealed"
    /\ state' = [state EXCEPT !.placement = "target"]

Next ==
    \/ Commit \/ Request \/ Reserve \/ Fetch \/ ToggleLink \/ Seal \/ Install
    \/ \E cut \in Cuts : Register(cut) \/ Publish(cut) \/ Trim(cut)
                         \/ StartDisposal(cut) \/ FinishDisposal(cut)

Spec == Init /\ [][Next]_state
FairSpec ==
    /\ Spec
    /\ WF_state(Install)
    /\ WF_state(Reserve)
    /\ IF Variant = "unfair_fetch" THEN TRUE ELSE WF_state(Fetch)

CurrentHasCustody ==
    state.root \in state.custody

CurrentNotDeleting ==
    state.root \notin state.deleting

ProtectedRoot ==
    Held => state.basis \in state.custody /\ state.basis \notin state.deleting

ProtectedSuffix ==
    Held => (state.basis = state.cut \/ state.floor <= state.basis) /\
      state.basis <= state.cut /\ state.cut <= state.head

RetentionBound ==
    state.head - state.floor <= Capacity

ResponseAtCut ==
    state.phase = "finished" => state.answered = state.cut /\ state.cut <= state.head

CompletesWithStableLink ==
    (<>[]state.link) => ((state.phase = "pending") ~> (state.phase = "finished"))

CompletesWithoutStableLink ==
    (state.phase = "pending") ~> (state.phase = "finished")

NeverOvertaken ==
    ~(state.phase = "pending" /\ state.cut < state.root)

NeverServesOldBasisAfterMove ==
    ~state.served_old_on_target

NeverStallsAtBound ==
    ~(Held /\ state.basis < state.cut /\ state.root > state.basis /\
      state.head < MaxHead /\
      state.head - state.basis = Capacity)

NeverReclaimsOldBasis ==
    ~(state.served_old_on_target /\ state.basis \in state.disposed /\ state.floor > state.basis)

NeverFinishesEmptySuffixAfterTrim ==
    ~(state.phase = "finished" /\ state.basis = state.answered /\ state.floor_at_fetch > state.basis /\
      state.basis \in state.custody /\ state.basis \notin state.deleting)
=============================================================================
