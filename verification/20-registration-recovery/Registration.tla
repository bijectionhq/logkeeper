----------------------------- MODULE Registration ----------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS MaxId, Window, PinCapacity, Variant, Observe
VARIABLE state

Ids == 1..MaxId
Init ==
    state = [issued |-> 0, phase |-> [i \in Ids |-> "unused"], messages |-> {},
        known |-> {}, held |-> {}, spent |-> {}, released |-> {}, terminal |-> {},
        offer |-> 0, floor |-> 0, acknowledged |-> 0, running |-> TRUE,
        link |-> TRUE, replayed |-> FALSE, rejected |-> FALSE, interrupted |-> 0]

Prepare ==
    /\ state.running
    /\ state.issued < MaxId
    /\ state.issued - state.acknowledged < Window \/ Variant = "unbounded_window"
    /\ state' = [state EXCEPT !.issued = @ + 1, !.phase[state.issued + 1] = "preparing"]

Send(id) ==
    /\ state.running
    /\ state.phase[id] \in {"preparing", "published"}
    /\ id \notin state.known \/ Observe
    /\ id \notin state.messages
    /\ state' = [state EXCEPT !.messages = @ \cup {id}]

Deliver(id) ==
    /\ state.link
    /\ id \in state.messages
    /\ LET replay == id \in state.held
           admits == id \notin state.spent /\ (id > state.floor \/ Variant = "ignore_floor")
       IN /\ replay \/ ~admits \/ Cardinality(state.held) < PinCapacity \/ Variant = "unmetered_pins"
          /\ state' = [state EXCEPT !.messages = @ \ {id},
           !.held = IF replay \/ admits THEN @ \cup {id} ELSE @,
           !.replayed = @ \/ (Observe /\ replay /\ id <= state.floor),
           !.rejected = @ \/ (Observe /\ ~replay /\ ~admits /\
                                id <= state.floor /\ id \in state.released)]

ObserveGrant(id) ==
    /\ state.running /\ state.link
    /\ id \in state.held
    /\ id \notin state.known
    /\ state' = [state EXCEPT !.known = @ \cup {id}]

Publish(id) ==
    /\ state.running
    /\ state.phase[id] = "preparing" \/ (Variant = "publish_after_close" /\ state.phase[id] = "closed")
    /\ id \in state.known
    /\ state' = [state EXCEPT !.phase[id] = "published"]

Close(id) ==
    /\ state.running
    /\ state.phase[id] \in {"preparing", "published"}
    /\ state' = [state EXCEPT !.phase[id] = "closed", !.terminal = @ \cup {id}]

Release(id) ==
    /\ state.running /\ state.link
    /\ state.phase[id] = "closed"
    /\ id \notin state.released \/ id \in state.held
    /\ Variant # "release_needs_capacity" \/ Cardinality(state.held) < PinCapacity
    /\ state' = [state EXCEPT !.held = @ \ {id}, !.released = @ \cup {id},
        !.spent = IF id > state.floor THEN @ \cup {id} ELSE @]

Propose(cut) ==
    /\ state.running
    /\ cut \in (state.offer + 1)..state.issued
    /\ \A id \in 1..cut :
         state.phase[id] = "closed" \/
         (Variant # "terminal_only" /\ (id \in state.known \/ Variant = "promise_without_receipt"))
    /\ state' = [state EXCEPT !.offer = cut]

Install ==
    /\ state.link
    /\ state.offer > state.floor
    /\ state' = [state EXCEPT !.floor = state.offer, !.spent = @ \ (1..state.offer),
        !.held = IF Variant = "forget_held" THEN @ \ (1..state.offer) ELSE @]

ObserveFloor ==
    /\ state.running /\ state.link
    /\ IF Variant = "early_credit" THEN state.offer > state.acknowledged
       ELSE state.floor > state.acknowledged
    /\ state' = [state EXCEPT !.acknowledged = IF Variant = "early_credit" THEN state.offer ELSE state.floor,
        !.phase = IF Variant = "drop_closed_plan_at_floor"
                  THEN [id \in Ids |-> IF id <= state.floor /\ @[id] = "closed" THEN "unused" ELSE @[id]]
                  ELSE @]

Crash(id) ==
    /\ state.running
    /\ state' = [state EXCEPT !.running = FALSE,
        !.interrupted = IF Observe /\ @ = 0 /\ state.phase[id] = "preparing" /\
                           id \in state.held /\ id \notin state.known THEN id ELSE @,
        !.phase[id] = IF Variant = "forget_intent" /\ @ = "preparing" /\ id \in state.held
                      THEN "unused" ELSE @]

Restart == ~state.running /\ state' = [state EXCEPT !.running = TRUE]

ToggleLink ==
    /\ state.link \/ Variant # "permanent_loss"
    /\ state' = [state EXCEPT !.link = ~@]

Next ==
    \/ Prepare \/ Install \/ ObserveFloor \/ Restart \/ ToggleLink
    \/ \E id \in Ids : Send(id) \/ Deliver(id) \/ ObserveGrant(id) \/ Publish(id) \/
                         Close(id) \/ Release(id) \/ Propose(id) \/ Crash(id)

Spec == Init /\ [][Next]_state
FairSpec ==
    /\ Spec
    /\ \A id \in Ids : WF_state(Release(id))
    /\ WF_state(Install)

CustodyWasPlanned ==
    /\ \A id \in state.held : state.phase[id] # "unused"
    /\ \A id \in state.messages :
         state.phase[id] # "unused" \/ id <= state.floor \/ id \in state.spent

PublishedHasCustody ==
    \A id \in Ids : state.phase[id] = "published" => id \in state.held

ClosedCannotPublish ==
    \A id \in state.terminal : state.phase[id] # "published"

ClosedCannotResurrect ==
    state.held \cap state.released = {}

FloorDoesNotCrossUnacquiredPlan ==
    \A id \in 1..state.floor :
       state.phase[id] = "preparing" => id \in state.held

ReceiverCreditBound ==
    /\ state.acknowledged <= state.floor
    /\ state.issued - state.floor <= Window
    /\ state.spent \subseteq (state.floor + 1)..state.issued

PhysicalPinBound == Cardinality(state.held) <= PinCapacity

Settles(id) ==
    id \notin state.held /\ (id \in state.spent \/ id <= state.floor)

ClosedSettles ==
    (<>[](state.link /\ state.running)) =>
      (\A id \in Ids : state.phase[id] = "closed" ~> Settles(id))

ClosedSettlesWithoutLink ==
    (<>[]state.running) => (\A id \in Ids : state.phase[id] = "closed" ~> Settles(id))

NeverReusesCreditWhileOldRootLive ==
    ~(state.phase[1] = "published" /\ state.acknowledged >= 1 /\ state.issued > Window)

NeverReplaysHeldBelowFloor == ~state.replayed
NeverRejectsAfterCompaction == ~state.rejected
NeverSettlesInterruptedGrant ==
    ~(state.interrupted > 0 /\ state.running /\
      state.interrupted \in state.released /\ state.interrupted <= state.floor)
=============================================================================
