--------------------------- MODULE ChannelLifecycle --------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS MaxNonce, Variant, Observe
VARIABLE state

Nonces == 1..MaxNonce
Serials == {1, 2}
GrantKeys == Nonces \X Serials
None == <<0,0>>
PinCapacity == 2

Init ==
    state = [issued |-> 0, active |-> 0, serial |-> 0, floor |-> 0,
        held |-> {}, planned |-> {}, published |-> {}, withdrawn |-> {}, spent |-> {},
        retired |-> {}, held_at_close |-> {}, published_at_close |-> {},
        acquire_msg |-> None, close_msg |-> 0, floor_msg |-> 0,
        link |-> TRUE, stale_close |-> FALSE, stale_credit |-> FALSE, late_replay |-> None,
        late_refusal |-> FALSE, old_released |-> FALSE]

Open ==
    /\ state.active = 0
    /\ state.issued < MaxNonce
    /\ LET next == IF Variant = "reuse_handle" /\ state.issued > 0 THEN state.issued
                   ELSE state.issued + 1
       IN state' = [state EXCEPT !.issued = next, !.active = next, !.serial = 0, !.floor = 0, !.spent = {}]

MayClose ==
    /\ state.active # 0
    /\ Variant # "drain_first" \/ (\A key \in state.held : key[1] # state.active)

Closed(view) ==
    [view EXCEPT !.retired = @ \cup {view.active}, !.active = 0, !.serial = 0, !.floor = 0, !.spent = {},
        !.held_at_close = @ \cup {key \in view.held : key[1] = view.active},
        !.published_at_close = IF Observe THEN @ \cup {key \in view.published : key[1] = view.active} ELSE @,
        !.held = IF Variant = "drop_live_pins" THEN {key \in @ : key[1] # view.active} ELSE @]

CloseNow == MayClose /\ state' = Closed(state)

QueueClose ==
    /\ state.active # 0
    /\ state.close_msg = 0
    /\ state' = [state EXCEPT !.close_msg = state.active]

DeliverClose ==
    /\ state.close_msg # 0
    /\ LET matches == state.active = state.close_msg
           applies == MayClose /\ (matches \/ Variant = "close_by_route")
           consumed == [state EXCEPT !.close_msg = 0, !.stale_close = @ \/ (applies /\ ~matches)]
       IN state' = IF applies THEN Closed(consumed) ELSE consumed

Issue ==
    /\ state.active # 0
    /\ state.serial < 2
    /\ state.acquire_msg = None
    /\ LET key == <<state.active, state.serial + 1>>
       IN state' = [state EXCEPT !.serial = @ + 1, !.planned = @ \cup {key}, !.acquire_msg = key]

Retry(key) ==
    /\ Observe
    /\ key \in state.planned
    /\ state.acquire_msg = None
    /\ state' = [state EXCEPT !.acquire_msg = key]

ReceiveAcquire ==
    /\ state.link
    /\ state.acquire_msg # None
    /\ LET requested == state.acquire_msg
           matches == requested[1] = state.active
           handles == state.active # 0 /\ (matches \/ Variant \in {"ignore_channel", "rebind_to_route"})
           key == IF Variant = "rebind_to_route" THEN <<state.active,requested[2]>> ELSE requested
           replay == requested \in state.held
           eligible == handles /\ requested[2] \notin state.spent /\ requested[2] > state.floor
           admits == ~replay /\ eligible /\ Cardinality(state.held) < PinCapacity
       IN state' = [state EXCEPT !.acquire_msg = None,
           !.held = IF admits THEN @ \cup {key} ELSE @,
           !.late_replay = IF Observe /\ replay /\ ~matches /\
                              requested \in (state.published \cap state.published_at_close)
                            THEN requested ELSE @,
           !.late_refusal = @ \/ (Observe /\ ~replay /\ ~eligible /\ state.active > requested[1])]

QueueFloor ==
    /\ state.active # 0
    /\ <<state.active,1>> \in state.held
    /\ state.floor = 0
    /\ state.floor_msg = 0
    /\ state' = [state EXCEPT !.floor_msg = state.active]

DeliverFloor ==
    /\ state.link
    /\ state.floor_msg # 0
    /\ LET matches == state.active = state.floor_msg
           applies == state.active # 0 /\ (matches \/ Variant = "floor_by_route")
       IN state' = [state EXCEPT !.floor_msg = 0, !.floor = IF applies THEN 1 ELSE @,
           !.stale_credit = @ \/ (applies /\ ~matches)]

Publish(key) ==
    /\ key \in state.held \ state.withdrawn
    /\ key \notin state.published
    /\ state' = [state EXCEPT !.published = @ \cup {key}]

Withdraw(key) ==
    /\ key \in state.held \ state.withdrawn
    /\ state' = [state EXCEPT !.withdrawn = @ \cup {key}, !.published = @ \ {key}]

Release(key) ==
    /\ state.link
    /\ key \in state.held \cap state.withdrawn
    /\ Variant # "release_requires_channel" \/ state.active = key[1]
    /\ state' = [state EXCEPT
        !.held = IF Variant = "release_by_serial" THEN {other \in @ : other[2] # key[2]} ELSE @ \ {key},
        !.withdrawn = @ \ {key}, !.held_at_close = @ \ {key},
        !.spent = IF state.active = key[1] THEN @ \cup {key[2]} ELSE @,
        !.old_released = @ \/ (Observe /\ state.active > key[1] /\ key = state.late_replay)]

ToggleLink == state' = [state EXCEPT !.link = ~@]

Next ==
    \/ Open \/ CloseNow \/ QueueClose \/ DeliverClose \/ Issue \/ ReceiveAcquire
    \/ QueueFloor \/ DeliverFloor \/ ToggleLink
    \/ \E key \in GrantKeys : Retry(key) \/ Publish(key) \/ Withdraw(key) \/ Release(key)

Spec == Init /\ [][Next]_state
FairSpec == Spec /\ \A key \in GrantKeys : WF_state(Release(key))

OnlyFreshChannelIsActive == state.active \notin state.retired
PublishedPinsSurvive == state.published \subseteq state.held
EveryGrantWasPlanned == state.held \subseteq state.planned
LateAcquireDoesNotRecreateChannelInterest ==
    \A key \in state.held : key[1] \notin state.retired \/ key \in state.held_at_close
NoStaleClose == ~state.stale_close
NoStaleCredit == ~state.stale_credit
Footprint == Cardinality(state.held) <= PinCapacity /\ state.active <= state.issued

OldReleaseProgress ==
    (<>[]state.link) => (\A key \in GrantKeys : (key \in state.withdrawn) ~> (key \notin state.held))

NeverRotatesWithLivePublishedPin ==
    ~(\E key \in (state.published \cap state.published_at_close) : key[1] < state.active)

NeverReplaysOldAndThenReleases ==
    ~state.old_released

NeverRejectsDelayedOnSuccessor ==
    ~(state.active > 1 /\ state.late_refusal)
=============================================================================
