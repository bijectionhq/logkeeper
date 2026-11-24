------------------------------ MODULE Retention ------------------------------
EXTENDS Naturals
CONSTANTS MaxLsn, ReplayBudget, RetainedBudget, Mutation
VARIABLE state

None == MaxLsn + 1
Original == "original"
Foreign == "foreign"
EmptyReplay == [through |-> None, cursor |-> None, identity |-> Original,
                delivered |-> 0, done |-> FALSE]

Init ==
    state = [
        head |-> 0,
        uploaded |-> 0,
        published |-> 0,
        floor |-> 0,
        replay_intent |-> None,
        trim_intent |-> None,
        hold |-> None,
        replay |-> EmptyReplay,
        closed_at_capacity |-> FALSE
    ]

Append ==
    /\ state.head < MaxLsn
    /\ (state.head + 1 - state.published <= ReplayBudget \/ Mutation = "no_recovery_cap")
    /\ (state.head + 1 - state.floor <= RetainedBudget \/ Mutation = "no_retained_cap")
    /\ state' = [state EXCEPT !.head = @ + 1]

Upload(cut) ==
    /\ cut \in (state.uploaded + 1)..state.head
    /\ state' = [state EXCEPT !.uploaded = cut]

Publish ==
    /\ state.published < state.uploaded
    /\ state' = [state EXCEPT !.published = state.uploaded]

PrepareReplay(lsn) ==
    /\ state.replay_intent = None
    /\ state.hold = None
    /\ lsn \in state.floor..(state.head - 1)
    /\ state.head > 0
    /\ state' = [state EXCEPT !.replay_intent = lsn]

AdmitReplay ==
    /\ state.replay_intent # None
    /\ (state.floor <= state.replay_intent \/ Mutation = "stale_replay")
    /\ state' = [state EXCEPT !.hold = state.replay_intent, !.replay_intent = None]

CloseReplay ==
    /\ state.hold # None \/ state.replay_intent # None
    /\ state' = [state EXCEPT !.hold = None, !.replay_intent = None,
        !.replay = EmptyReplay,
        !.closed_at_capacity = @ \/ (state.hold = state.floor /\
                                 state.head - state.floor = RetainedBudget)]

CheckpointLimit ==
    IF Mutation = "use_uploaded" THEN state.uploaded ELSE state.published

PrepareTrim(cut) ==
    /\ state.trim_intent = None
    /\ cut \in (state.floor + 1)..CheckpointLimit
    /\ cut <= state.hold
    /\ state' = [state EXCEPT !.trim_intent = cut]

Trim ==
    /\ state.trim_intent # None
    /\ (state.trim_intent <= state.hold \/ Mutation = "stale_trim")
    /\ state' = [state EXCEPT !.floor = state.trim_intent, !.trim_intent = None]

AbandonTrim ==
    /\ state.trim_intent # None
    /\ state' = [state EXCEPT !.trim_intent = None]

Next ==
    \/ Append \/ Publish \/ AdmitReplay \/ CloseReplay \/ Trim \/ AbandonTrim
    \/ \E lsn \in 0..MaxLsn : Upload(lsn) \/ PrepareReplay(lsn) \/ PrepareTrim(lsn)

Spec == Init /\ [][Next]_state

PublishedBeforeTrim == state.floor <= state.published
ReplayProtected == state.floor <= state.hold
RecoveryBound == state.head - state.published <= ReplayBudget
RetainedBound == state.head - state.floor <= RetainedBudget

NeverPausedByHold ==
    ~(state.hold = state.floor /\ state.head < MaxLsn /\
      state.head - state.floor = RetainedBudget /\ state.head = state.published /\
      ~ENABLED Append)

NeverReclaimsAfterClose ==
    ~(state.closed_at_capacity /\ state.floor > 0 /\ state.hold = None /\
      state.head > RetainedBudget)
\* A second specification keeps the original terminal cut while append and
\* trim interleave with delivery. Original and Foreign represent distinct
\* digests at the same numeric cut.
AdmitPageReplay ==
    /\ state.replay_intent # None
    /\ state.floor <= state.replay_intent
    /\ state' = [state EXCEPT !.hold = state.replay_intent, !.replay_intent = None,
        !.replay = [EmptyReplay EXCEPT !.through = state.head,
                                      !.cursor = state.replay_intent]]

DeliverPageRecord(next, identity) ==
    /\ state.hold # None
    /\ ~state.replay.done
    /\ state.replay.cursor < next
    /\ next <= state.replay.through
    /\ (next = state.replay.cursor + 1 \/ Mutation = "skip_record")
    /\ (identity = Original \/ (Mutation = "foreign_terminal" /\ next = state.replay.through))
    /\ state' = [state EXCEPT !.replay.cursor = next, !.replay.identity = identity,
                              !.replay.delivered = @ + 1]

EndPageReplay ==
    /\ state.hold # None
    /\ ~state.replay.done
    /\ ((state.replay.cursor = state.replay.through /\ state.replay.identity = Original)
        \/ Mutation = "early_end")
    /\ state' = [state EXCEPT !.replay.done = TRUE]

ReplayNext ==
    \/ Append \/ Publish \/ AdmitPageReplay \/ CloseReplay \/ Trim \/ AbandonTrim
    \/ \E lsn \in 0..MaxLsn : Upload(lsn) \/ PrepareReplay(lsn) \/ PrepareTrim(lsn)
    \/ \E next \in 1..MaxLsn, identity \in {Original, Foreign} : DeliverPageRecord(next, identity)
    \/ EndPageReplay

ReplaySpec == Init /\ [][ReplayNext]_state

ReplayContiguous == state.hold # None =>
    /\ state.hold <= state.replay.cursor
    /\ state.replay.cursor <= state.replay.through
    /\ state.replay.delivered = state.replay.cursor - state.hold

ReplayOriginal == state.replay.identity = Original
ReplayExactEnd == state.replay.done =>
    state.replay.cursor = state.replay.through /\ state.replay.identity = Original

NeverCompletesWhileHeadAdvances ==
    ~(state.replay.done /\ state.replay.through < state.head)
=============================================================================
