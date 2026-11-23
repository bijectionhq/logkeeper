------------------------------ MODULE Retention ------------------------------
EXTENDS Naturals
CONSTANTS MaxLsn, ReplayBudget, RetainedBudget, Mutation
VARIABLE state

None == MaxLsn + 1

Init ==
    state = [
        head |-> 0,
        uploaded |-> 0,
        published |-> 0,
        floor |-> 0,
        replay_intent |-> None,
        trim_intent |-> None,
        hold |-> None,
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
=============================================================================
