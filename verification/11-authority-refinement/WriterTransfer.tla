--------------------------- MODULE WriterTransfer ----------------------------
EXTENDS Naturals, Sequences
CONSTANTS Design, Mutation, MaxLsn
VARIABLE state

Grant(holder, epoch, placement) == [holder |-> holder, epoch |-> epoch, placement |-> placement]
NoGrant == Grant(0, 0, 0)
Appends == [grant : {Grant(h, e, p) : h \in 1..2, e \in 1..3, p \in 1..2},
            lsn : 0..(MaxLsn - 1), bytes : {"A", "B"}]
NoRequest == [grant |-> NoGrant, lsn |-> 0, bytes |-> "A"]

Init ==
    state = [
        directory_up |-> TRUE,
        phase |-> "source",
        prepared |-> NoGrant,
        source_grant |-> Grant(1, 1, 1),
        target_grant |-> NoGrant,
        replacement |-> NoGrant,
        source_log |-> <<>>,
        target_log |-> <<>>,
        pending |-> NoRequest,
        observed |-> NoRequest,
        expected_grant |-> NoGrant,
        expected_lsn |-> 0,
        wrote_offline |-> FALSE
    ]

Prepare ==
    /\ state.directory_up
    /\ state.phase = "source"
    /\ state.prepared = NoGrant
    /\ state' = [state EXCEPT !.prepared = state.source_grant]

RotateSource ==
    /\ state.directory_up
    /\ state.phase = "source"
    /\ state.source_grant.epoch = 1
    /\ state' = [state EXCEPT !.source_grant = Grant(2, 2, 1)]

LoseDirectory ==
    /\ state.directory_up
    /\ state' = [state EXCEPT !.directory_up = FALSE]

Seal ==
    /\ state.phase = "source"
    /\ state.prepared # NoGrant
    /\ state' = [state EXCEPT !.phase = "sealed"]

IssueReplacement ==
    /\ Design = "fresh"
    /\ state.phase = "sealed"
    /\ state.directory_up
    /\ state.replacement = NoGrant
    /\ state' = [state EXCEPT !.replacement = Grant(2, state.source_grant.epoch + 1, 2)]

Carry ==
    IF Mutation = "stale_prepare"
    THEN Grant(state.prepared.holder, state.prepared.epoch, 2)
    ELSE IF Mutation = "replace_holder"
    THEN Grant(3 - state.source_grant.holder, state.source_grant.epoch, 2)
    ELSE Grant(state.source_grant.holder, state.source_grant.epoch, 2)

Install ==
    /\ state.phase = "sealed"
    /\ state.replacement # NoGrant \/ Design = "carry"
    /\ state' = [state EXCEPT
        !.phase = "target",
        !.target_grant = IF Design = "carry" THEN Carry ELSE state.replacement,
        !.target_log = state.source_log]

CurrentGrant == IF state.phase = "target" THEN state.target_grant ELSE state.source_grant
CurrentHead == IF state.phase = "target" THEN Len(state.target_log) ELSE Len(state.source_log)

Stage(request) ==
    /\ state.pending = NoRequest
    /\ request.lsn <= CurrentHead
    /\ CurrentHead < MaxLsn
    /\ state' = [state EXCEPT !.pending = request]

Matches(request, grant) ==
    /\ request.grant.epoch = grant.epoch
    /\ request.grant.holder = grant.holder \/ Mutation = "ignore_holder"
    /\ request.grant.placement = grant.placement \/ Mutation = "ignore_placement"

Commit ==
    /\ state.phase # "sealed"
    /\ state.pending # NoRequest
    /\ CurrentHead < MaxLsn
    /\ Matches(state.pending, CurrentGrant)
    /\ state.pending.lsn = CurrentHead \/ Mutation = "ignore_lsn"
    /\ LET record == state.pending
           output == [state EXCEPT !.observed = record,
               !.expected_grant = CurrentGrant, !.expected_lsn = CurrentHead,
               !.pending = NoRequest]
       IN state' = IF state.phase = "target"
                    THEN [output EXCEPT !.target_log = Append(@, record.bytes),
                          !.wrote_offline = @ \/ ~state.directory_up]
                    ELSE [output EXCEPT !.source_log = Append(@, record.bytes)]

Discard ==
    /\ state.pending # NoRequest
    /\ state' = [state EXCEPT !.pending = NoRequest]

Next ==
    \/ Prepare \/ RotateSource \/ LoseDirectory \/ Seal \/ IssueReplacement \/ Install \/ Commit \/ Discard
    \/ \E request \in Appends : Stage(request)

Spec == Init /\ [][Next]_state

FairSpec == Spec /\ WF_state(Seal) /\ WF_state(Install) /\ WF_state(IssueReplacement)

NoWriterSubstitution ==
    state.phase = "target" =>
        /\ state.target_grant.placement = 2
        /\ IF Design = "carry"
           THEN state.target_grant.holder = state.source_grant.holder /\
                state.target_grant.epoch = state.source_grant.epoch
           ELSE state.source_grant.epoch < state.target_grant.epoch

BoundAppend ==
    state.observed = NoRequest \/
        (state.observed.grant = state.expected_grant /\ state.observed.lsn = state.expected_lsn)

ExactPrefix ==
    state.phase = "target" =>
        Len(state.source_log) <= Len(state.target_log) /\
        \A i \in 1..Len(state.source_log) : state.source_log[i] = state.target_log[i]

PreparedMoveCompletes == (state.prepared # NoGrant) ~> (state.phase = "target")

NeverMovesAndAppendsOffline ==
    ~(state.wrote_offline /\ Len(state.source_log) > 0 /\ state.source_grant.epoch = 2)
=============================================================================
