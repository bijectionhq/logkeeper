------------------------------- MODULE Handoff ------------------------------
EXTENDS Naturals, Sequences
CONSTANTS Design, Mutation, MaxLsn
VARIABLE state

Init ==
    state = [
        directory_up |-> TRUE,
        linked |-> TRUE,
        authorized |-> FALSE,
        sealed |-> FALSE,
        installed |-> FALSE,
        published |-> FALSE,
        active |-> FALSE,
        source |-> <<>>,
        target |-> <<>>,
        installed_end |-> 0,
        appended_during_outage |-> FALSE,
        activated_disconnected |-> FALSE
    ]

Authorize ==
    /\ state.directory_up
    /\ ~state.authorized
    /\ state' = [state EXCEPT !.authorized = TRUE]

AppendSource(payload) ==
    /\ ~state.sealed
    /\ Len(state.source) < MaxLsn
    /\ state' = [state EXCEPT !.source = Append(@, payload)]

AppendTarget(payload) ==
    /\ state.active
    /\ Len(state.target) < MaxLsn
    /\ state' = [state EXCEPT !.target = Append(@, payload),
        !.appended_during_outage = @ \/ ~state.directory_up]

Precopy ==
    /\ state.authorized
    /\ state.linked
    /\ ~state.installed
    /\ ~state.active
    /\ state.target # state.source
    /\ state' = [state EXCEPT !.target = state.source]

Seal ==
    /\ state.authorized
    /\ ~state.sealed
    /\ state' = [state EXCEPT !.sealed = TRUE]

Install ==
    /\ state.sealed
    /\ state.linked
    /\ ~state.installed
    /\ ~state.active
    /\ LET copied == IF Mutation = "trust_precopy" THEN state.target ELSE state.source
       IN state' = [state EXCEPT
           !.installed = TRUE, !.target = copied, !.installed_end = Len(copied)]

Publish ==
    /\ state.directory_up
    /\ ~state.published
    /\ IF Design = "directory" THEN state.installed ELSE state.active
    /\ state' = [state EXCEPT !.published = TRUE]

Activate ==
    /\ ~state.active
    /\ state.authorized
    /\ ((state.installed /\ (Design = "portable" \/ state.published)) \/
        (Mutation = "skip_seal" /\ ~state.linked))
    /\ state' = [state EXCEPT !.active = TRUE,
        !.activated_disconnected = ~state.linked /\ ~state.directory_up]

Reopen ==
    /\ Mutation = "reopen_source"
    /\ state.sealed
    /\ ~state.linked
    /\ state' = [state EXCEPT !.sealed = FALSE]

ToggleDirectory ==
    /\ state.directory_up \/ Mutation # "permanent_directory_loss"
    /\ state' = [state EXCEPT !.directory_up = ~@]

ToggleLink ==
    state' = [state EXCEPT !.linked = ~@]

Next ==
    \/ Authorize \/ Precopy \/ Seal \/ Install \/ Publish \/ Activate \/ Reopen
    \/ ToggleDirectory \/ ToggleLink
    \/ \E payload \in {"A", "B"} : AppendSource(payload) \/ AppendTarget(payload)

Spec == Init /\ [][Next]_state

FairSpec ==
    /\ Spec
    /\ WF_state(Seal)
    /\ WF_state(Install)
    /\ WF_state(Publish)
    /\ WF_state(Activate)

SingleAuthority == state.sealed \/ ~state.active

NoFork ==
    state.active => \A lsn \in (1..Len(state.source)) \cap (1..Len(state.target)) :
        state.source[lsn] = state.target[lsn]

ExactCut ==
    state.active =>
        /\ state.installed
        /\ state.installed_end = Len(state.source)
        /\ state.installed_end <= Len(state.target)
        /\ \A lsn \in 1..state.installed_end : state.source[lsn] = state.target[lsn]

WithDirectoryProgress ==
    (<>[] (state.authorized /\ state.linked /\ state.directory_up)) => <>state.active

LinkOnlyProgress ==
    (<>[] (state.authorized /\ state.linked)) => <>state.active

InstalledProgress == state.installed ~> state.active

NeverAppendsAfterDirectoryLoss ==
    ~(state.appended_during_outage /\ Len(state.source) > 0)

NeverActivatesWithLinkDown ==
    ~state.activated_disconnected
=============================================================================
