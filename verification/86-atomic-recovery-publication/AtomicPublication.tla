---------------------------- MODULE AtomicPublication ------------------------
EXTENDS Naturals

CONSTANTS Variant, Scenario
VARIABLE state

Key(lineage, revision, frontier, run) ==
    [lineage |-> lineage, revision |-> revision, frontier |-> frontier, run |-> run]
Origin == Key(1, 1, 2, 1)

Init ==
    state = [key |-> Origin, pending |-> {}, open |-> {}, fallback |-> FALSE, checked |-> FALSE,
             changed |-> FALSE, online |-> TRUE, admitted |-> FALSE, finished |-> FALSE, stopped |-> FALSE,
             wrongMount |-> FALSE, replaced |-> FALSE, issuedOffline |-> FALSE, finishedStopped |-> FALSE]

Prepare ==
    /\ state.pending = {}
    /\ ~state.changed
    /\ state' = [state EXCEPT !.pending = {state.key}]

Check ==
    /\ Scenario = "advance"
    /\ state.pending = {state.key} /\ ~state.checked
    /\ state' = [state EXCEPT !.checked = TRUE]

Move ==
    CASE Scenario = "advance" -> [state.key EXCEPT !.frontier = @ + 1]
      [] Scenario = "replace" -> [state.key EXCEPT !.revision = @ + 1]
      [] Scenario = "restart" -> [state.key EXCEPT !.run = @ + 1]
      [] Scenario = "reopen" -> [state.key EXCEPT !.run = @ + 1, !.frontier = @ + 1]
      [] OTHER -> [state.key EXCEPT !.lineage = @ + 1]

Advance ==
    /\ Scenario \in {"advance", "replace", "restart", "reopen", "reuse-route"}
    /\ state.pending # {} /\ ~state.changed
    /\ Scenario # "advance" \/ state.checked
    /\ state' = [state EXCEPT !.key = Move, !.changed = TRUE, !.open = {}]

Restage ==
    /\ Scenario = "reopen" /\ state.changed
    /\ state.open = {} /\ state.key \notin state.pending
    /\ state' = [state EXCEPT !.pending = @ \cup {state.key}]

OpenCurrent ==
    /\ Scenario = "duplicate" /\ state.pending # {} /\ ~state.fallback
    /\ state.open = {}
    /\ state' = [state EXCEPT !.fallback = TRUE, !.open = {state.key}]

Matches(image) ==
    CASE Variant = "reuse-check" -> state.checked
      [] Variant = "skip-run" -> [image EXCEPT !.run = state.key.run] = state.key
      [] Variant = "skip-revision" -> [image EXCEPT !.revision = state.key.revision] = state.key
      [] Variant = "skip-lineage" -> [image EXCEPT !.lineage = state.key.lineage] = state.key
      [] OTHER -> image = state.key

Attach ==
    /\ state.pending # {}
    /\ (state.open = {} \/ Variant = "overwrite")
    /\ \E image \in state.pending :
        /\ Matches(image)
        /\ state' = [state EXCEPT !.pending = {}, !.open = {image},
                      !.wrongMount = (image # state.key), !.replaced = (state.open # {})]

LoseQuorum ==
    /\ Scenario \in {"uncertain", "overlap"} /\ state.online
    /\ IF Scenario = "overlap" THEN state.admitted ELSE state.pending # {}
    /\ state' = [state EXCEPT !.online = FALSE]

Admit ==
    /\ state.open = {state.key} /\ ~state.admitted
    /\ Scenario \in {"uncertain", "overlap", "stopped"}
    /\ (state.online \/ Variant = "image-authorizes")
    /\ state' = [state EXCEPT !.admitted = TRUE, !.issuedOffline = ~state.online]

Stop ==
    /\ Scenario = "stopped" /\ state.admitted /\ ~state.stopped
    /\ state' = [state EXCEPT !.stopped = TRUE]

Finish ==
    /\ (Scenario = "overlap" /\ ~state.online) \/ (Scenario = "stopped" /\ state.stopped)
    /\ state.admitted /\ ~state.finished
    /\ ~state.stopped \/ Variant = "ignore-stop"
    /\ Variant # "require-online-at-delivery"
    /\ state' = [state EXCEPT !.finished = TRUE, !.finishedStopped = state.stopped]

Next == Prepare \/ Check \/ Advance \/ Restage \/ OpenCurrent \/ Attach \/ LoseQuorum \/ Admit \/ Stop \/ Finish
Spec == Init /\ [][Next]_state
FairOverlap == Spec /\ WF_state(Prepare) /\ WF_state(Attach) /\ WF_state(Admit) /\
    WF_state(LoseQuorum) /\ WF_state(Finish)
FairReopen == Spec /\ WF_state(Prepare) /\ WF_state(Advance) /\ WF_state(Restage) /\ WF_state(Attach)

ExactAtEffect == ~state.wrongMount
SingleAttach == ~state.replaced
OnlyAuthorityAdmits == ~state.issuedOffline
OnlyHeldCompletes == ~state.finishedStopped
CompletesProtected == <>state.finished
ReopensCurrent == <>(state.changed /\ state.open = {state.key})
=============================================================================
