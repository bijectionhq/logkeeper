----------------------------- MODULE CancelMove -----------------------------
EXTENDS Naturals
CONSTANTS MaxNonce, Mutation
VARIABLE state

Init ==
    state = [issued |-> 0, slot |-> 0, cancel_request |-> 0, aborted |-> {},
             sealed |-> 0, installed |-> FALSE, linked |-> TRUE]

Prepare ==
    /\ state.slot = 0
    /\ state.issued < MaxNonce
    /\ ~state.installed
    /\ state' = [state EXCEPT !.issued = @ + 1, !.slot = state.issued + 1]

RequestCancel ==
    /\ state.slot # 0
    /\ state.cancel_request # state.slot
    /\ state' = [state EXCEPT !.cancel_request = state.slot]

IssueAbort ==
    /\ state.linked
    /\ state.slot # 0
    /\ state.cancel_request = state.slot
    /\ state.slot \notin state.aborted
    /\ state.sealed = 0
    /\ state' = [state EXCEPT !.aborted = @ \cup {state.slot}]

Seal ==
    /\ state.linked
    /\ state.slot # 0
    /\ state.sealed = 0
    /\ state.slot \notin state.aborted \/ Mutation = "ignore_abort"
    /\ state' = [state EXCEPT !.sealed = state.slot]

Cancel ==
    /\ state.slot # 0
    /\ (state.slot \in state.aborted /\ state.linked) \/
        (Mutation = "abort_by_stream" /\ state.aborted # {}) \/
        (Mutation = "no_source_evidence" /\ ~state.linked)
    /\ state' = [state EXCEPT !.slot = 0]

Install ==
    /\ state.linked
    /\ state.slot # 0
    /\ state.sealed = state.slot
    /\ state' = [state EXCEPT !.slot = 0, !.installed = TRUE]

ToggleLink ==
    state' = [state EXCEPT !.linked = ~@]

Next == Prepare \/ RequestCancel \/ IssueAbort \/ Seal \/ Cancel \/ Install \/ ToggleLink

Spec == Init /\ [][Next]_state

FairSpec ==
    /\ Spec
    /\ WF_state(IssueAbort)
    /\ WF_state(Cancel)
    /\ WF_state(Install)

SealAndAbortAreExclusive ==
    state.sealed \notin state.aborted

SealRetainsItsDestination ==
    state.sealed = 0 \/ state.installed \/ state.slot = state.sealed

RequestedReleaseWithSource ==
    (<>[] state.linked) =>
        \A nonce \in 1..MaxNonce :
            (state.cancel_request = nonce /\ state.slot = nonce) ~> (state.slot # nonce)

RequestedReleaseWithoutSource ==
    \A nonce \in 1..MaxNonce :
        (state.cancel_request = nonce /\ state.slot = nonce) ~> (state.slot # nonce)

NeverCancelsThenInstallsNew ==
    ~(state.sealed > 1 /\ state.installed /\ 1 \in state.aborted)
=============================================================================
