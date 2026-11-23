----------------------------- MODULE CheckpointCut ----------------------------
EXTENDS Naturals, Sequences
CONSTANTS MaxLsn, Mutation
VARIABLE state

Descriptor(scope, cut, prefix, image, complete, format) ==
    [scope |-> scope, cut |-> cut, prefix |-> prefix, image |-> image,
     complete |-> complete, format |-> format]

NoReceipt == Descriptor("none", 0, <<>>, 0, FALSE, 0)
Genesis == Descriptor("child", 0, <<>>, 6, TRUE, 1)

RECURSIVE Sum(_)
Sum(records) == IF Len(records) = 0 THEN 0 ELSE Head(records) + Sum(Tail(records))

Init ==
    state = [
        born |-> FALSE,
        history |-> <<>>,
        prepared |-> NoReceipt,
        published |-> NoReceipt,
        floor |-> 0,
        captured |-> FALSE,
        requested |-> 0,
        selected |-> NoReceipt,
        finished |-> FALSE,
        response |-> 0, read_floor |-> 0, head_at_read |-> 0
    ]

At(end) == 6 + Sum(SubSeq(state.history, 1, end))

ForkGenesis ==
    /\ ~state.born
    /\ state' = [state EXCEPT !.born = TRUE, !.published = Genesis]

Commit(record) ==
    /\ state.born
    /\ Len(state.history) < MaxLsn
    /\ state' = [state EXCEPT !.history = Append(@, record)]

Stage(end, kind) ==
    /\ state.born
    /\ state.prepared = NoReceipt
    /\ end \in state.published.cut..Len(state.history)
    /\ kind # "swapped" \/ (end = 2 /\ state.history[1] # state.history[2])
    /\ LET scope == IF kind = "foreign" THEN "parent" ELSE "child"
           prefix == IF kind = "swapped" THEN <<state.history[2], state.history[1]>>
                     ELSE SubSeq(state.history, 1, end)
           value == IF kind = "wrong_root" THEN At(end) + 1 ELSE At(end)
           format == IF kind = "wrong_format" THEN 2 ELSE 1
       IN state' = [state EXCEPT !.prepared =
            Descriptor(scope, end, prefix, value, kind # "incomplete", format)]

Discard ==
    /\ state.prepared # NoReceipt
    /\ state' = [state EXCEPT !.prepared = NoReceipt]

Publish ==
    /\ state.prepared # NoReceipt
    /\ state.prepared.cut >= state.published.cut
    /\ state.prepared.scope = "child" \/ Mutation = "numeric_scope"
    /\ state.prepared.prefix = SubSeq(state.history, 1, state.prepared.cut) \/ Mutation = "by_state"
    /\ state.prepared.image = At(state.prepared.cut) \/ Mutation = "loose_root"
    /\ state.prepared.complete \/ Mutation = "manifest_only"
    /\ state.prepared.format = 1 \/ Mutation = "ignore_format"
    /\ state' = [state EXCEPT !.published = state.prepared, !.prepared = NoReceipt]

Trim ==
    /\ state.published.cut > state.floor
    /\ state.selected = NoReceipt \/ state.finished \/ state.published.cut <= state.selected.cut
    /\ state' = [state EXCEPT !.floor = state.published.cut]

Capture ==
    /\ state.born
    /\ ~state.captured
    /\ state' = [state EXCEPT !.captured = TRUE, !.requested = Len(state.history)]

Select ==
    /\ state.captured
    /\ state.selected = NoReceipt
    /\ state.floor <= state.published.cut
    /\ state.published.cut <= state.requested \/ Mutation = "newer_root"
    /\ state' = [state EXCEPT !.selected = state.published]

Read ==
    /\ state.selected # NoReceipt
    /\ ~state.finished
    /\ LET stop == IF Mutation = "follow_head" THEN Len(state.history) ELSE state.requested
           last == IF Mutation = "omit_tail" /\ stop > state.selected.cut THEN stop - 1 ELSE stop
           received == SubSeq(state.history, state.selected.cut + 1, last)
       IN state' = [state EXCEPT !.finished = TRUE, !.response = state.selected.image + Sum(received),
            !.read_floor = state.floor, !.head_at_read = Len(state.history)]

Next ==
    \/ ForkGenesis \/ Discard \/ Publish \/ Trim \/ Capture \/ Select \/ Read
    \/ \E record \in 1..2 : Commit(record)
    \/ \E end \in 0..MaxLsn, kind \in
         {"exact", "foreign", "swapped", "wrong_root", "incomplete", "wrong_format"} : Stage(end, kind)

Spec == Init /\ [][Next]_state

PublishedOwnScope ==
    state.born => state.published.scope = "child"

PublishedExactHistory ==
    state.born => state.published.prefix = SubSeq(state.history, 1, state.published.cut)

PublishedReconstructs ==
    state.born => state.published.complete /\ state.published.format = 1 /\
        state.published.image = At(state.published.cut)

ReaderInsulated ==
    state.selected # NoReceipt /\ ~state.finished => state.floor <= state.selected.cut

ResponseAtRequestedCut ==
    state.finished => state.response = At(state.requested)

NeverReadsForkGenesis ==
    ~(state.finished /\ state.requested = 0 /\ state.response = 6)

NeverRecoversFromTrimWhileWritesContinue ==
    ~(state.finished /\ state.read_floor > 0 /\ state.selected.cut < state.requested /\
      state.requested < state.head_at_read)
=============================================================================
