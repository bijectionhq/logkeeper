------------------------------- MODULE ExactFeed ------------------------------
EXTENDS Naturals, Sequences
CONSTANTS MaxLsn, Mutation
VARIABLE state

NoWindow == [first |-> 0, stop |-> 0, seam |-> 0, phase |-> "idle"]
NoSegment == [start |-> 0, stop |-> 0, entries |-> <<>>]

Init ==
    state = [
        history |-> <<>>,
        journal |-> <<>>,
        floor |-> 0,
        checkpoint |-> 0,
        archive |-> <<>>,
        staged |-> NoSegment,
        window |-> NoWindow,
        response |-> <<>>,
        refreshed |-> FALSE,
        served_refreshed |-> FALSE,
        read_floor |-> 0
    ]

Slice(history, first, stop) == SubSeq(history, first + 1, stop)
Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a <= b THEN b ELSE a

Commit(entry) ==
    /\ Len(state.history) < MaxLsn
    /\ state' = [state EXCEPT !.history = Append(@, entry), !.journal = Append(@, entry)]

Checkpoint ==
    /\ state.checkpoint < Len(state.history)
    /\ state' = [state EXCEPT !.checkpoint = Len(state.history)]

StageArchive(stop) ==
    /\ state.staged = NoSegment
    /\ stop \in (Len(state.archive) + 1)..Len(state.history)
    /\ state.floor <= Len(state.archive)
    /\ LET start == IF Mutation = "archive_gap" THEN Len(state.archive) + 1 ELSE Len(state.archive)
       IN /\ start < stop
          /\ state' = [state EXCEPT !.staged =
               [start |-> start, stop |-> stop, entries |-> Slice(state.history, start, stop)]]

PublishArchive ==
    /\ state.staged # NoSegment
    /\ state.staged.start = Len(state.archive) \/ Mutation = "archive_gap"
    /\ state' = [state EXCEPT !.archive = @ \o state.staged.entries, !.staged = NoSegment]

Trim(cut) ==
    /\ cut \in (state.floor + 1)..state.checkpoint
    /\ cut <= Len(state.archive) \/ Mutation = "checkpoint_only"
    /\ state.window.phase # "admitted" \/ state.window.seam = state.window.stop \/ cut <= state.window.seam
    /\ state' = [state EXCEPT !.floor = cut, !.journal = SubSeq(@, cut - state.floor + 1, Len(@))]

Capture(first) ==
    /\ state.window = NoWindow
    /\ first \in 0..Len(state.history)
    /\ state' = [state EXCEPT !.window =
        [first |-> first, stop |-> Len(state.history), seam |-> Max(first, Len(state.archive)),
         phase |-> "planned"]]

Refresh ==
    /\ state.window.phase = "planned"
    /\ state.window.seam < Min(state.floor, state.window.stop)
    /\ state' = [state EXCEPT !.window.seam = Min(state.window.stop, Len(state.archive)), !.refreshed = TRUE]

Admit ==
    /\ state.window.phase = "planned"
    /\ state.window.seam >= Min(state.floor, state.window.stop) \/ Mutation = "skip_recheck"
    /\ state' = [state EXCEPT !.window.phase = "admitted"]

Read ==
    /\ state.window.phase = "admitted"
    /\ LET span == state.window
           seam == Min(span.seam, span.stop)
           archiveStop == IF Mutation = "duplicate_seam"
                          THEN Min(Min(seam + 1, span.stop), Len(state.archive))
                          ELSE seam
           journalStart == Max(seam, state.floor) - state.floor
           journalStop == Max(span.stop, state.floor) - state.floor
       IN state' = [state EXCEPT !.window.phase = "finished",
            !.response = Slice(state.archive, span.first, archiveStop) \o
                         Slice(state.journal, journalStart, journalStop),
            !.served_refreshed = state.refreshed, !.read_floor = state.floor]

Next ==
    \/ Checkpoint \/ PublishArchive \/ Refresh \/ Admit \/ Read
    \/ \E entry \in {1, 2} : Commit(entry)
    \/ \E cut \in 0..MaxLsn : StageArchive(cut) \/ Trim(cut) \/ Capture(cut)

Spec == Init /\ [][Next]_state

ArchiveIsExact ==
    state.archive = Slice(state.history, 0, Len(state.archive))

NoUncoveredTrim == state.floor <= Len(state.archive)

SuccessfulFeedIsExact ==
    state.window.phase = "finished" =>
      state.response = Slice(state.history, state.window.first, state.window.stop)

NeverRefreshesAndCompletes ==
    ~(state.served_refreshed /\ state.read_floor > 0 /\ state.window.first < state.window.stop)

NeverJoinsBothSources ==
    ~(state.window.phase = "finished" /\ state.read_floor > 0 /\
      state.window.first < state.window.seam /\ state.window.seam < state.window.stop)
=============================================================================
