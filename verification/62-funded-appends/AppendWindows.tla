---------------------------- MODULE AppendWindows ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Capacity, Variant
Streams == {1, 2}
WindowSize == 2
Sizes == 1..WindowSize

VARIABLES debits, windows, move, quoted, cursors, histories, cuts, replayed, expected, fullAppend
vars == <<debits, windows, move, quoted, cursors, histories, cuts, replayed, expected, fullAppend>>

Used == WindowSize * Cardinality(debits) + move
Init ==
    /\ debits = {} /\ windows = {} /\ move = 0 /\ quoted = {}
    /\ cursors = [stream \in Streams |-> 0]
    /\ histories = [stream \in Streams |-> <<>>]
    /\ cuts = [stream \in Streams |-> 0]
    /\ replayed = [stream \in Streams |-> <<>>]
    /\ expected = replayed /\ fullAppend = FALSE

Quote(stream) ==
    /\ Variant = "stale_capacity" /\ Used + WindowSize <= Capacity
    /\ quoted' = quoted \cup {stream}
    /\ UNCHANGED <<debits, windows, move, cursors, histories, cuts, replayed, expected, fullAppend>>

Grant(stream) ==
    /\ stream \notin windows
    /\ Used + WindowSize <= Capacity \/ (Variant = "stale_capacity" /\ stream \in quoted)
    /\ debits' = debits \cup {stream} /\ windows' = windows \cup {stream}
    /\ UNCHANGED <<move, quoted, cursors, histories, cuts, replayed, expected, fullAppend>>

PrepareMove == /\ move = 0 /\ Used < Capacity /\ move' = 1
               /\ UNCHANGED <<debits, windows, quoted, cursors, histories, cuts, replayed, expected, fullAppend>>

AppendRecord(stream, offset, size) ==
    /\ stream \in windows \/ Variant = "without_window"
    /\ offset = cursors[stream] \/ Variant = "reuse_offset"
    /\ offset + size <= WindowSize /\ Len(histories[stream]) < WindowSize
    /\ cursors' = [cursors EXCEPT ![stream] = offset + size]
    /\ histories' = [histories EXCEPT ![stream] = Append(@, <<offset, size>>)]
    /\ fullAppend' = (fullAppend \/ (stream = 1 /\ Used = Capacity /\ move = 1))
    /\ UNCHANGED <<debits, windows, move, quoted, cuts, replayed, expected>>

Trim(stream) ==
    /\ cuts[stream] < Len(histories[stream])
    /\ cuts' = [cuts EXCEPT ![stream] = Len(histories[stream])]
    /\ UNCHANGED <<debits, windows, move, quoted, cursors, histories, replayed, expected, fullAppend>>

RefundLive(stream) ==
    /\ Variant = "refund_live" /\ stream \in debits
    /\ debits' = debits \ {stream}
    /\ UNCHANGED <<windows, move, quoted, cursors, histories, cuts, replayed, expected, fullAppend>>

Recover(stream) ==
    /\ expected' = [expected EXCEPT ![stream] = histories[stream]]
    /\ replayed' = [replayed EXCEPT ![stream] =
        IF Variant = "current_capacity_on_replay" /\ Used = Capacity THEN <<>>
        ELSE histories[stream]]
    /\ UNCHANGED <<debits, windows, move, quoted, cursors, histories, cuts, fullAppend>>

Next ==
    \/ PrepareMove
    \/ \E stream \in Streams :
        \/ Quote(stream) \/ Grant(stream) \/ Trim(stream) \/ RefundLive(stream) \/ Recover(stream)
        \/ \E offset \in 0..WindowSize, size \in Sizes : AppendRecord(stream, offset, size)

Spec == Init /\ [][Next]_vars
Fits == Used <= Capacity
ExactLiveDebit ==
    /\ windows \subseteq debits
    /\ \A stream \in Streams : cuts[stream] < Len(histories[stream]) => stream \in debits
DisjointRanges ==
    \A stream \in Streams : \A first, next \in 1..Len(histories[stream]) :
        first < next => histories[stream][first][1] + histories[stream][first][2] <= histories[stream][next][1]
OriginalReplies == replayed = expected
NeverAppendAtFullPool == ~fullAppend
=============================================================================
