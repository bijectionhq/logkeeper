------------------------------- MODULE WALErasure -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Layout, Fault
Groups == {1, 2}
Tenant == 1
Neighbour == 2
OldKey == <<Tenant, 1>>
NewKey == <<Tenant, 2>>
OtherKey == <<Neighbour, 1>>
Frame(g, k, slot, form) ==
    [group |-> g, generation |-> k, slot |-> slot, form |-> form]
Old == Frame(Tenant, 1, "before", "cipher")
RawOld == Frame(Tenant, 1, "before", "raw")
Other == Frame(Neighbour, 1, "before", "cipher")
Clean == Frame(Tenant, 2, "clean-root", "cipher")
OtherNext == Frame(Neighbour, 1, "after", "cipher")
PostCut(k) == Frame(Tenant, k, "after", "cipher")
IsOld(row) == row.group = Tenant /\ row.generation = 1
Key(row) == <<row.group, row.generation>>

Files == IF Layout = "shared" THEN {0} ELSE Groups
File(g) == IF Layout = "shared" THEN 0 ELSE g
InitialLog == [f \in Files |->
    IF f = 0 THEN <<Old, Other>> ELSE IF f = Tenant THEN <<Old>> ELSE <<Other>>]

VARIABLES log, archive, keys, held, prepared, visible, durable,
          committed, revoked, crashed, compacted, appended
vars == <<log, archive, keys, held, prepared, visible, durable,
          committed, revoked, crashed, compacted, appended>>

Init ==
    /\ log = InitialLog
    /\ archive = <<Old>>
    /\ keys = {OldKey, NewKey, OtherKey}
    /\ held = TRUE
    /\ prepared = FALSE /\ visible = 1 /\ durable = 1
    /\ committed = FALSE /\ revoked = FALSE /\ crashed = 0
    /\ compacted = FALSE /\ appended = {}

Stage ==
    /\ ~prepared
    /\ prepared' = TRUE
    /\ log' = [log EXCEPT ![File(Tenant)] = Append(@, Clean)]
    /\ UNCHANGED <<archive, keys, held, visible, durable, committed, revoked,
                   crashed, compacted, appended>>

Publish ==
    /\ prepared /\ visible = 1
    /\ visible' = 2
    /\ UNCHANGED <<log, archive, keys, held, prepared, durable, committed, revoked,
                   crashed, compacted, appended>>

Settle ==
    /\ visible # durable
    /\ durable' = visible
    /\ UNCHANGED <<log, archive, keys, held, prepared, visible, committed, revoked,
                   crashed, compacted, appended>>

Crash ==
    /\ crashed = 0
    /\ \E survived \in {visible, durable} : visible' = survived /\ durable' = survived
    /\ crashed' = IF revoked THEN 2 ELSE 1
    /\ UNCHANGED <<log, archive, keys, held, prepared, committed, revoked,
                   compacted, appended>>

Commit ==
    /\ ~committed /\ visible = 2
    /\ durable = 2 \/ Fault = "early-rotation"
    /\ committed' = TRUE
    /\ held' = IF Fault = "revoke-hold" THEN FALSE ELSE held
    /\ UNCHANGED <<log, archive, keys, prepared, visible, durable, revoked,
                   crashed, compacted, appended>>

\* The deadline action abstracts exact custody destruction and cache invalidation.
Revoke ==
    /\ committed /\ ~revoked
    /\ revoked' = TRUE
    /\ keys' = CASE Fault = "key-alias" -> keys
                  [] Fault = "shared-key" -> keys \ {OldKey, OtherKey}
                  [] OTHER -> keys \ {OldKey}
    /\ UNCHANGED <<log, archive, held, prepared, visible, durable, committed,
                   crashed, compacted, appended>>

AppendNext(g) ==
    /\ g \notin appended
    /\ g = Neighbour \/ committed
    /\ LET row == IF g = Neighbour THEN OtherNext
                  ELSE PostCut(IF Fault = "stale-append" THEN 1 ELSE 2) IN
         log' = [log EXCEPT ![File(g)] = Append(@, row)]
    /\ appended' = appended \cup {g}
    /\ UNCHANGED <<archive, keys, held, prepared, visible, durable,
                   committed, revoked, crashed, compacted>>

\* Abstract a durably selected compacted replacement. The separate archive
\* models retained old ciphertext outside the replacement's named scope.
Compact ==
    /\ revoked /\ ~compacted
    /\ compacted' = TRUE
    /\ log' = [log EXCEPT ![File(Tenant)] = SelectSeq(@, LAMBDA row :
        (Fault = "copy-obsolete" \/ ~IsOld(row))
        /\ (Fault # "drop-neighbour" \/ row.group # Neighbour))]
    /\ UNCHANGED <<archive, keys, held, prepared, visible, durable, committed, revoked,
                   crashed, appended>>

LeakPlaintext ==
    /\ Fault = "raw-archive" /\ archive = <<Old>> /\ ~committed
    /\ archive' = Append(archive, RawOld)
    /\ UNCHANGED <<log, keys, held, prepared, visible, durable, committed, revoked,
                   crashed, compacted, appended>>

Next == LeakPlaintext \/ Stage \/ Publish \/ Settle \/ Crash \/ Commit \/ Revoke \/ Compact
        \/ (\E g \in Groups : AppendNext(g))
Spec == Init /\ [][Next]_vars

Rows(s) == {s[i] : i \in 1..Len(s)}
DiskRows == Rows(archive) \cup UNION {Rows(log[f]) : f \in Files}
GroupLog(g) == SelectSeq(log[File(g)], LAMBDA row : row.group = g)
Readable(row) == row.form = "raw" \/ Key(row) \in keys
RecoveryRoot(k) == IF k = 1 THEN Old ELSE Clean
NoResurrection == committed => {visible, durable} = {2}
ExactRecovery ==
    /\ \A k \in {visible, durable} :
           RecoveryRoot(k) \in Rows(GroupLog(Tenant)) /\ Readable(RecoveryRoot(k))
    /\ Tenant \in appended => PostCut(2) \in Rows(GroupLog(Tenant)) /\ NewKey \in keys
NoPlaintextAfterDeadline == revoked =>
    \A row \in DiskRows : IsOld(row) => ~Readable(row)
HeldOutcome == IF ~held THEN "lost" ELSE
               IF OldKey \in keys THEN "readable" ELSE "rtdb/erased-under-view"
D02HeldView ==
    held /\ HeldOutcome = IF revoked THEN "rtdb/erased-under-view" ELSE "readable"
NeighbourUnchanged ==
    OtherKey \in keys /\
    GroupLog(Neighbour) = IF Neighbour \in appended THEN <<Other, OtherNext>> ELSE <<Other>>
ScopedCleanup == compacted => \A row \in Rows(GroupLog(Tenant)) : ~IsOld(row)
CiphertextOnly == \A row \in DiskRows : row.form = "cipher"

DeadlineWitness == ~(committed /\ revoked /\ crashed = 2 /\ compacted /\ appended = Groups
                     /\ Old \in Rows(archive) /\ ~Readable(Old))
=============================================================================
