----------------------------- MODULE FundedWindowMove -------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Capacity, Variant
Pools == {1, 2}
Moves == {1, 2}
Extents == 1..5
Plan(move) == IF move = 1 THEN {2, 3} ELSE {4, 5}
Pool(version) == IF version \in {1, 2, 5} THEN 1 ELSE 2
Window(move) == IF move = 1 THEN 2 ELSE 4

VARIABLES phase, charged, holders, ordinary, windows, borrowed, fullInstall
vars == <<phase, charged, holders, ordinary, windows, borrowed, fullInstall>>

Init ==
    /\ phase = [move \in Moves |-> "open"]
    /\ charged = {1} /\ holders = [version \in Extents |-> 0]
    /\ ordinary = [pool \in Pools |-> 0] /\ windows = [move \in Moves |-> 0]
    /\ borrowed = TRUE /\ fullInstall = FALSE

Used(pool) == ordinary[pool] + Cardinality({version \in charged : Pool(version) = pool})
Owns(move, version) == version \in charged /\ holders[version] = move
Full(move) == \A version \in Plan(move) : Owns(move, version)

Prepare(move, version) ==
    /\ phase[move] = "open" /\ version \in Plan(move) \ charged
    /\ Used(Pool(version)) < Capacity
    /\ charged' = charged \cup {version}
    /\ holders' = [holders EXCEPT ![version] = move]
    /\ UNCHANGED <<phase, ordinary, windows, borrowed, fullInstall>>

AdmitOrdinary(pool) ==
    /\ Used(pool) < Capacity /\ ordinary[pool] < 1
    /\ ordinary' = [ordinary EXCEPT ![pool] = @ + 1]
    /\ UNCHANGED <<phase, charged, holders, windows, borrowed, fullInstall>>

Seal(move) ==
    /\ phase[move] = "open"
    /\ Full(move)
       \/ (Variant = "partial_vector" /\ \E version \in Plan(move) : Owns(move, version))
       \/ (Variant = "foreign_vector" /\ \A pool \in Pools :
              \E version \in charged : holders[version] # 0 /\ Pool(version) = pool)
    /\ phase' = [phase EXCEPT ![move] = "sealed"]
    /\ UNCHANGED <<charged, holders, ordinary, windows, borrowed, fullInstall>>

Abort(move) ==
    /\ phase[move] = "open"
    /\ phase' = [phase EXCEPT ![move] = "aborted"]
    /\ UNCHANGED <<charged, holders, ordinary, windows, borrowed, fullInstall>>

DisposeAborted(version) ==
    /\ version \in charged /\ holders[version] \in Moves /\ phase[holders[version]] = "aborted"
    /\ charged' = charged \ {version} /\ holders' = [holders EXCEPT ![version] = 0]
    /\ UNCHANGED <<phase, ordinary, windows, borrowed, fullInstall>>

Install(move, version) ==
    /\ phase[move] = "sealed" /\ Full(move)
    /\ version = Window(move)
       \/ (Variant = "substitute_window" /\ version \in charged /\ Pool(version) = Pool(Window(move)))
       \/ (Variant = "overwrite_recovery" /\ version \in Plan(move) \ {Window(move)})
    /\ Variant # "rebill" \/ Used(Pool(version)) < Capacity
    /\ phase' = [phase EXCEPT ![move] = "installed"]
    /\ windows' = [windows EXCEPT ![move] = version]
    /\ charged' = IF Variant = "forget_old" /\ move = 1 THEN charged \ {1} ELSE charged
    /\ fullInstall' = (fullInstall \/ (move = 1 /\ borrowed /\ Used(Pool(version)) = Capacity))
    /\ UNCHANGED <<holders, ordinary, borrowed>>

FinishBorrow ==
    /\ borrowed
    /\ borrowed' = FALSE
    /\ UNCHANGED <<phase, charged, holders, ordinary, windows, fullInstall>>

DisposeOld ==
    /\ ~borrowed /\ phase[1] = "installed" /\ 1 \in charged
    /\ charged' = charged \ {1}
    /\ UNCHANGED <<phase, holders, ordinary, windows, borrowed, fullInstall>>

Next ==
    \/ FinishBorrow \/ DisposeOld
    \/ \E pool \in Pools : AdmitOrdinary(pool)
    \/ \E move \in Moves : Seal(move) \/ Abort(move)
    \/ \E version \in Extents : DisposeAborted(version)
    \/ \E move \in Moves, version \in Extents : Prepare(move, version) \/ Install(move, version)

Spec == Init /\ [][Next]_vars
Fits == \A pool \in Pools : Used(pool) <= Capacity
SealedHasFullVector == \A move \in Moves : phase[move] = "sealed" => Full(move)
ExactInstalledWindow == \A move \in Moves :
    phase[move] = "installed" => windows[move] = Window(move) /\ Owns(move, windows[move])
OldBorrowKeepsBytes == borrowed => 1 \in charged
RecoveredImageDisjoint == \A move \in Moves : windows[move] \notin Plan(move) \ {Window(move)}
NoInstallAtCapacity == ~fullInstall
=============================================================================
