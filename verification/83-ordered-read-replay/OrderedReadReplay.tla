--------------------------- MODULE OrderedReadReplay ---------------------------
EXTENDS Naturals, Sequences

CONSTANTS Variant, Coverage, Custody
VARIABLE state

Cut == 6
Book(row, hold, issued) == [row |-> row, hold |-> hold, issued |-> issued]
Empty == Book(0, 0, 0)
First == Book(1, 1, 1)
Second == Book(2, 2, 2)

Frame(pos, action, serial, proof) ==
    [position |-> pos, action |-> action, serial |-> serial, proof |-> proof]
InitialRead == Frame(1, "admit", 1, TRUE)
Chosen == <<InitialRead, Frame(2, "close", 1, TRUE), Frame(3, "admit", 2, TRUE),
           Frame(4, "close", 1, TRUE)>>
Rival == <<InitialRead, Chosen[2], Frame(3, "admit", 2, FALSE), Chosen[4]>>
Staged == Append(Chosen, Frame(5, "close", 2, TRUE))
Short == SubSeq(Chosen, 1, 3)
Project(frame) == <<frame.position, frame.action>>

Apply(book, frame) ==
    CASE frame.action = "admit" /\ frame.proof /\ book.row = 0 /\ frame.serial = book.issued + 1 ->
            IF Variant = "omit-hold" THEN Book(frame.serial, 0, frame.serial)
            ELSE Book(frame.serial, frame.serial, frame.serial)
      [] frame.action = "close" /\ frame.proof /\ book.row # 0 /\
             (book.row = frame.serial \/ Variant = "ignore-serial") /\ Variant # "omit-release" ->
            Book(0, 0, book.issued)
      [] OTHER -> book

Init ==
    state = [base |-> 3, position |-> 0, head |-> Cut, book |-> Empty,
             physical |-> <<>>, recovered |-> FALSE, answer |-> 0, online |-> TRUE]

CrashAndSelect(base, physical) ==
    /\ state.base = 3 /\ base \in {0, 1}
    /\ physical \in (IF Coverage THEN {Staged, Rival, Short} ELSE {Rival, Short})
    /\ state' = [state EXCEPT !.base = base, !.position = base,
                 !.book = IF base = 0 THEN Empty ELSE First,
                 !.physical = physical, !.online = FALSE]

RecoverNext ==
    LET next == state.position + 1 IN
    /\ state.base # 3 /\ next <= Len(Chosen) /\ next <= Len(state.physical)
    /\ IF Variant = "projection-only" THEN Project(state.physical[next]) = Project(Chosen[next])
       ELSE state.physical[next] = Chosen[next]
    /\ Variant # "recheck-live" \/ state.online
    /\ state' = [state EXCEPT !.position = next, !.book = Apply(state.book, state.physical[next])]

TrustedPrefix ==
    state.base # 3 /\ Len(state.physical) >= Len(Chosen) /\ SubSeq(state.physical, 1, Len(Chosen)) = Chosen

Finish ==
    /\ ~state.recovered /\ state.position = Len(Chosen)
    /\ state' = [state EXCEPT !.recovered = TRUE]

Answer ==
    /\ state.recovered /\ state.answer = 0 /\ state.book.row # 0
    /\ Custody \/ Variant = "skip-current"
    /\ state' = [state EXCEPT !.answer = state.book.row]

Next == (\E base \in {0, 1}, copies \in {Staged, Rival, Short}: CrashAndSelect(base, copies)) \/
        RecoverNext \/ Finish \/ Answer
Spec == Init /\ [][Next]_state
Fair == Spec /\ WF_state(RecoverNext) /\ WF_state(Finish) /\ WF_state(Answer)

FullFrame == state.recovered => TrustedPrefix
Paired == state.book.row = state.book.hold
NoResurrection == state.answer # 1
LatestSurvives == state.recovered /\ TrustedPrefix => state.book = Second
CurrentCoverage == state.answer # 0 => Custody
ServesOffline == TrustedPrefix ~> (state.answer = 2)
================================================================================
