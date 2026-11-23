--------------------------- MODULE HistoricalInstall ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Variant, MaxCommands
VARIABLE s

Seeds == {1, 2}
Revisions == {1, 2}
Packet(kind, seed, revision) == [kind |-> kind, seed |-> seed, revision |-> revision]
Change == Packet("change", 0, 2)
Commands == {Packet(kind, seed, rev) : kind \in {"ready", "activate"}, seed \in Seeds, rev \in Revisions}
    \cup {Packet("discard", seed, 0) : seed \in Seeds} \cup {Change}
Empty == [revision |-> 1, installed |-> 0, ready |-> {}, everReady |-> {}, spent |-> {}]
InitialReplay == [view |-> Empty, answers |-> <<>>]

Evaluate(view, command, checkedRevision, mode) ==
    LET seed == command.seed
        correctScope == command.revision = checkedRevision
        allowedReady == correctScope /\ view.installed = 0 /\ seed \notin view.spent
        hasCustody == IF mode = "reuse_dead_ready" THEN seed \in view.everReady ELSE seed \in view.ready
        allowedInstall == (correctScope \/ mode = "ignore_stage_revision")
           /\ view.installed = 0 /\ hasCustody
    IN CASE command.kind = "change" -> [viewAfter |-> [view EXCEPT !.revision = 2, !.ready = {}], result |-> 0]
         [] command.kind = "ready" ->
            [viewAfter |-> IF allowedReady THEN [view EXCEPT !.ready = @ \cup {seed}, !.everReady = @ \cup {seed}]
                       ELSE view, result |-> 0]
         [] command.kind = "discard" ->
            [viewAfter |-> IF seed = view.installed THEN view
                       ELSE [view EXCEPT !.ready = @ \ {seed}, !.spent = @ \cup {seed}], result |-> 0]
         [] OTHER ->
            [viewAfter |-> IF allowedInstall THEN [view EXCEPT !.installed = seed] ELSE view,
             result |-> IF allowedInstall THEN seed ELSE 0]

RECURSIVE Replay(_)
Replay(history) ==
    IF Len(history) = 0 THEN InitialReplay
    ELSE LET current == Replay(SubSeq(history, 1, Len(history) - 1))
             next == Evaluate(current.view, history[Len(history)], current.view.revision, "reference")
         IN [view |-> next.viewAfter, answers |-> Append(current.answers, next.result)]

Init ==
    s = [chosen |-> <<>>, physicalRevision |-> 1, through |-> 0,
         applied |-> InitialReplay, oldAppliedAfterChange |-> FALSE]

Choose(command) ==
    /\ Len(s.chosen) < MaxCommands
    /\ IF command.kind = "change" THEN s.physicalRevision = 1
       ELSE command.revision <= s.physicalRevision
    /\ s' = [s EXCEPT !.chosen = Append(@, command),
                  !.physicalRevision = IF command.kind = "change" THEN 2 ELSE @]

Apply ==
    /\ s.through < Len(s.chosen)
    /\ LET command == s.chosen[s.through + 1]
           installed == Evaluate(s.applied.view, command,
                       IF Variant = "replay_current_revision" THEN s.physicalRevision ELSE s.applied.view.revision,
                       Variant)
       IN s' = [s EXCEPT !.through = @ + 1,
                !.applied = [view |-> installed.viewAfter, answers |-> Append(s.applied.answers, installed.result)],
                !.oldAppliedAfterChange = @ \/ (s.physicalRevision = 2 /\ command.revision = 1
                                  /\ command.kind = "activate" /\ installed.result # 0)]

Next == (\E command \in Commands : Choose(command)) \/ Apply
Spec == Init /\ [][Next]_s

ReplayAgrees == s.applied = Replay(SubSeq(s.chosen, 1, s.through))
AppliedRepliesAgree == s.applied.answers = Replay(SubSeq(s.chosen, 1, s.through)).answers
NeverAppliesOldChoiceAfterPhysicalChange == ~s.oldAppliedAfterChange
NeverRefusesLaterStalePacket ==
    ~(s.physicalRevision = 2 /\ \E earlier, change, packet \in 1..s.through :
       earlier < change /\ change < packet /\ s.chosen[change] = Change
       /\ s.chosen[earlier].kind = "ready" /\ s.chosen[earlier].seed = s.chosen[packet].seed
       /\ s.chosen[packet].kind = "activate" /\ s.chosen[packet].revision = 1
       /\ s.applied.answers[packet] = 0)

=============================================================================
