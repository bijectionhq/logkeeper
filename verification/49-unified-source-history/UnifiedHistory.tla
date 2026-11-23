----------------------------- MODULE UnifiedHistory -----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Limit, Variant
VARIABLE s

Base == [stream |-> "active", row |-> "empty", anchor |-> 0, acknowledged |-> FALSE]
Command(op, proof) == [op |-> op, proof |-> proof]
Accept(value) == <<value, TRUE>>
Refuse(value) == <<value, FALSE>>

Decide(value, command, position, mode, liveProof) ==
    CASE command.op = "plan" ->
        IF value.stream = "active" /\ value.row = "empty" /\ position = 1
        THEN Accept([value EXCEPT !.row = "planned"]) ELSE Refuse(value)
    [] command.op = "seal" ->
        IF value.stream = "active" /\ value.row = "planned" /\ command.proof = 1
        THEN Accept([value EXCEPT !.stream = "sealed", !.anchor = position,
                        !.row = IF mode = "freeze_only" THEN @ ELSE "sealed"])
        ELSE Refuse(value)
    [] command.op = "retire" ->
        IF value.stream \in {"active", "target"}
        THEN Accept([value EXCEPT !.stream = "retired", !.row = IF @ = "planned" THEN "aborted" ELSE @])
        ELSE Refuse(value)
    [] command.op = "install" ->
        IF value.stream = "sealed" /\
           (command.proof = value.anchor \/ mode = "data_lsn_only")
        THEN Accept([value EXCEPT !.stream = "target"]) ELSE Refuse(value)
    [] command.op = "ack" ->
        IF (value.row = "aborted" \/ (value.row = "sealed" /\ value.stream \in {"target", "retired"})) /\
           (CASE mode = "reread_effect" -> liveProof
              [] mode = "enrich_refusal" -> command.proof = 1 \/ liveProof
              [] OTHER -> command.proof = 1)
        THEN Accept([value EXCEPT !.acknowledged = TRUE]) ELSE Refuse(value)
    [] command.op = "compact" ->
        IF value.acknowledged
        THEN Accept([value EXCEPT !.row = "closed", !.acknowledged = FALSE]) ELSE Refuse(value)
    [] OTHER -> Refuse(value)

Init ==
    s = [phase |-> "open", commands |-> <<>>, result |-> Base, outcomes |-> <<>>,
         learned |-> 0, applied |-> Base, seen |-> <<>>, funding |-> FALSE, effect |-> FALSE,
         available |-> TRUE, hidden |-> FALSE, installedOffline |-> FALSE]

Funding ==
    /\ ~s.funding
    /\ s' = [s EXCEPT !.funding = TRUE]

Effect ==
    /\ ~s.effect /\ s.result.row \in {"sealed", "aborted"}
    /\ s' = [s EXCEPT !.effect = TRUE]

Candidates ==
    (IF Len(s.commands) = 0 THEN {Command("plan", 0)} ELSE {}) \cup
    (IF s.result.stream = "active" /\ s.result.row = "planned"
        THEN {Command("seal", IF s.funding THEN 1 ELSE 0)} ELSE {}) \cup
    (IF s.result.stream \in {"active", "target"} THEN {Command("retire", 0)} ELSE {}) \cup
    (IF s.result.stream = "sealed" THEN {Command("install", s.result.anchor), Command("install", 0)} ELSE {}) \cup
    (IF s.result.row \in {"sealed", "aborted"} /\ ~s.result.acknowledged
        THEN {Command("ack", IF s.available /\ s.effect THEN 1 ELSE 0)} ELSE {}) \cup
    (IF s.result.acknowledged THEN {Command("compact", 0)} ELSE {})

Choose ==
    /\ s.phase = "open" /\ Len(s.commands) < Limit
    /\ \E command \in Candidates :
        LET next == Decide(s.result, command, Len(s.commands) + 1, "reference", FALSE)
        IN s' = [s EXCEPT !.commands = Append(@, command), !.result = next[1], !.outcomes = Append(@, next[2])]

ApplyNext(mode, effect) ==
    /\ s.learned < Len(s.commands)
    /\ LET position == s.learned + 1
           next == Decide(s.applied, s.commands[position], position, mode, effect)
       IN s' = [s EXCEPT !.learned = position, !.applied = next[1], !.seen = Append(@, next[2])]

Learn == s.phase = "open" /\ ApplyNext("reference", FALSE)

Close ==
    /\ s.phase = "open"
    /\ s' = [s EXCEPT !.phase = "closed", !.hidden = s.learned < Len(s.commands)]

Disconnect ==
    /\ s.phase = "closed" /\ s.available
    /\ s' = [s EXCEPT !.available = FALSE]

Recover ==
    /\ s.phase = "closed"
    /\ Variant # "remote_required" \/ s.available
    /\ s' = IF Variant = "learner_only"
             THEN [s EXCEPT !.phase = "installed", !.installedOffline = ~s.available]
             ELSE [s EXCEPT !.phase = "replaying", !.applied = Base, !.seen = <<>>, !.learned = 0]

ReplayNext == s.phase = "replaying" /\ ApplyNext(Variant, s.available /\ s.effect)

PublishRecovered ==
    /\ s.phase = "replaying" /\ s.learned = Len(s.commands)
    /\ s' = [s EXCEPT !.phase = "installed", !.installedOffline = ~s.available]

Next == Funding \/ Effect \/ Choose \/ Learn \/ Close \/ Disconnect \/ Recover \/ ReplayNext \/ PublishRecovered
Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(Recover) /\ WF_s(ReplayNext) /\ WF_s(PublishRecovered)
InstalledExact == s.phase = "installed" => s.applied = s.result /\ s.seen = s.outcomes
AuthorityAndBookTogether == s.phase = "installed" /\ s.applied.stream = "sealed" => s.applied.row = "sealed"
Installs == (s.phase = "closed") ~> (s.phase = "installed")
NeverRecoversHiddenRetirementAndCompaction ==
    ~(s.phase = "installed" /\ s.installedOffline /\ s.hidden /\
      s.applied.stream = "retired" /\ s.applied.row = "closed")
NeverPreservesHistoricalRefusal ==
    ~(s.phase = "installed" /\ s.installedOffline /\ s.effect /\ s.applied.row = "aborted" /\
      \E i \in 1..Len(s.commands) : s.commands[i] = Command("ack", 0) /\ ~s.seen[i])
=============================================================================
