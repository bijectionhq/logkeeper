------------------------- MODULE OrderedApplication -------------------------
EXTENDS Naturals, Sequences

CONSTANTS Variant, MaxCommands
VARIABLE s

Nonces == 1..2

Command(kind, writer, number) ==
    [kind |-> kind, writer |-> writer, number |-> number, submittedAuthorized |-> FALSE]

Commands ==
    {Command("append", writer, lsn) : writer \in 1..2, lsn \in 0..1}
    \cup {Command("retire", writer, 0) : writer \in 1..2}
    \cup {Command("read", writer, nonce) : writer \in 1..2, nonce \in Nonces}
    \cup {Command("fence", 1, 2)}

InitialStream == [writer |-> 1, history |-> <<>>]

ApplyCommand(stream, command, variant) ==
    LET cut == Len(stream.history)
        authorized ==
            IF variant = "check_on_submit" /\ command.kind = "append"
            THEN command.submittedAuthorized
            ELSE command.writer = stream.writer
        admitted ==
            CASE command.kind = "append" ->
                    authorized /\ (variant = "ignore_lsn" \/ command.number = cut)
              [] command.kind \in {"fence", "retire"} -> authorized
              [] command.kind = "read" -> authorized
        next ==
            IF ~admitted THEN stream
            ELSE CASE command.kind = "append" -> [stream EXCEPT !.history = Append(@, command.writer)]
                   [] command.kind = "fence" -> [stream EXCEPT !.writer = command.number]
                   [] command.kind = "retire" -> [stream EXCEPT !.writer = 0]
                   [] command.kind = "read" -> stream
    IN [stream |-> next, outcome |-> [ok |-> admitted, cut |-> Len(next.history)]]

RECURSIVE Replay(_)
Replay(commands) ==
    IF Len(commands) = 0 THEN InitialStream
    ELSE ApplyCommand(Replay(SubSeq(commands, 1, Len(commands) - 1)),
                      commands[Len(commands)], "ordered").stream

At(index) == Replay(SubSeq(s.proposals, 1, index))

Expected(index) == ApplyCommand(At(index - 1), s.proposals[index], "ordered").outcome

Init ==
    s = [proposals |-> <<>>, chosen |-> 0, decisions |-> <<>>, stream |-> InitialStream,
         invoked |-> [nonce \in Nonces |-> [started |-> FALSE, at |-> 0, floor |-> 0,
                                               afterAppendReply |-> FALSE]],
         appendReply |-> 0, appendRepliedAfterRetire |-> FALSE,
         readReply |-> [nonce |-> 0, at |-> 0, cut |-> 0, headAtReply |-> 0]]

Invoke(nonce) ==
    /\ ~s.invoked[nonce].started
    /\ s' = [s EXCEPT !.invoked[nonce] = [started |-> TRUE, at |-> s.chosen,
                                             floor |-> Len(At(s.chosen).history),
                                             afterAppendReply |-> s.appendReply > 0]]

Submit(command) ==
    /\ Len(s.proposals) < MaxCommands
    /\ IF command.kind = "read"
       THEN s.invoked[command.number].started /\
            \A previous \in 1..Len(s.proposals) :
                s.proposals[previous].kind # "read" \/ s.proposals[previous].number # command.number
       ELSE TRUE
    /\ LET proposed ==
              IF Variant = "check_on_submit" /\ command.kind = "append"
              THEN [command EXCEPT !.submittedAuthorized = command.writer = s.stream.writer]
              ELSE command
       IN s' = [s EXCEPT !.proposals = Append(@, proposed)]

Choose ==
    /\ s.chosen < Len(s.proposals)
    /\ s' = [s EXCEPT !.chosen = @ + 1]

Apply ==
    /\ Len(s.decisions) < s.chosen
    /\ LET result == ApplyCommand(s.stream, s.proposals[Len(s.decisions) + 1], Variant)
       IN s' = [s EXCEPT !.stream = result.stream, !.decisions = Append(@, result.outcome)]

ReplyAppend(index) ==
    /\ s.appendReply = 0
    /\ s.proposals[index].kind = "append"
    /\ IF Variant = "reply_on_choice" THEN index <= s.chosen
       ELSE index <= Len(s.decisions) /\ s.decisions[index].ok
    /\ s' = [s EXCEPT !.appendReply = index, !.appendRepliedAfterRetire = s.stream.writer = 0]

ReplyRead(nonce, index) ==
    /\ s.readReply.nonce = 0 /\ s.invoked[nonce].started
    /\ s.proposals[index].kind = "read" /\ s.decisions[index].ok
    /\ s.proposals[index].number = nonce \/ Variant = "replay_old_marker"
    /\ s' = [s EXCEPT !.readReply = [nonce |-> nonce, at |-> index,
                                         cut |-> s.decisions[index].cut,
                                         headAtReply |-> Len(s.stream.history)]]

ReplyFromLaggingReplica(nonce) ==
    /\ Variant = "read_lagging_replica"
    /\ s.readReply.nonce = 0 /\ s.invoked[nonce].afterAppendReply
    /\ s' = [s EXCEPT !.readReply = [nonce |-> nonce, at |-> 0, cut |-> 0, headAtReply |-> 0]]

Next ==
    \/ \E nonce \in Nonces : Invoke(nonce) \/ ReplyFromLaggingReplica(nonce)
    \/ \E command \in Commands : Submit(command)
    \/ Choose \/ Apply
    \/ \E index \in 1..s.chosen : ReplyAppend(index)
    \/ \E nonce \in Nonces, index \in 1..Len(s.decisions) : ReplyRead(nonce, index)

Spec == Init /\ [][Next]_s

AppliedMatchesReference ==
    /\ s.stream = At(Len(s.decisions))
    /\ \A index \in 1..Len(s.decisions) : s.decisions[index] = Expected(index)

FencedWriterCannotAppend ==
    \A index \in 1..Len(s.decisions) :
        (s.proposals[index].kind = "append" /\ s.proposals[index].writer = 1 /\
         At(index - 1).writer = 2) => ~s.decisions[index].ok

ReplyNeverConfirmsRefusedCommand ==
    IF s.appendReply = 0 THEN TRUE ELSE Expected(s.appendReply).ok

ReplyHasExactAppliedAppend ==
    IF s.appendReply = 0 THEN TRUE ELSE
      IF s.appendReply > Len(s.decisions) THEN FALSE ELSE
        LET command == s.proposals[s.appendReply]
        IN /\ Expected(s.appendReply).ok
           /\ command.number < Len(s.stream.history)
           /\ s.stream.history[command.number + 1] = command.writer

ReadUsesItsOrderedMarker ==
    IF s.readReply.nonce = 0 THEN TRUE ELSE
      LET marker == s.readReply.at
          invocation == s.invoked[s.readReply.nonce]
      IN IF marker <= invocation.at \/ marker > Len(s.decisions) THEN FALSE ELSE
         /\ s.proposals[marker].number = s.readReply.nonce
         /\ Expected(marker).ok
         /\ s.readReply.cut = Expected(marker).cut

ReadIncludesPreexistingCommits ==
    s.readReply.nonce = 0 \/ s.readReply.cut >= s.invoked[s.readReply.nonce].floor

NeverChoosesThenRefusesStaleAppend ==
    ~(Len(s.decisions) >= 2 /\ s.proposals[1].kind = "fence" /\
      s.proposals[2].kind = "append" /\ s.proposals[2].writer = 1 /\
      s.proposals[2].number = 0 /\ ~s.decisions[2].ok /\ Len(s.stream.history) = 0)

NeverDeliversOriginalReadAfterLaterAppend ==
    ~(s.readReply.nonce = 1 /\ s.readReply.at = 1 /\ s.readReply.cut = 0 /\
      s.readReply.headAtReply = 1)

NeverDeliversOldAppendAfterRetire ==
    ~(s.appendReply = 1 /\ s.appendRepliedAfterRetire /\ Len(s.stream.history) = 1)
=============================================================================
