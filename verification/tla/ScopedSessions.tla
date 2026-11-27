---------------------------- MODULE ScopedSessions ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Original, Successor, Owner, OtherOwner, Session, OtherSession,
          CheckSession, CheckStream, GateReplies, AllowInPlaceRecovery

Streams == {Original, Successor}
Owners == {Owner, OtherOwner}
Sessions == {Session, OtherSession}
InitialHistory == <<"base", "kept">>

Receipt(s, epoch, session, owner, head) ==
    [stream |-> s, epoch |-> epoch, session |-> session, owner |-> owner, head |-> head]
FirstSeal == Receipt(Original, 1, Session, Owner, Len(InitialHistory))

VARIABLES history, floor, writers, receipts, authority, available, recovery, job, receiptsExact

vars == <<history, floor, writers, receipts, authority, available, recovery, job, receiptsExact>>
data == <<history, floor, writers, receipts, receiptsExact>>
env == <<authority, available, recovery>>

Init ==
    /\ history = [s \in Streams |-> IF s = Original THEN InitialHistory ELSE <<>>]
    /\ floor = [s \in Streams |-> 1]
    /\ writers = [s \in Streams |-> IF s = Original THEN FirstSeal ELSE
                         Receipt(s, 0, Session, Owner, 0)]
    /\ receipts = {FirstSeal}
    /\ authority = [s \in Streams |-> [revision |-> 1, granted |-> 1, lapsed |-> FALSE,
                                           ticked |-> FALSE]]
    /\ available = {Original}
    /\ recovery = "none"
    /\ job = [step |-> "idle", target |-> Original, fence |-> FirstSeal, owner |-> Owner,
               kind |-> "append", revision |-> 0, decision |-> "none", good |-> FALSE,
               replyAuthorized |-> FALSE]
    /\ receiptsExact = TRUE

(* One revision change represents normal quorum-preserving reconfiguration
   and replacement of the serving keeper's lease. The writer seal belongs
   to ordered application state and is independent of this lease. *)
Gate(s) ==
    /\ s \in available /\ ~authority[s].lapsed
    /\ authority[s].granted = authority[s].revision
Move(s) ==
    /\ s \in available /\ authority[s].revision = 1
    /\ authority' = [authority EXCEPT ![s].revision = 2]
    /\ UNCHANGED <<data, available, recovery, job>>
Lapse(s) ==
    /\ Gate(s) /\ ~authority[s].ticked
    /\ authority' = [authority EXCEPT ![s].lapsed = TRUE, ![s].ticked = TRUE]
    /\ UNCHANGED <<data, available, recovery, job>>
Renew(s) ==
    /\ s \in available /\ ~Gate(s)
    /\ authority' = [authority EXCEPT ![s].granted = authority[s].revision, ![s].lapsed = FALSE]
    /\ UNCHANGED <<data, available, recovery, job>>

Seal(s) ==
    /\ Gate(s) /\ writers[s].epoch < 2
    /\ \E session \in Sessions, owner \in Owners:
        LET fresh == Receipt(s, writers[s].epoch + 1, session, owner, Len(history[s]))
        IN /\ writers' = [writers EXCEPT ![s] = fresh]
           /\ receipts' = receipts \cup {fresh}
    /\ UNCHANGED <<history, floor, env, job, receiptsExact>>

(* A seal retried with the expected epoch the current seal advanced from
   (State::seal_session, `require_writer`): the same principal and session
   receive the original receipt, with the head captured at the seal even
   after later appends; any other session or principal is refused. Without
   CheckSession, another session of the same principal is handed a receipt
   for the current epoch under its own session ID. *)
RetrySeal(s) ==
    /\ Gate(s) /\ writers[s].epoch > 0
    /\ \E session \in Sessions, owner \in Owners:
        LET w == writers[s]
            returned == Receipt(s, w.epoch, session, owner, w.head)
        IN /\ owner = w.owner /\ (CheckSession => session = w.session)
           /\ receipts' = receipts \cup {returned}
           /\ receiptsExact' = (receiptsExact /\ returned = w)
    /\ UNCHANGED <<history, floor, writers, env, job>>

LoseQuorum ==
    /\ recovery = "none" /\ Original \in available
    /\ available' = available \ {Original} /\ recovery' = "requested"
    /\ UNCHANGED <<data, authority, job>>

(* Immutable histories refuse the same-stream recovery cut. The verified
   application checkpoint is installed only under the fresh stream ID. *)
Recover ==
    /\ recovery = "requested"
    /\ IF AllowInPlaceRecovery
       THEN /\ history' = [history EXCEPT ![Original] = SubSeq(@, 1, 1)]
            /\ available' = available \cup {Original}
            /\ UNCHANGED <<writers, floor>>
       ELSE /\ history' = [history EXCEPT ![Successor] = SubSeq(history[Original], 1, 1)]
            /\ available' = available \cup {Successor}
            /\ UNCHANGED <<writers, floor>>
    /\ recovery' = "done"
    /\ UNCHANGED <<authority, receipts, job, receiptsExact>>

Submit ==
    /\ job.step = "idle"
    /\ \E s \in available, f \in receipts, owner \in Owners,
           kind \in {"append", "trim", "reservation"}:
        /\ Gate(s)
        /\ job' = [job EXCEPT !.step = "queued", !.target = s, !.fence = f, !.owner = owner,
                                !.kind = kind, !.revision = authority[s].revision]
    /\ UNCHANGED <<data, env>>

CorrectFence ==
    LET w == writers[job.target] IN
        /\ job.fence.stream = job.target
        /\ job.fence.epoch = w.epoch
        /\ job.fence.session = w.session
        /\ job.owner = w.owner

AllowsFence ==
    LET w == writers[job.target] IN
        /\ (~CheckStream \/ job.fence.stream = job.target)
        /\ job.fence.epoch = w.epoch
        /\ (~CheckSession \/ job.fence.session = w.session)
        /\ job.owner = w.owner

Decide ==
    /\ job.step = "queued"
    /\ LET s == job.target
           admitted == Gate(s) /\ job.revision = authority[s].revision /\ AllowsFence
       IN /\ job' = [job EXCEPT !.step = "decided", !.good = CorrectFence,
                                  !.decision = IF admitted THEN "accepted" ELSE "refused"]
          /\ history' = IF admitted /\ job.kind = "append"
                       THEN [history EXCEPT ![s] = Append(@, "appended")] ELSE history
          /\ floor' = IF admitted /\ job.kind = "trim"
                     THEN [floor EXCEPT ![s] = Len(history[s]) + 1] ELSE floor
    /\ UNCHANGED <<env, writers, receipts, receiptsExact>>

Reply ==
    /\ job.step = "decided"
    /\ job' = [job EXCEPT !.step = "done", !.replyAuthorized = Gate(job.target),
                          !.decision = IF GateReplies /\ ~Gate(job.target) THEN "refused" ELSE @]
    /\ UNCHANGED <<data, env>>

Next ==
    \/ Seal(Original) \/ Seal(Successor)
    \/ LoseQuorum \/ Recover \/ Submit \/ Decide \/ Reply
    \/ \E s \in Streams: Lapse(s) \/ Renew(s) \/ Move(s) \/ RetrySeal(s)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(Recover) /\ WF_vars(Decide) /\ WF_vars(Reply)
    /\ \A s \in Streams: WF_vars(Renew(s))

ImmutablePrefix ==
    /\ Len(history[Original]) >= Len(InitialHistory)
    /\ SubSeq(history[Original], 1, Len(InitialHistory)) = InitialHistory
ScopedDecision == job.decision = "accepted" => job.good
LeaseGatesReply == job.step = "done" /\ job.decision = "accepted" => job.replyAuthorized
ExactSealReceipt == receiptsExact /\ \A s \in Streams:
    writers[s].epoch > 0 => writers[s] \in receipts /\ writers[s].head <= Len(history[s])

RequestsSettle == (job.step = "queued") ~> (job.step = "done")
RecoveryStartsSuccessor == (recovery = "requested") ~> (Successor \in available)

=============================================================================
