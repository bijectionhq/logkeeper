------------------------------- MODULE Commit -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Design, Mutation, MaxLsn, TraceAcceptance
VARIABLE state

Azs == 1..3
Epochs == 1..2
Payloads == {"a", "b"}
Requests == [epoch : Epochs, lsn : 0..(MaxLsn - 1), payload : Payloads]
NoRequest == [epoch |-> 0, lsn |-> 0, payload |-> "a"]
NoPending == [request |-> NoRequest, copies |-> {}, object_present |-> FALSE]
NoBarrier == [committed_end |-> 0, reported_end |-> 0, has_staged_payload |-> FALSE]

Init ==
    state = [
        live |-> Azs,
        epoch |-> 1,
        fence_end |-> 0,
        history |-> <<>>,
        pending |-> NoPending,
        last_receipt |-> NoRequest,
        barrier |-> NoBarrier,
        receipts |-> {},
        reconciled |-> FALSE,
        first_receipt_before_loss |-> FALSE
    ]

NextLsn == Len(state.history)
AuthorityAvailable == Cardinality(state.live) >= 2
HistoryEntries == {state.history[i] : i \in 1..NextLsn}

IsCommitted(request) ==
    IF request.lsn < NextLsn
    THEN state.history[request.lsn + 1].request = request
    ELSE FALSE

Stage(request) ==
    /\ state.pending = NoPending
    /\ request.epoch <= state.epoch
    /\ NextLsn < MaxLsn
    /\ request.lsn <= NextLsn
    /\ state' = [state EXCEPT !.pending =
        [request |-> request, copies |-> {}, object_present |-> FALSE]]

Persist(az) ==
    /\ state.pending # NoPending
    /\ IF Design = "quorum"
       THEN /\ az \in state.live \ state.pending.copies
            /\ state' = [state EXCEPT !.pending.copies = @ \cup {az}]
       ELSE /\ az = 1
            /\ ~state.pending.object_present
            /\ state' = [state EXCEPT !.pending.object_present = TRUE]

PayloadReady ==
    IF Design = "quorum"
    THEN Cardinality(state.pending.copies) >=
        (IF Mutation = "single_vote" THEN 1 ELSE 2)
    ELSE state.pending.object_present \/ Mutation = "publish_before_data"

CanCommit ==
    /\ state.pending # NoPending
    /\ AuthorityAvailable
    /\ PayloadReady
    /\ (state.pending.request.epoch = state.epoch \/ Mutation = "ignore_fence")
    /\ (state.pending.request.lsn = NextLsn \/ Mutation = "ignore_position")

CommitAppend ==
    /\ CanCommit
    /\ state' = [state EXCEPT
        !.history = Append(@, [
            request |-> state.pending.request,
            decision_epoch |-> state.epoch,
            copies |-> state.pending.copies,
            object_present |-> state.pending.object_present,
            after_loss |-> TraceAcceptance /\ state.live # Azs
        ]),
        !.pending = NoPending,
        !.barrier = NoBarrier,
        !.last_receipt = NoRequest]

OpenWriter ==
    /\ AuthorityAvailable
    /\ state.epoch < 2
    /\ state' = [state EXCEPT
        !.epoch = @ + 1,
        !.fence_end = IF Mutation = "fence_omits_tail" /\ NextLsn > 0
                      THEN NextLsn - 1
                      ELSE NextLsn]

ForgetProposal ==
    /\ state.pending # NoPending
    /\ state' = [state EXCEPT !.pending = NoPending]

LoseAz(az) ==
    /\ state.live = Azs
    /\ state' = [state EXCEPT
        !.live = @ \ {az},
        !.first_receipt_before_loss =
            IF TraceAcceptance /\ NextLsn > 0
            THEN state.history[1].request \in state.receipts
            ELSE FALSE,
        !.pending = IF @ = NoPending THEN @ ELSE [@ EXCEPT !.copies = @ \ {az}]]

CanReply(request) ==
    \/ IsCommitted(request)
    \/ /\ Mutation = "reply_before_commit"
       /\ state.pending # NoPending
       /\ state.pending.request = request
       /\ PayloadReady
    \/ /\ Mutation = "retry_by_lsn"
       /\ request.lsn < NextLsn

Reply(request) ==
    /\ CanReply(request)
    /\ state' = [state EXCEPT
        !.last_receipt = request,
        !.receipts = IF TraceAcceptance THEN @ \cup {request} ELSE @,
        !.reconciled = @ \/ (TraceAcceptance /\ request \notin state.receipts /\
                              request.epoch < state.epoch)]

ReadBarrier ==
    /\ AuthorityAvailable
    /\ LET reached_media ==
               IF state.pending = NoPending
               THEN FALSE
               ELSE state.pending.copies # {} \/ state.pending.object_present
           reported_end ==
               IF Mutation = "barrier_by_held" /\ reached_media
               THEN NextLsn + 1
               ELSE NextLsn
       IN state' = [state EXCEPT !.barrier =
            [committed_end |-> NextLsn, reported_end |-> reported_end,
             has_staged_payload |-> (TraceAcceptance /\ reached_media)]]

Next ==
    \/ \E request \in Requests : Stage(request) \/ Reply(request)
    \/ \E az \in Azs : Persist(az) \/ LoseAz(az)
    \/ CommitAppend
    \/ OpenWriter
    \/ ForgetProposal
    \/ ReadBarrier

DenseHistory ==
    \A i \in 1..NextLsn : state.history[i].request.lsn = i - 1

ReceiptMatchesCommit ==
    state.last_receipt = NoRequest \/ IsCommitted(state.last_receipt)

Recoverable ==
    \A entry \in HistoryEntries :
        IF Design = "quorum"
        THEN entry.copies \intersect state.live # {}
        ELSE entry.object_present

Fenced ==
    \A entry \in HistoryEntries : entry.request.epoch = entry.decision_epoch

ExactFenceCut ==
    state.epoch = 1 \/
        /\ state.fence_end <= NextLsn
        /\ \A i \in 1..NextLsn :
            (i <= state.fence_end) <=> (state.history[i].decision_epoch = 1)

ExactBarrier ==
    state.barrier.reported_end = state.barrier.committed_end

NeverOrdinaryAppend ==
    ~(NextLsn = 1 /\ state.history[1].request \in state.receipts /\
      state.barrier.reported_end = 1)

NeverReconciles ==
    ~state.reconciled

NeverResumesAfterLoss ==
    ~(NextLsn >= 2 /\ state.history[1].decision_epoch = 1 /\
      state.history[2].decision_epoch = 2 /\
      state.first_receipt_before_loss /\ state.history[2].after_loss /\
      state.history[2].request \in state.receipts)

NeverRefusesStagedOldWriter ==
    IF state.pending = NoPending
    THEN TRUE
    ELSE ~(PayloadReady /\ state.pending.request.lsn = NextLsn /\
           state.pending.request.epoch < state.epoch /\ ~CanCommit)

NeverReadsWhileStaged ==
    ~(state.barrier.has_staged_payload /\ state.barrier.reported_end = 0)
=============================================================================
