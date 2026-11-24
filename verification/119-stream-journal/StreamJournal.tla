--------------------------- MODULE StreamJournal ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Scenario, Fault
Streams == {"a", "b"}
Keepers == 1..4
Originals == 1..3
Stream == "a"
Null == "none"
History(epoch, payload) == [epoch |-> epoch, payload |-> payload]
X == <<History(1, "x")>>
Y == <<History(2, "y")>>
XY == X \o Y
Empty == [created |-> FALSE, deleted |-> FALSE, promised |-> 0,
          holder |-> 0, synced |-> 0, history |-> <<>>, commit |-> 0, floor |-> 1,
          stage |-> <<>>, staging |-> FALSE]
Live(k) == k.created /\ ~k.deleted
Prefix(a,b) == Len(a) <= Len(b) /\ a = SubSeq(b,1,Len(a))
Cut(k) == SubSeq(k.history,1,k.commit)
EpochOK(k,e) == k.promised = e /\ k.synced = e
Request(verb,e,h,pos,records,c,complete) ==
    [verb |-> verb, epoch |-> e, holder |-> h, pos |-> pos,
     records |-> records, commit |-> c, complete |-> complete]
Simple(v) == Request(v,0,0,0,<<>>,0,FALSE)
Seal(e,h) == Request("seal",e,h,0,<<>>,0,FALSE)
Sync(e,pos,records,complete) == Request("sync",e,e,pos,records,0,complete)
AppendTo(e,pos,records,c) == Request("append",e,e,pos,records,c,FALSE)
Trim(e,pos) == Request("trim",e,e,pos,<<>>,0,FALSE)
Check(e) == Request("check",e,0,0,<<>>,0,FALSE)
Read(pos,n) == Request("read",0,0,pos,<<>>,n,FALSE)
Max(a,b) == IF a >= b THEN a ELSE b
SyncBase(k) == IF k.staging THEN k.stage ELSE k.history
SyncHistory(k,r) == SubSeq(SyncBase(k),1,r.pos-1) \o r.records
NextPosition(k,r) == r.pos = Len(k.history) + 1
Identical(k,r) ==
    /\ r.pos \in k.floor..Len(k.history)
    /\ r.records = SubSeq(k.history,r.pos,r.pos)
Page(k,r,end) == [floor |-> k.floor, endLsn |-> k.commit,
                  records |-> SubSeq(k.history,r.pos,
                                      IF end < r.pos+r.commit THEN end ELSE r.pos+r.commit-1)]
Refuse(k) == [ok |-> FALSE, image |-> k, value |-> Null]
Reply(k,v) == [ok |-> TRUE, image |-> k, value |-> v]
Stay(k) == Reply(k,Null)

Decide(k,r) ==
    LET e == r.epoch IN
    CASE r.verb = "create" ->
        IF ~k.deleted \/ Fault = "recreate"
        THEN Stay([k EXCEPT !.created = TRUE, !.deleted = FALSE]) ELSE Refuse(k)
      [] ~Live(k) -> Refuse(k)
      [] r.verb = "seal" ->
        IF e > k.promised \/ (e = k.promised /\ (r.holder = k.holder \/ Fault = "seal-tie"))
           \/ Fault = "seal-lower"
        THEN Reply(IF e = k.promised /\ r.holder = k.holder THEN k
                   ELSE [k EXCEPT !.promised = e, !.holder = r.holder, !.staging = FALSE], k)
        ELSE Refuse(k)
      [] r.verb = "sync" ->
        LET h == SyncHistory(k,r) IN
        IF /\ (e = k.promised \/ Fault = "sync-promise")
           /\ r.pos \in 1..(Len(SyncBase(k))+1)
           /\ (Prefix(Cut(k),h) \/ Fault = "sync-truncate")
           /\ (~r.complete \/ e # k.synced \/ k.history = h)
        THEN Stay(IF r.complete \/ Fault = "sync-incomplete"
                  THEN [k EXCEPT !.history = h, !.synced = e, !.staging = FALSE]
                  ELSE [k EXCEPT !.stage = h, !.staging = TRUE])
        ELSE Refuse(k)
      [] r.verb = "append" ->
        IF /\ (k.promised = e \/ Fault = "append-promise")
           /\ (k.synced = e \/ Fault = "append-unsynced")
           /\ (NextPosition(k,r) \/ Identical(k,r)
                \/ Fault = "append-gap" \/ (Fault = "append-conflict" /\ r.pos \in k.floor..Len(k.history)))
           /\ r.commit <= Max(Len(k.history),r.pos)
        THEN Stay([k EXCEPT
                      !.history = IF NextPosition(k,r) \/ Fault = "append-gap"
                                  THEN @ \o r.records
                                  ELSE IF Fault = "append-conflict" THEN r.records
                                       ELSE IF Fault = "append-retry" THEN <<>> ELSE @,
                      !.commit = Max(@,r.commit), !.staging = FALSE])
        ELSE Refuse(k)
      [] r.verb = "trim" ->
        IF (EpochOK(k,e) \/ Fault = "trim-epoch") /\
           (r.pos <= k.commit \/ Fault = "trim-above")
        THEN Stay([k EXCEPT !.floor = Max(@,r.pos+1)]) ELSE Refuse(k)
      [] r.verb = "check" ->
        Reply(IF Fault = "check-mutates" THEN [k EXCEPT !.commit = Len(k.history)] ELSE k,k)
      [] r.verb = "read" ->
        IF r.pos >= k.floor \/ Fault = "read-below"
        THEN Reply(k,Page(k,r,IF Fault = "read-uncommitted" THEN Len(k.history) ELSE k.commit))
        ELSE Refuse(k)
      [] r.verb = "delete" ->
        Stay(IF Fault = "delete-forgets" THEN Empty ELSE [k EXCEPT !.deleted = TRUE])

VARIABLES store, pc, event, writer, wal, head
vars == <<store,pc,event,writer,wal,head>>
Frame(s,k) == [stream |-> s, image |-> k]
NoEvent == [before |-> Empty, request |-> Simple("none"), result |-> Refuse(Empty)]
InitialWriter ==
    [epoch |-> 0, seed |-> <<>>, committed |-> <<>>, acknowledged |-> 0,
     cuts |-> <<0>>, voters |-> Originals, live |-> Originals, learner |-> FALSE,
     lost |-> FALSE, repaired |-> FALSE, zombie |-> FALSE, tried |-> FALSE,
     retried |-> FALSE, rankOK |-> TRUE, sealedEnd |-> 0, sealPrior |-> 0]
Init ==
    /\ store = [k \in Keepers |-> [s \in Streams |-> Empty]]
    /\ pc = 1
    /\ event = NoEvent
    /\ writer = InitialWriter
    /\ wal = [covered |-> <<>>, pending |-> <<>>, replies |-> {}, torn |-> {},
               batched |-> FALSE]
    /\ head = [start |-> 0, opened |-> 0, epoch |-> 0, samples |-> [k \in Keepers |-> Empty],
                answered |-> {}, returned |-> 0, finish |-> 0, mode |-> Null,
                cached |-> [k \in Keepers |-> Empty]]

Observe(k,s,r) ==
    LET before == store[k][s]
        result == Decide(before,r)
    IN /\ store' = [store EXCEPT ![k][s] = result.image]
       /\ event' = [before |-> before, request |-> r, result |-> result]

Do(k,s,r) ==
    /\ Observe(k,s,r)
    /\ pc' = pc + 1
    /\ UNCHANGED <<writer,wal,head>>

Advance ==
    /\ pc' = pc + 1
    /\ UNCHANGED <<store,event,wal,head>>

\* Shared decisions exercised by both the protocol and rule probes.
\* Probes issue legal and illegal messages to one keeper in a fixed order.
RuleRequests ==
    <<Simple("create"), Seal(1,1), AppendTo(1,1,X,0), Seal(1,2),
      Sync(2,1,<<>>,TRUE), Sync(1,1,<<>>,FALSE), Sync(1,1,<<>>,TRUE),
      AppendTo(1,3,X,0), AppendTo(1,1,X,0), Read(1,2), Check(1), Trim(1,1),
      AppendTo(1,1,<<History(1,"z")>>,0), AppendTo(1,1,X,1), Seal(2,2),
      AppendTo(1,2,X,0), Seal(1,1), Sync(2,1,<<>>,TRUE), Sync(2,2,<<>>,TRUE),
      Trim(1,1), Trim(2,1), Read(1,2), Simple("delete"), Simple("create"),
      Read(2,1)>>
Rules ==
    /\ pc \in 1..Len(RuleRequests)
    /\ Do(1,Stream,RuleRequests[pc])

\* Epoch 1 writes at two zones. The third keeper is ready but is missing x.
Startup ==
    <<Simple("create"),Seal(1,1),Sync(1,1,<<>>,TRUE)>>
StartupStep ==
    /\ pc \in 1..9
    /\ \E k \in Originals, i \in 1..3 :
         /\ pc = (i-1)*3+k
         /\ Do(k,Stream,Startup[i])

LastEpoch(k) == IF k.history = <<>> THEN 0 ELSE k.history[Len(k.history)].epoch
RankLE(a,b) == a.synced < b.synced \/ (a.synced = b.synced /\ Len(a.history) <= Len(b.history))
Pick(a,b) ==
    IF IF Fault = "last-entry" THEN LastEpoch(a) <= LastEpoch(b) ELSE RankLE(a,b)
    THEN b ELSE a

RankProbe ==
    CASE pc = 10 -> Do(1,Stream,AppendTo(1,1,X,0))
      [] pc = 11 -> Do(2,Stream,Seal(2,2))
      [] pc = 12 -> Do(3,Stream,Seal(2,2))
      [] pc = 13 -> Do(2,Stream,Sync(2,1,<<>>,TRUE))
      [] pc = 14 -> Do(3,Stream,Sync(2,1,<<>>,TRUE))
      [] pc = 15 -> Do(1,Stream,Seal(3,3))
      [] pc = 16 -> Do(2,Stream,Seal(3,3))
      [] pc = 17 ->
        LET a == store[1][Stream] b == store[2][Stream] best == Pick(a,b)
        IN /\ writer' = [writer EXCEPT !.rankOK = RankLE(a,best) /\ RankLE(b,best)]
           /\ pc' = 18
           /\ UNCHANGED <<store,event,wal,head>>
      [] OTHER -> FALSE

\* Durable accepts choose at the second keeper independently of reply delivery.
RecordChoice(w,h) ==
    [w EXCEPT !.committed = h, !.cuts = Append(@,Len(h))]
FirstAppend ==
    /\ pc \in {10,11}
    /\ LET k == pc-9
           before == store[k][Stream]
           request == AppendTo(1,1,X,IF Fault = "uncommitted-watermark" THEN 1 ELSE 0)
           result == Decide(before,request)
           other == Decide(store[2]["b"],Simple("create")).image
       IN /\ result.ok
          /\ event' = [before |-> before, request |-> request, result |-> result]
          /\ IF pc = 10 THEN
                 /\ store' = [store EXCEPT ![k][Stream] = result.image]
                 /\ writer' = IF Fault = "single-accept"
                               THEN RecordChoice([writer EXCEPT !.epoch = 1],X)
                               ELSE [writer EXCEPT !.epoch = 1]
                 /\ head' = [head EXCEPT !.cached = [i \in Keepers |-> store[i][Stream]]]
                 /\ UNCHANGED wal
             ELSE
                 /\ store' = [store EXCEPT ![2][Stream] = result.image, ![2]["b"] = other]
                 /\ writer' = RecordChoice([writer EXCEPT !.lost = TRUE],X)
                 /\ wal' = [wal EXCEPT !.covered = <<Frame(Stream,result.image),Frame("b",other)>>,
                               !.replies = {Frame(Stream,result.image),Frame("b",other)},
                               !.batched = TRUE]
                 /\ UNCHANGED head
    /\ pc' = pc+1

Retry ==
    /\ pc = 12
    /\ wal.pending = <<>>
    /\ Observe(2,Stream,AppendTo(1,1,X,1))
    /\ writer' = [writer EXCEPT !.acknowledged = 1, !.retried = TRUE]
    /\ pc' = 13
    /\ UNCHANGED <<wal,head>>

LoseAZ ==
    /\ pc = 13
    /\ writer' = [writer EXCEPT !.live = {2,3}, !.voters = {2,3}]
    /\ pc' = 14
    /\ IF Fault = "empty-rejoin"
       THEN store' = [store EXCEPT ![2][Stream] = Decide(Empty,Simple("create")).image]
       ELSE UNCHANGED store
    /\ UNCHANGED <<event,wal,head>>

BeginReplacement ==
    /\ pc = 14
    /\ Observe(4,Stream,Simple("create"))
    /\ writer' = [writer EXCEPT !.learner = TRUE, !.live = {2,3,4},
                    !.voters = IF Fault = "learner-votes" THEN {2,3,4} ELSE @]
    /\ pc' = 15
    /\ UNCHANGED <<wal,head>>

Elect ==
    CASE pc = 15 -> Do(2,Stream,Seal(2,2))
      [] pc = 16 -> Do(3,Stream,Seal(2,2))
      [] pc = 17 ->
         LET a == store[2][Stream] b == store[3][Stream] winner == Pick(a,b)
         IN /\ writer' = [writer EXCEPT !.seed = winner.history,
                   !.rankOK = RankLE(a,winner) /\ RankLE(b,winner)]
            /\ pc' = 18
            /\ UNCHANGED <<store,event,wal,head>>
      [] pc = 18 -> Do(2,Stream,Sync(2,1,writer.seed,TRUE))
      [] pc = 19 ->
         /\ Observe(3,Stream,Sync(2,1,IF Fault = "skip-repair" THEN <<>> ELSE writer.seed,TRUE))
         /\ writer' = [writer EXCEPT !.epoch = 2, !.sealedEnd = IF Fault = "seal-short" THEN 0 ELSE Len(writer.seed),
                         !.sealPrior = writer.acknowledged, !.repaired = TRUE]
         /\ pc' = 20
         /\ UNCHANGED <<wal,head>>
      [] OTHER -> FALSE

wasAccepted(k,r) == Decide(store[k][Stream],r).ok

Zombie ==
    /\ pc \in 17..28
    /\ ~writer.tried
    /\ \E k \in {2,3} :
         LET r == AppendTo(1,2,<<History(1,"z")>>,1)
         IN /\ Observe(k,Stream,r)
            /\ writer' = [writer EXCEPT !.tried = TRUE, !.zombie = wasAccepted(k,r)]
    /\ UNCHANGED <<pc,wal,head>>

Replacement ==
    CASE pc = 20 -> Do(4,Stream,Seal(2,2))
      [] pc = 21 -> Do(4,Stream,Sync(2,1,writer.seed,TRUE))
      [] pc = 22 ->
         /\ writer' = [writer EXCEPT !.voters = {2,3,4}, !.learner = FALSE]
         /\ pc' = 23
         /\ UNCHANGED <<store,event,wal,head>>
      [] OTHER -> FALSE

SecondAppend ==
    CASE pc = 23 ->
       \E k \in writer.voters :
          /\ Observe(k,Stream,AppendTo(2,2,Y,1))
          /\ pc' = 24
          /\ UNCHANGED <<writer,wal,head>>
      [] pc = 24 ->
       \E k \in writer.voters :
          /\ store[k][Stream].history = X
          /\ Observe(k,Stream,AppendTo(2,2,Y,1))
          /\ writer' = RecordChoice([writer EXCEPT !.acknowledged = 2],XY)
          /\ pc' = 25
          /\ UNCHANGED <<wal,head>>
      [] pc \in 25..27 -> Do(pc-23,Stream,AppendTo(2,2,Y,2))
      [] OTHER -> FALSE

StartHead ==
    /\ Scenario = "protocol"
    /\ pc \in 12..28
    /\ head.start = 0
    /\ \E mode \in {"writer","non-writer"} :
        head' = [head EXCEPT !.start = Len(writer.cuts), !.mode = mode]
    /\ UNCHANGED <<store,pc,event,writer,wal>>

OpenRound ==
    /\ head.start > 0
    /\ head.opened = 0
    /\ IF Fault = "stale-head" /\ writer.epoch = 1
       THEN head' = [head EXCEPT !.opened = 1, !.epoch = 1,
                                !.answered = {1,2}, !.samples = head.cached]
       ELSE head' = [head EXCEPT !.opened = Len(writer.cuts), !.epoch = writer.epoch]
    /\ UNCHANGED <<store,pc,event,writer,wal>>

Sample ==
    /\ head.opened > 0
    /\ head.finish = 0
    /\ \E k \in (writer.live \cap writer.voters) \ head.answered :
        LET checked == Decide(store[k][Stream], Check(head.epoch))
            image == checked.value
        IN /\ checked.ok
           /\ EpochOK(image,head.epoch)
           /\ head' = [head EXCEPT !.answered = @ \cup {k},
                          !.samples[k] = image]
    /\ UNCHANGED <<store,pc,event,writer,wal>>

FinishHead ==
    /\ head.finish = 0
    /\ Cardinality(head.answered \cap writer.voters) >= 2
    /\ \A k \in head.answered : EpochOK(head.samples[k],head.epoch)
    /\ LET end == CHOOSE n \in {Len(head.samples[k].history) : k \in head.answered} :
                    \A k \in head.answered : Len(head.samples[k].history) <= n
           known == writer.acknowledged
           result == IF head.mode = "writer" THEN known ELSE end
       IN /\ ((head.mode = "writer" /\ head.epoch = writer.epoch /\
                (known >= end \/ Fault = "writer-known-only")) \/
                (head.mode = "non-writer" /\ Cardinality({k \in head.answered \cap writer.voters : head.samples[k].commit >= end}) >= 2))
          /\ head' = [head EXCEPT !.returned = result, !.finish = Len(writer.cuts)]
    /\ UNCHANGED <<store,pc,event,writer,wal>>

\* Study 117's covering frontier, specialized to one keeper with two streams.
\* Queued frames contain already-decided images. One barrier covers both.
WalWrite(k,s,r) ==
    /\ ~\E i \in 1..Len(wal.pending) : wal.pending[i].stream = s
    /\ LET result == Decide(store[k][s],r) IN
        /\ result.ok
        /\ wal' = [wal EXCEPT !.pending = Append(@,Frame(s,result.image))]
    /\ UNCHANGED <<store,pc,event,writer,head>>
WalWriteNext ==
    /\ wal.torn = {}
    /\ \E s \in Streams :
       IF ~store[1][s].created THEN WalWrite(1,s,Simple("create"))
       ELSE IF store[1][s].promised = 0 THEN WalWrite(1,s,Seal(1,1))
       ELSE FALSE
WalFlush ==
    /\ Len(wal.pending) > 0
    /\ Len(wal.covered) <= 2
    /\ wal' = [wal EXCEPT !.covered = @ \o wal.pending, !.pending = <<>>,
                  !.batched = @ \/ Len(wal.pending) = 2]
    /\ store' = [store EXCEPT ![1] = [s \in Streams |->
                  IF \E i \in 1..Len(wal.pending) : wal.pending[i].stream = s
                  THEN wal.pending[CHOOSE i \in 1..Len(wal.pending) : wal.pending[i].stream = s].image
                  ELSE @[s]]]
    /\ UNCHANGED <<pc,event,writer,head>>
WalReply ==
    /\ \E row \in {wal.covered[i] : i \in 1..Len(wal.covered)} \cup
          (IF Fault = "early-wal-reply" THEN {wal.pending[i] : i \in 1..Len(wal.pending)} ELSE {}) :
         /\ row \notin wal.replies
         /\ wal' = [wal EXCEPT !.replies = @ \cup {row}]
    /\ UNCHANGED <<store,pc,event,writer,head>>
Recover(s,rows) ==
    LET matches == {i \in 1..Len(rows) : rows[i].stream = s} IN
        IF matches = {} THEN Empty
        ELSE rows[CHOOSE i \in matches : \A j \in matches : j <= i].image
WalTear(k) ==
    /\ Len(wal.pending) > 0
    /\ LET rows == IF Fault = "cross-frontier"
                   THEN SubSeq(wal.covered,1,Len(wal.covered)-1) ELSE wal.covered
       IN /\ wal' = [wal EXCEPT !.covered = rows, !.pending = <<>>,
                      !.torn = {wal.pending[i].stream : i \in 1..Len(wal.pending)}]
          /\ store' = [store EXCEPT ![k] = [s \in Streams |->
                   Recover(IF Fault = "wrong-stream" THEN
                             (IF s = "a" THEN "b" ELSE "a") ELSE s,rows)]]
    /\ UNCHANGED <<pc,event,writer,head>>

ProtocolWal ==
    /\ pc = 12
    /\ wal.torn = {}
    /\ WalWrite(2,Stream,AppendTo(1,1,X,1))
       \/ WalWrite(2,"b",Seal(1,1))
       \/ (Len(wal.pending) = 2 /\ WalTear(2))

Protocol ==
    StartupStep \/ FirstAppend \/ Retry \/ LoseAZ \/ BeginReplacement \/ Elect \/
    Zombie \/ Replacement \/ SecondAppend \/ StartHead \/ OpenRound \/ Sample \/
    FinishHead \/ ProtocolWal

\* A lower writer already has keeper 1's accept. Keeper 3 can still accept
\* that delayed append after the new writer has synced keepers 1 and 2.
Handoff ==
    CASE pc = 10 -> Do(1,Stream,AppendTo(1,1,X,0))
      [] pc = 11 -> Do(1,Stream,Seal(2,2))
      [] pc = 12 -> Do(2,Stream,Seal(2,2))
      [] pc = 13 ->
         /\ writer' = [writer EXCEPT !.seed = Pick(store[1][Stream],store[2][Stream]).history]
         /\ Advance
      [] pc = 14 -> Do(1,Stream,Sync(2,1,writer.seed,TRUE))
      [] pc = 15 ->
         /\ Observe(2,Stream,Sync(2,1,writer.seed,TRUE))
         /\ LET sealed == [writer EXCEPT !.epoch = 2]
             IN writer' = IF Fault = "seal-observed-only" THEN sealed
                          ELSE RecordChoice([sealed EXCEPT !.sealedEnd = Len(writer.seed)],writer.seed)
         /\ pc' = pc+1
         /\ UNCHANGED <<wal,head>>
      [] pc = 16 ->
         /\ Observe(3,Stream,AppendTo(1,1,X,0))
         /\ LET late == [writer EXCEPT !.tried = TRUE] IN
             writer' = IF writer.committed = <<>> THEN RecordChoice(late,X) ELSE late
         /\ pc' = pc+1
         /\ UNCHANGED <<wal,head>>
      [] OTHER -> FALSE

ContractRead(left,right,pos) ==
    LET a == store[left][Stream]
        b == store[right][Stream]
        floor == Max(a.floor,b.floor)
        source == IF a.commit >= b.commit THEN a ELSE b
        page == [Page(source,Read(pos,1),source.commit) EXCEPT !.floor = floor]
    IN /\ event' = [before |-> b, request |-> Request("contract-read",0,0,pos,<<>>,1,FALSE),
                    result |-> [ok |-> pos >= floor, image |-> b, value |-> page]]
       /\ pc' = pc+1
       /\ UNCHANGED <<store,writer,wal,head>>

TrimRead ==
    CASE pc \in 10..12 -> Do(pc-9,Stream,AppendTo(1,1,X,0))
      [] pc \in 13..15 -> Do(pc-12,Stream,AppendTo(1,1,X,1))
      [] pc \in 16..17 -> Do(pc-15,Stream,Trim(1,1))
      [] pc = 18 ->
           IF Fault = "single-read-floor" THEN Do(3,Stream,Read(1,1))
           ELSE \E left,right \in Originals, pos \in 1..2 :
                  left < right /\ ContractRead(left,right,pos)
      [] OTHER -> FALSE

Next ==
    CASE Scenario = "rules" -> Rules
      [] Scenario = "rank" -> StartupStep \/ RankProbe
      [] Scenario = "protocol" -> Protocol
      [] Scenario = "handoff" -> StartupStep \/ Handoff
      [] Scenario = "retention" -> StartupStep \/ TrimRead
      [] Scenario = "wal" -> WalWriteNext \/ WalFlush \/ WalReply \/ WalTear(1)
Spec == Init /\ [][Next]_vars

CheckRule(verb) == event.request.verb = verb /\ event.result.ok
CreateGuard == CheckRule("create") => ~event.before.deleted
SealOrder == CheckRule("seal") => event.before.promised <= event.request.epoch
SealHolder == (CheckRule("seal") /\ event.before.promised = event.request.epoch)
                => event.before.holder = event.request.holder
SyncPromise == CheckRule("sync") => event.before.promised = event.request.epoch
SyncRetainsCommit == CheckRule("sync") => Prefix(Cut(event.before),event.result.image.history)
SyncComplete == (CheckRule("sync") /\ ~event.request.complete)
                 => /\ event.result.image.synced = event.before.synced
                    /\ event.result.image.history = event.before.history
AppendPromise == CheckRule("append") => event.before.promised = event.request.epoch
AppendSynced == CheckRule("append") => event.before.synced = event.request.epoch
AppendCondition == CheckRule("append") =>
    NextPosition(event.before,event.request) \/ Identical(event.before,event.request)
AppendRetry == (CheckRule("append") /\ Identical(event.before,event.request)) =>
    event.before.history = event.result.image.history
TrimEpoch == CheckRule("trim") => EpochOK(event.before,event.request.epoch)
TrimCommit == CheckRule("trim") => event.request.pos <= event.before.commit
CheckPure == CheckRule("check") => event.result.image = event.before
ReadFloor == CheckRule("read") => event.before.floor <= event.request.pos
ReadExact == CheckRule("read") =>
    Page(event.before,event.request,event.before.commit) = event.result.value
DeleteTerminal == CheckRule("delete") => event.result.image.deleted
WinnerRank == writer.rankOK
LearnerExcluded == writer.learner => 4 \notin writer.voters
KeeperBounds == \A k \in Keepers, s \in Streams :
    LET st == store[k][s] IN st.floor \in 1..(st.commit+1) /\ st.commit <= Len(st.history)
CommittedPrefix == Scenario = "protocol" =>
    /\ writer.committed \in {<<>>,X,XY}
    /\ \A k \in writer.live : Prefix(Cut(store[k][Stream]),writer.committed)
    /\ writer.acknowledged <= Len(writer.committed)
QuorumCommit == (Scenario = "protocol" /\ (pc < 14 \/ writer.repaired)) =>
    Cardinality({k \in writer.voters : Prefix(writer.committed,store[k][Stream].history)}) >= 2
ServedSeal == writer.epoch = 2 =>
    /\ writer.sealPrior <= writer.sealedEnd
    /\ \A k \in {2,3} : store[k][Stream].promised >= 2
    /\ ~writer.zombie
HeadLinearizable == head.finish # 0 =>
    /\ head.opened >= head.start
    /\ \E i \in head.start..head.finish : writer.cuts[i] = head.returned
ReplyDurable == wal.replies \subseteq {wal.covered[i] : i \in 1..Len(wal.covered)}
ExactDemux ==
    /\ Scenario = "wal" => \A s \in Streams : store[1][s] = Recover(s,wal.covered)
    /\ (Scenario = "protocol" /\ pc = 12) =>
        \A s \in Streams : store[2][s] = Recover(s,wal.covered)

RecoverableAfterLoss == (Scenario = "protocol" /\ writer.live # Originals) =>
    \E k \in writer.voters : Prefix(writer.committed,store[k][Stream].history)
BothSurvivorsAfterLoss == (Scenario = "protocol" /\ pc >= 14) =>
    \A k \in {2,3} : Prefix(X,store[k][Stream].history)
BothSurvivorsAfterRepair == writer.repaired =>
    \A k \in {2,3} : Prefix(X,store[k][Stream].history)
DelayedAppendAlreadyCommitted == (Scenario = "handoff" /\ writer.tried) =>
    Len(writer.committed) <= writer.sealedEnd
QuorumTrimReadFloor == (Scenario = "retention" /\ pc = 19) =>
    /\ event.result.value.floor >= 2
    /\ event.result.ok = (event.request.pos >= event.result.value.floor)
NoTrimReadWitness == ~(Scenario = "retention" /\ pc = 19 /\ event.before.floor = 1
    /\ event.request.pos = 1 /\ ~event.result.ok /\ event.result.value.floor = 2)
NoDelayedAppendWitness == ~(writer.tried /\ writer.epoch = 2 /\ writer.committed = X
    /\ store[3][Stream].promised = 1 /\ event.result.ok)
NoProtocolWitness == ~(writer.epoch = 2 /\ writer.lost /\ writer.retried /\ writer.tried
    /\ wal.torn = Streams /\ writer.repaired /\ 4 \in writer.voters /\ writer.committed = XY /\ head.returned = 2)
NoNonWriterWitness == ~(head.mode = "non-writer" /\ head.returned = 2)
NoWalWitness == ~(wal.batched /\ wal.torn = Streams /\ Cardinality(wal.replies) = 2)
=============================================================================
