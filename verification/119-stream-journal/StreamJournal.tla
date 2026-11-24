--------------------------- MODULE StreamJournal ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Scenario, Fault
Streams == {"a", "b"}
Keepers == 1..4
Originals == 1..3
OldEnsemble == <<1,2,3>>
NewEnsemble == <<4,2,3>>
Members(ensemble) == {ensemble[i] : i \in 1..Len(ensemble)}
Stream == "a"
Null == "none"
History(epoch, payload) == [epoch |-> epoch, payload |-> payload]
X == <<History(1, "x")>>
Y == <<History(2, "y")>>
XY == X \o Y
Empty == [created |-> FALSE, deleted |-> FALSE, promised |-> 0,
          identity |-> 0, synced |-> 0, history |-> <<>>, head |-> 0, floor |-> 1,
          stage |-> <<>>, staging |-> FALSE, ensemble |-> OldEnsemble, learner |-> FALSE]
Live(k) == k.created /\ ~k.deleted
Prefix(a,b) == Len(a) <= Len(b) /\ a = SubSeq(b,1,Len(a))
Cut(k) == SubSeq(k.history,1,k.head)
EpochOK(k,e) == k.promised = e /\ k.synced = e
\* The identity comes from the authenticated transport envelope.
Request(verb,e,h,pos,records,c,complete) ==
    [verb |-> verb, epoch |-> e, identity |-> h, pos |-> pos,
     records |-> records, head |-> c, max |-> 0, complete |-> complete,
     origin |-> OldEnsemble, to |-> OldEnsemble]
Simple(v) == Request(v,0,0,0,<<>>,0,FALSE)
Seal(e,h) == Request("seal",e,h,0,<<>>,0,FALSE)
SealAt(e,h,ensemble) == [Seal(e,h) EXCEPT !.origin = ensemble]
ReplaceTo(e,origin,to) ==
    [Request("replace",e,e,0,<<>>,0,FALSE) EXCEPT !.origin = origin, !.to = to]
Sync(e,pos,records,complete) == Request("sync",e,e,pos,records,0,complete)
SyncThrough(e,pos,records,head) == [Sync(e,pos,records,TRUE) EXCEPT !.head = head]
AppendTo(e,pos,records,c) == Request("append",e,e,pos,records,c,FALSE)
Trim(e,pos) == Request("trim",e,e,pos,<<>>,0,FALSE)
Check(e) == Request("check",e,0,0,<<>>,0,FALSE)
Read(pos,n) == [Request("read",0,0,pos,<<>>,0,FALSE) EXCEPT !.max = n]
Max(a,b) == IF a >= b THEN a ELSE b
SyncBase(k) == IF k.staging THEN k.stage ELSE k.history
SyncHistory(k,r) == SubSeq(SyncBase(k),1,r.pos-1) \o r.records
NextPosition(k,r) == r.pos = Len(k.history) + 1
Identical(k,r) ==
    /\ r.pos \in k.floor..Len(k.history)
    /\ r.records = SubSeq(k.history,r.pos,r.pos)
Page(k,r,through) == [floor |-> k.floor, head |-> k.head,
                  records |-> SubSeq(k.history,r.pos,
                                      IF through < r.pos+r.max THEN through ELSE r.pos+r.max-1)]
Refuse(k) == [ok |-> FALSE, image |-> k, value |-> Null]
Reply(k,v) == [ok |-> TRUE, image |-> k, value |-> v]
Stay(k) == Reply(k,Null)

RecordBytes(record) == IF record.payload = "oversized" THEN 2 ELSE 1
Capacity(k,r) ==
    IF \E i \in 1..Len(r.records) : RecordBytes(r.records[i]) > 1 THEN "too-large"
    ELSE IF Len(k.history) + 1 - k.floor + Len(r.records) > 1 THEN "full" ELSE Null

Decide(id,k,r) ==
    LET e == r.epoch IN
    CASE r.verb = "create" ->
        IF ~k.deleted \/ Fault = "recreate"
        THEN IF Live(k) THEN Stay(k)
             ELSE Stay([k EXCEPT !.created = TRUE, !.deleted = FALSE,
                                 !.ensemble = r.origin, !.learner = id \notin Members(r.origin)])
        ELSE Refuse(k)
      [] ~Live(k) -> Refuse(k)
      [] r.verb = "seal" ->
        IF r.origin # k.ensemble /\ Fault # "stale-route"
        THEN [Refuse(k) EXCEPT !.value = k.ensemble]
        ELSE IF e > k.promised \/ (e = k.promised /\ (r.identity = k.identity \/ Fault = "seal-tie"))
           \/ Fault = "seal-lower"
        THEN Reply(IF e = k.promised /\ r.identity = k.identity THEN k
                   ELSE [k EXCEPT !.promised = e, !.identity = r.identity, !.staging = FALSE], k)
        ELSE Refuse(k)
      [] r.verb = "sync" ->
        LET h == SyncHistory(k,r) IN
        IF /\ (e = k.promised \/ Fault = "sync-promise")
           /\ r.pos \in 1..(Len(SyncBase(k))+1)
           /\ (Prefix(Cut(k),h) \/ Fault = "sync-truncate")
           /\ (~r.complete \/ e # k.synced \/ k.history = h)
           /\ r.head <= Len(h)
        THEN Stay(IF r.complete \/ Fault = "sync-incomplete"
                  THEN [k EXCEPT !.history = h, !.synced = e, !.staging = FALSE,
                                 !.head = Max(@,r.head)]
                  ELSE [k EXCEPT !.stage = h, !.staging = TRUE])
        ELSE Refuse(k)
      [] r.verb = "append" ->
        IF /\ (k.promised = e \/ Fault = "append-promise")
           /\ (k.synced = e \/ Fault = "append-unsynced")
           /\ (~k.learner \/ Fault = "learner-append")
           /\ (NextPosition(k,r) \/ Identical(k,r)
                \/ Fault = "append-gap" \/ (Fault = "append-conflict" /\ r.pos \in k.floor..Len(k.history)))
           /\ r.head <= Max(Len(k.history),r.pos)
        THEN LET limit == IF Scenario = "capacity" /\ (NextPosition(k,r) \/ Fault = "charge-duplicate")
                          THEN Capacity(k,r) ELSE Null
             IN IF limit # Null THEN [Refuse(k) EXCEPT !.value = limit]
                ELSE Stay([k EXCEPT
                      !.history = IF NextPosition(k,r) \/ Fault = "append-gap"
                                  THEN @ \o r.records
                                  ELSE IF Fault = "append-conflict" THEN r.records
                                       ELSE IF Fault = "append-retry" THEN <<>> ELSE @,
                      !.head = Max(@,r.head), !.staging = FALSE])
        ELSE Refuse(k)
      [] r.verb = "trim" ->
        IF (EpochOK(k,e) \/ Fault = "trim-epoch") /\
           (r.pos <= k.head \/ Fault = "trim-above")
        THEN Stay([k EXCEPT !.floor = Max(@,r.pos+1)]) ELSE Refuse(k)
      [] r.verb = "check" ->
        Reply(IF Fault = "check-mutates" THEN [k EXCEPT !.head = Len(k.history)] ELSE k,k)
      [] r.verb = "read" ->
        IF r.pos >= k.floor \/ Fault = "read-below"
        THEN Reply(k,Page(k,r,IF Fault = "read-uncommitted" THEN Len(k.history) ELSE k.head))
        ELSE Refuse(k)
      [] r.verb = "replace" ->
        IF ~EpochOK(k,e) \/ k.identity # r.identity THEN Refuse(k)
        ELSE IF k.ensemble = r.to THEN Stay(k)
        ELSE IF k.ensemble # r.origin THEN [Refuse(k) EXCEPT !.value = k.ensemble]
        ELSE IF /\ Len(r.to) = 3 /\ Cardinality(Members(r.to)) = 3
                /\ Members(r.to) \subseteq Keepers /\ id \in Members(r.to)
                /\ Cardinality({i \in 1..3 : r.origin[i] # r.to[i]}) = 1
             THEN Stay([k EXCEPT !.ensemble = r.to, !.learner = FALSE])
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
     retried |-> FALSE, rankOK |-> TRUE, sealedEnd |-> 0, sealPrior |-> 0,
     pending |-> <<>>, refused |-> {}, uncertain |-> FALSE, discarded |-> FALSE]
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
        result == Decide(k,before,r)
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
           result == Decide(k,before,request)
           other == Decide(2,store[2]["b"],Simple("create")).image
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
       THEN store' = [store EXCEPT ![2][Stream] = Decide(2,Empty,Simple("create")).image]
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

wasAccepted(k,r) == Decide(k,store[k][Stream],r).ok

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
         /\ LET replace == ReplaceTo(2,OldEnsemble,NewEnsemble) IN
              store' = [k \in Keepers |-> IF k = 1 THEN store[k]
                  ELSE [store[k] EXCEPT ![Stream] = Decide(k,store[k][Stream],replace).image]]
         /\ UNCHANGED <<event,wal,head>>
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
        LET checked == Decide(k,store[k][Stream], Check(head.epoch))
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
                (head.mode = "non-writer" /\ Cardinality({k \in head.answered \cap writer.voters : head.samples[k].head >= end}) >= 2))
          /\ head' = [head EXCEPT !.returned = result, !.finish = Len(writer.cuts)]
    /\ UNCHANGED <<store,pc,event,writer,wal>>

\* Study 117's covering frontier, specialized to one keeper with two streams.
\* Queued frames contain already-decided images. One barrier covers both.
WalWrite(k,s,r) ==
    /\ ~\E i \in 1..Len(wal.pending) : wal.pending[i].stream = s
    /\ LET result == Decide(k,store[k][s],r) IN
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

\* One disk is permanently lost. Both surviving members publish the adopted tail,
\* then install independently. Requests and a retry can observe the split.
Survivors == {2,3}
OnRoute(route) == {k \in writer.live \cap Members(route) :
    LET image == store[k][Stream] IN
      Live(image) /\ ~image.learner /\ (image.ensemble = route \/ Fault = "count-wrong-route")}
Installed == OnRoute(NewEnsemble) \cap Survivors
PreparedCount == Cardinality({k \in writer.live :
    Prefix(X,store[k][Stream].history) /\ store[k][Stream].head >= 1})
Copies(history) == {k \in writer.live : Prefix(history,store[k][Stream].history)}

ReplacementLoss ==
    /\ pc = 13
    /\ pc' = 14
    /\ writer' = [writer EXCEPT !.live = Survivors, !.voters = Survivors]
    /\ store' = [store EXCEPT ![1][Stream] = Empty]
    /\ UNCHANGED <<event,wal,head>>

ReplacementPrepare ==
    CASE pc \in 14..15 -> Do(pc-12,Stream,Seal(2,2))
      [] pc = 16 ->
         LET choice == Pick(store[2][Stream],store[3][Stream]).history IN
         /\ Observe(2,Stream,Sync(2,1,choice,TRUE))
         /\ writer' = [writer EXCEPT !.seed = choice]
         /\ pc' = 17
         /\ UNCHANGED <<head,wal>>
      [] pc = 17 -> Do(3,Stream,Sync(2,1,IF Fault = "skip-repair" THEN <<>> ELSE writer.seed,TRUE))
      [] pc = 18 -> Do(2,Stream,AppendTo(2,2,<<>>,1))
      [] pc = 19 -> Do(3,Stream,AppendTo(2,Len(store[3][Stream].history)+1,<<>>,
                                                     Len(store[3][Stream].history)))
      [] pc = 20 -> Do(4,Stream,Simple("create"))
      [] pc = 21 -> Do(4,Stream,Seal(2,2))
      [] pc = 22 -> Do(4,Stream,SyncThrough(2,1,writer.seed,Len(writer.seed)))
      [] OTHER -> FALSE

InstallSurvivor ==
    /\ pc \in 23..24
    /\ \E k \in Survivors \ Installed :
         Do(k,Stream,ReplaceTo(2,OldEnsemble,NewEnsemble))

SplitProbe ==
    /\ pc = 24
    /\ ~writer.tried
    /\ \E k \in Installed :
         /\ Observe(k,Stream,SealAt(3,3,OldEnsemble))
         /\ writer' = [writer EXCEPT !.tried = TRUE]
    /\ UNCHANGED <<pc,wal,head>>

ResumeInstall ==
    /\ pc = 24
    /\ writer.tried
    /\ ~writer.zombie
    /\ \E k \in Installed :
         /\ Observe(k,Stream,SealAt(2,2,NewEnsemble))
         /\ writer' = [writer EXCEPT !.zombie = TRUE]
    /\ UNCHANGED <<pc,wal,head>>

LearnerProbe ==
    /\ pc \in 23..24
    /\ Observe(4,Stream,AppendTo(2,2,Y,1))
    /\ UNCHANGED <<pc,wal,head,writer>>

DelayedOldAppend ==
    /\ pc = 16
    /\ \E k \in Survivors : Observe(k,Stream,AppendTo(1,2,<<History(1,"z")>>,1))
    /\ UNCHANGED <<pc,wal,head,writer>>

BeforePublicationRead ==
    /\ pc = 31
    /\ Observe(2,Stream,Read(1,2))
    /\ UNCHANGED <<pc,wal,head,writer>>

InstallLearner ==
    /\ pc \in 23..25
    /\ Installed = Survivors \/ Fault = "early-learner-install"
    /\ Observe(4,Stream,ReplaceTo(2,OldEnsemble,NewEnsemble))
    /\ writer' = [writer EXCEPT !.live = Members(NewEnsemble), !.repaired = TRUE]
    /\ pc' = 26
    /\ UNCHANGED <<wal,head>>

ReplacementSecondLoss ==
    /\ pc = 26
    /\ \E k \in writer.live :
         /\ store' = [store EXCEPT ![k][Stream] = Empty]
         /\ writer' = [writer EXCEPT !.live = @ \ {k}]
    /\ pc' = 36
    /\ UNCHANGED <<event,wal,head>>

AfterReplacement ==
    LET suffix == <<History(3,"y")>>
        history == X \o suffix
    IN CASE pc = 26 -> Do(2,Stream,SealAt(3,3,NewEnsemble))
         [] pc = 27 -> Do(4,Stream,SealAt(3,3,NewEnsemble))
         [] pc = 28 -> Do(2,Stream,SyncThrough(3,2,<<>>,1))
         [] pc = 29 -> Do(4,Stream,SyncThrough(3,2,<<>>,1))
         [] pc = 30 -> Do(2,Stream,AppendTo(3,2,suffix,1))
         [] pc = 31 ->
              /\ Observe(4,Stream,AppendTo(3,2,suffix,1))
              /\ writer' = RecordChoice([writer EXCEPT !.epoch = 3], history)
              /\ pc' = 32
              /\ UNCHANGED <<wal,head>>
         [] pc = 32 -> Do(2,Stream,AppendTo(3,3,<<>>,2))
         [] pc = 33 ->
              /\ Observe(4,Stream,AppendTo(3,3,<<>>,2))
              /\ writer' = [writer EXCEPT !.acknowledged = 2]
              /\ pc' = 34
              /\ UNCHANGED <<wal,head>>
         [] pc = 34 -> \E k \in writer.live : Do(k,Stream,Read(1,2))
         [] OTHER -> FALSE

ChangingEnsemble ==
    StartupStep \/ FirstAppend \/ Retry \/ ReplacementLoss \/ ReplacementPrepare \/
    InstallSurvivor \/ SplitProbe \/ ResumeInstall \/ LearnerProbe \/ InstallLearner \/
    DelayedOldAppend \/ ReplacementSecondLoss \/ AfterReplacement \/ BeforePublicationRead

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

TrimRead ==
    CASE pc \in {10,12} -> Do(pc-9,Stream,AppendTo(1,1,X,0))
      [] pc = 11 ->
           /\ Observe(2,Stream,AppendTo(1,1,X,0))
           /\ writer' = RecordChoice(writer,X)
           /\ pc' = pc+1
           /\ UNCHANGED <<wal,head>>
      [] pc \in 13..15 -> Do(pc-12,Stream,AppendTo(1,1,X,1))
      [] pc \in 16..17 -> Do(pc-15,Stream,Trim(1,1))
      [] pc = 18 -> Do(3,Stream,AppendTo(1,2,<<History(1,"y")>>,1))
      [] pc = 19 -> \E source \in Originals, pos \in 1..2 : Do(source,Stream,Read(pos,2))
      [] OTHER -> FALSE

\* One committed record fills the quota. Two pending positions share the same
\* refusal round. A timed-out request can arrive after Trim frees space.
PendingRecords(payload) == <<History(1,payload),History(1,"suffix")>>
DiscardPending ==
    /\ pc \in 19..20
    /\ IF Fault = "discard-minority" THEN Cardinality(writer.refused) >= 2
       ELSE writer.refused = Originals
    /\ ~writer.uncertain \/ Fault = "discard-uncertain"
    /\ writer' = [writer EXCEPT !.pending = <<>>, !.discarded = TRUE]
    /\ pc' = 21
    /\ UNCHANGED <<store,event,wal,head>>

CapacityAppend ==
    CASE pc \in 10..12 -> Do(pc-9,Stream,AppendTo(1,1,X,0))
      [] pc \in 13..15 -> Do(pc-12,Stream,AppendTo(1,1,X,1))
      [] pc = 16 ->
         /\ \E payload \in {"pending","oversized"}, uncertain \in BOOLEAN :
              /\ uncertain => payload = "pending"
              /\ writer' = [writer EXCEPT !.pending = PendingRecords(payload), !.uncertain = uncertain]
              /\ IF uncertain THEN Observe(1,Stream,AppendTo(1,2,<<History(1,payload)>>,1))
                 ELSE UNCHANGED <<store,event>>
         /\ pc' = pc+1
         /\ UNCHANGED <<wal,head>>
      [] pc \in 17..19 ->
         LET k == pc-16
             request == AppendTo(1,2,SubSeq(writer.pending,1,1),1)
             result == Decide(k,store[k][Stream],request)
         IN /\ Observe(k,Stream,request)
            /\ result.value \in {"full","too-large"}
            /\ writer' = [writer EXCEPT !.refused = @ \cup {k}]
            /\ pc' = pc+1
            /\ UNCHANGED <<wal,head>>
      [] pc = 20 /\ writer.uncertain ->
         /\ Advance
         /\ UNCHANGED writer
      [] pc \in 21..23 -> Do(pc-20,Stream,Trim(1,1))
      [] pc = 24 ->
         /\ writer' = IF writer.discarded THEN [writer EXCEPT !.pending = <<History(1,"replacement")>>]
                       ELSE writer
         /\ Advance
      [] pc \in 25..26 -> Do(1,Stream,AppendTo(1,2,SubSeq(writer.pending,1,1),1))
      [] OTHER -> FALSE

Next ==
    CASE Scenario = "rules" -> Rules
      [] Scenario = "rank" -> StartupStep \/ RankProbe
      [] Scenario = "protocol" -> Protocol
      [] Scenario = "replacement" -> ChangingEnsemble
      [] Scenario = "handoff" -> StartupStep \/ Handoff
      [] Scenario = "retention" -> StartupStep \/ TrimRead
      [] Scenario = "capacity" -> StartupStep \/ CapacityAppend \/ DiscardPending
      [] Scenario = "wal" -> WalWriteNext \/ WalFlush \/ WalReply \/ WalTear(1)
Spec == Init /\ [][Next]_vars

CheckRule(verb) == event.request.verb = verb /\ event.result.ok
CreateGuard == CheckRule("create") => ~event.before.deleted
SealOrder == CheckRule("seal") => event.before.promised <= event.request.epoch
SealHolder == (CheckRule("seal") /\ event.before.promised = event.request.epoch)
                => event.before.identity = event.request.identity
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
TrimCommit == CheckRule("trim") => event.request.pos <= event.before.head
CheckPure == CheckRule("check") => event.result.image = event.before
ReadFloor == CheckRule("read") => event.before.floor <= event.request.pos
ReadExact == CheckRule("read") =>
    Page(event.before,event.request,event.before.head) = event.result.value
DeleteTerminal == CheckRule("delete") => event.result.image.deleted
WinnerRank == writer.rankOK
LearnerExcluded == writer.learner => 4 \notin writer.voters
KeeperBounds == \A k \in Keepers, s \in Streams :
    LET st == store[k][s] IN st.floor \in 1..(st.head+1) /\ st.head <= Len(st.history)
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
RetentionReadCommitted == (Scenario = "retention" /\ pc = 20 /\ event.result.ok) =>
    LET page == event.result.value
        pos == event.request.pos
        upper == pos + event.request.max - 1
    IN /\ page.head <= Len(writer.committed)
       /\ page.records = SubSeq(writer.committed,pos,IF upper < page.head THEN upper ELSE page.head)
NoTrimReadWitness == ~(Scenario = "retention" /\ pc = 20
    /\ store[1][Stream].floor = 2 /\ store[2][Stream].floor = 2
    /\ event.before.floor = 1 /\ Len(event.before.history) = 2 /\ event.request.pos = 1
    /\ event.result.ok /\ event.result.value.records = X)
DiscardSafe == writer.discarded => writer.refused = Originals /\ ~writer.uncertain
CapacityDuplicate == (Scenario = "capacity" /\ pc \in {14,15,16,27}) =>
    event.result.ok /\ event.result.image.history = event.before.history
NoCapacityDiscardWitness == ~(Scenario = "capacity" /\ pc = 27 /\ writer.discarded
    /\ event.result.ok /\ event.result.image.history[2].payload = "replacement")
NoCapacityUncertainWitness == ~(Scenario = "capacity" /\ pc = 27 /\ writer.uncertain
    /\ ~writer.discarded /\ event.result.ok /\ event.result.image.history[2].payload = "pending")
NoTooLargeWitness == ~(Scenario = "capacity" /\ pc = 20 /\ writer.refused = Originals
    /\ event.result.value = "too-large")
NoDelayedAppendWitness == ~(writer.tried /\ writer.epoch = 2 /\ writer.committed = X
    /\ store[3][Stream].promised = 1 /\ event.result.ok)
NoProtocolWitness == ~(writer.epoch = 2 /\ writer.lost /\ writer.retried /\ writer.tried
    /\ wal.torn = Streams /\ writer.repaired /\ 4 \in writer.voters /\ writer.committed = XY /\ head.returned = 2)
NoNonWriterWitness == ~(head.mode = "non-writer" /\ head.returned = 2)
NoWalWitness == ~(wal.batched /\ wal.torn = Streams /\ Cardinality(wal.replies) = 2)

StaleRouteRefused ==
    (event.request.verb = "seal" /\ Live(event.before) /\
        event.request.origin # event.before.ensemble) =>
    ~event.result.ok /\ event.result.image = event.before /\ event.result.value = event.before.ensemble
OneEnsembleAuthority ==
    ~(Cardinality(OnRoute(OldEnsemble)) >= 2 /\ Cardinality(OnRoute(NewEnsemble)) >= 2)
LearnerAfterSurvivors == (pc = 26 /\ writer.repaired) => Installed = Survivors
LearnerCannotAppend == CheckRule("append") => ~event.before.learner
PublishedOnSurvivors == pc \in 20..25 => PreparedCount >= 2
ReplacementDurability ==
    writer.acknowledged > 0 =>
    Cardinality(Copies(SubSeq(writer.committed,1,writer.acknowledged))) >=
      (IF pc = 13 \/ pc \in 20..35 THEN 2 ELSE 1)
ReplacementCommittedPrefix == \A k \in writer.live :
    Prefix(Cut(store[k][Stream]),writer.committed)
ReplacementFencesOldAppends == pc = 16 => ~CheckRule("append")
ReplacementReadExact == CheckRule("read") =>
    LET page == event.result.value IN
      page.records = SubSeq(writer.committed,1,page.head)
NoSplitInstallWitness ==
    ~(pc = 24 /\ Cardinality(Installed) = 1 /\ writer.tried /\ writer.zombie /\
        Cardinality(OnRoute(OldEnsemble)) < 2 /\ Cardinality(OnRoute(NewEnsemble)) < 2)
NoReplacementRecoveryWitness ==
    ~(pc = 26 /\ writer.repaired /\ writer.tried /\ writer.zombie /\
        Cardinality(OnRoute(NewEnsemble)) = 3 /\ Cardinality(Copies(X)) = 3)
NoSecondLossWitness == ~(pc = 36 /\ writer.repaired /\ Cardinality(Copies(X)) = 2)
NoNewEnsembleWriteWitness ==
    ~(pc = 35 /\ writer.acknowledged = 2 /\ writer.tried /\ writer.zombie /\
        CheckRule("read") /\ event.result.value.head = 2)
=============================================================================
