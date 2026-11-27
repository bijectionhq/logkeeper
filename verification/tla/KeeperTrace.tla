------------------------------ MODULE KeeperTrace ------------------------------
EXTENDS Integers, Sequences, KeeperSafety

CONSTANTS TraceLength, EventAt(_), Nodes, Streams
VARIABLES position, state

Nil == "00000000-0000-0000-0000-000000000000"
Zero == <<0, 0, 0, 0>>
NoCut == [index |-> 0, term |-> Zero]
NoVote == [term |-> Zero, votedFor |-> Nil, committed |-> FALSE]
EmptyCopy == [registered |-> FALSE, vote |-> NoVote, log |-> <<>>, base |-> NoCut,
              snapshot |-> NoCut, applied |-> NoCut, commit |-> NoCut, parked |-> FALSE]
EmptyKeeper == [epoch |-> 0, incarnation |-> Nil, duration |-> 0, margin |-> 0,
                fences |-> [s \in Streams |-> 0]]
NoRecovery == [epoch |-> 0, loss |-> 0, fenced |-> {}, target |-> {}, wait |-> 0]
NoLease == [granted |-> FALSE, epoch |-> 0]

Max(a, b) == IF a >= b THEN a ELSE b
Min(a, b) == IF a <= b THEN a ELSE b
TermLess(a, b) == \E i \in 1..Len(a) : /\ a[i] < b[i]
                                      /\ \A j \in 1..(i-1) : a[j] = b[j]
CutLeq(a, b) == a.index < b.index \/ a = b
MaxCut(a, b) == IF a.index >= b.index THEN a ELSE b
AsSet(seq) == {seq[i] : i \in 1..Len(seq)}
Keys == Nodes \X Streams

Empty ==
    [copies |-> [k \in Keys |-> EmptyCopy],
     media |-> [n \in Nodes |-> Nil],
     leaders |-> [s \in Streams |-> {}],
     recoveries |-> [s \in Streams |-> {}],
     chosen |-> [s \in Streams |-> {}],
     keepers |-> [n \in Nodes |-> EmptyKeeper],
     leases |-> [n \in Nodes |-> NoLease],
     catalogAt |-> 0,
     recovery |-> [s \in Streams |-> NoRecovery],
     ready |-> [k \in Keys |-> 0],
     activated |-> [s \in Streams |-> 0],
     markers |-> [s \in Streams |-> {}],
     uploads |-> [s \in Streams |-> {}]]

Tip(r) == r.base.index + Len(r.log)
HasEntry(r, i) == i > r.base.index /\ i <= Tip(r)
At(r, i) == r.log[i - r.base.index]
Known(r) == MaxCut(r.commit, MaxCut(r.snapshot, r.base))

Covered(r, c) ==
    \/ c = NoCut
    \/ IF c.index <= r.snapshot.index THEN CutLeq(c, r.snapshot) ELSE FALSE
    \/ IF HasEntry(r, c.index) THEN At(r, c.index).cut = c ELSE c = r.base

RecordVote(st, k, v) ==
    [st EXCEPT !.copies[k].vote = v,
               !.leaders[k[2]] = IF v.committed /\ v.term # Zero
                                 THEN @ \cup {v} ELSE @]

CanVote(st, k, v) ==
    /\ st.copies[k].registered
    /\ RaftVoteLeq(st.copies[k].vote, v, Nil, TermLess)
    /\ v.committed =>
        \A old \in st.leaders[k[2]] : old.term = v.term => old.votedFor = v.votedFor

Splice(r, entries) ==
    LET i == entries[1].cut.index
    IN [r EXCEPT !.log = SubSeq(@, 1, i - r.base.index - 1) \o entries]

Matches(peer, r, entries) ==
    LET new == Splice(r, entries)
    IN \A j \in 1..Len(entries) :
          LET i == entries[j].cut.index
          IN IF HasEntry(peer, i) /\ entries[j].cut = At(peer, i).cut
             THEN \A p \in (Max(peer.base.index, new.base.index) + 1)..i :
                   At(peer, p) = At(new, p)
             ELSE TRUE

CanSplice(st, k, entries) ==
    LET r == st.copies[k]
        first == entries[1].cut.index
    IN /\ r.registered
       /\ first > r.base.index
       /\ first <= Tip(r) + 1
       /\ \A j \in 1..Len(entries) : entries[j].cut.index = first + j - 1
       /\ \A n \in Nodes \ {k[1]} : Matches(st.copies[<<n, k[2]>>], r, entries)

PreservesApplied(r, entries) ==
    LET protected == Max(r.applied.index, r.commit.index)
        first == entries[1].cut.index
    IN \A i \in first..Min(protected, Tip(r)) :
           LET j == i - first + 1
           IN IF j <= Len(entries) THEN At(r, i) = entries[j] ELSE FALSE

RecoveryTerm(old, new) ==
    \* Adding 2^32 increments the second digit, with carry into the first.
    /\ new[1] = old[1] + (old[2] + 1) \div 65536
    /\ new[2] = (old[2] + 1) % 65536
    /\ new[3] = old[3] /\ new[4] = old[4]

RecoverAllowed(st, k, d) ==
    LET r == st.copies[k]
        tipTerm == IF Len(r.log) = 0 THEN r.base.term ELSE r.log[Len(r.log)].cut.term
        lastTerm == IF TermLess(r.vote.term, tipTerm) THEN tipTerm ELSE r.vote.term
    IN /\ st.ready[k] > 0
       /\ CanVote(st, k, d.vote)
       /\ d.vote.committed /\ d.vote.votedFor = k[1]
       /\ RecoveryTerm(lastTerm, d.vote.term)
       /\ CanSplice(st, k, d.entries)
       /\ \A entry \in AsSet(d.entries) : entry.cut.term = d.vote.term
       /\ d.entries[1].cut.index =
            IF d.exact THEN Min(Known(r).index, Tip(r)) + 1 ELSE Tip(r) + 1

ResetForRecovery(r, entries) ==
    LET last == entries[1].cut.index - 1
    IN [Splice(r, entries) EXCEPT
         !.applied = IF @.index <= last THEN @ ELSE Known(r),
         !.commit = IF @.index <= last THEN @ ELSE NoCut]

Purge(r, c) ==
    [r EXCEPT !.base = c, !.log = IF c.index >= Tip(r) THEN <<>>
                                 ELSE SubSeq(@, c.index - r.base.index + 1, Len(@))]

Fenced(d) ==
    LET removed == RemovedVoters(AsSet(d.old), AsSet(d.target))
    IN IF d.writer = Nil THEN removed ELSE AsSet(d.old) \ {d.writer}

MaxLeaseWindow(st, fenced) ==
    LET windows == {0} \cup {st.keepers[n].duration + st.keepers[n].margin : n \in fenced}
    IN CHOOSE w \in windows : \A v \in windows : v <= w

RecoveryAuthority(st, e) ==
    LET d == e.data
        s == e.stream
        old == AsSet(d.old)
        target == AsSet(d.target)
        fenced == Fenced(d)
    IN /\ Cardinality(old) \in {3, 5}
       /\ Cardinality(old) = Cardinality(target)
       /\ (old \cap target) # {} /\ ~Majority(target, old)
       /\ AsSet(d.dead) \subseteq RemovedVoters(old, target)
       /\ d.writer # Nil => d.writer \in (old \cap target)
       /\ d.epoch = d.sourceRevision + 1
       /\ d.epoch > st.recovery[s].epoch
       /\ state' = [st EXCEPT !.catalogAt = d.at,
                    !.recovery[s] = [epoch |-> d.epoch, loss |-> d.loss,
                                     fenced |-> fenced, target |-> target,
                                     wait |-> MaxLeaseWindow(st, fenced)],
                    !.keepers = [n \in Nodes |->
                        LET row == st.keepers[n]
                        IN [row EXCEPT !.epoch = IF n \in AsSet(d.dead) THEN Max(1, @) + 1 ELSE @,
                                       !.fences[s] = IF n \in fenced THEN Max(@, d.epoch) ELSE @]]]

Catalog(st, e) ==
    LET d == e.data
        n == d.keeper
    IN IF d.at <= st.catalogAt THEN state' = st
       ELSE CASE e.kind = "RecoveryTransaction" -> RecoveryAuthority(st, e)
              [] e.kind = "Enroll" ->
                   state' = [st EXCEPT !.catalogAt = d.at, !.keepers[n].epoch =
                         IF st.keepers[n].incarnation = Nil THEN Max(1, @)
                         ELSE IF st.keepers[n].incarnation = d.incarnation THEN @ ELSE @ + 1,
                         !.keepers[n].incarnation = d.incarnation]
              [] e.kind = "Fence" ->
                   state' = [st EXCEPT !.catalogAt = d.at, !.keepers[n].epoch = Max(1, @) + 1]
              [] e.kind = "LeasePolicy" ->
                   state' = [st EXCEPT !.catalogAt = d.at, !.keepers[n].epoch = Max(1, @),
                             !.keepers[n].duration = Max(@, d.duration),
                             !.keepers[n].margin = Max(@, d.margin)]

AdoptLease(st, n, d) ==
    LET row == st.keepers[n]
    IN /\ d.enforced =>
          /\ d.epoch > 0 /\ d.epoch <= row.epoch
          /\ d.asked \in {0, d.epoch}
          /\ d.epoch = row.epoch => d.incarnation = row.incarnation
          /\ d.duration <= row.duration /\ d.margin >= row.margin
          /\ \A f \in AsSet(d.fences) : f.revision <= row.fences[f.stream]
       /\ d.valid = CurrentLease(d.age < d.duration - d.margin, d.epoch, d.epoch, FALSE)
       /\ state' = [st EXCEPT !.leases[n] = [granted |-> TRUE, epoch |-> d.epoch]]

RecoveryReady(st, k, d) ==
    LET rec == st.recovery[k[2]]
        target == AsSet(d.target)
        fenced == AsSet(d.fenced)
    IN /\ k[1] \in AsSet(d.old) \cap target
       /\ d.authority =>
          /\ rec.epoch = d.epoch /\ rec.loss = d.loss
          /\ rec.target = target /\ rec.fenced = fenced
          /\ d.wait >= rec.wait
       /\ d.exact => d.loss = Max(d.knownHead, d.offloaded)
       /\ d.elapsed >= d.wait
       /\ state' = [st EXCEPT !.ready[k] = d.epoch]

Offload(st, s, d) ==
    /\ d.lineage = d.beforeLineage /\ d.afterLineage = d.lineage
    /\ d.afterThrough = Max(d.beforeThrough, Min(d.requested, d.head))
    /\ d.afterThrough <= d.head
    /\ d.floor <= d.localFloor
    /\ d.localFloor <= Max(d.floor, d.afterThrough + 1)
    /\ \A i \in Max(d.beforeThrough + 1, d.floor)..d.afterThrough :
           \E u \in st.uploads[s] : u.lineage = d.lineage /\ u.first <= i /\ i <= u.last

\* Within a recovery era, two applied prefixes cannot disagree at an index.
\* The recovery gap keeps old leaders in their own era. A retained entry
\* below the recovery cut still belongs to its original era.
Era(st, s, c) ==
    LET terms == {Zero} \cup {r.term :
                    r \in {x \in st.recoveries[s] :
                           x.first <= c.index /\ ~TermLess(c.term, x.term)}}
    IN CHOOSE t \in terms : \A u \in terms : ~TermLess(t, u)

Apply(st, k, d) ==
    LET r == st.copies[k]
        entry == d.entry
        c == entry.cut
        era == Era(st, k[2], c)
    IN /\ r.registered /\ ~r.parked /\ Covered(r, c)
       /\ c.index = d.previous.index + 1
       /\ HasEntry(r, c.index) => At(r, c.index) = entry
       /\ \A record \in st.chosen[k[2]] :
               (record.era = era /\ record.entry.cut.index = c.index) => record.entry = entry
       /\ state' = [st EXCEPT !.copies[k].applied = MaxCut(@, c),
                              !.chosen[k[2]] = @ \cup {[era |-> era, entry |-> entry]}]

Replica(st, e) ==
    LET d == e.data
        k == <<e.node, e.stream>>
        r == st.copies[k]
    IN CASE e.kind = "Register" -> state' = [st EXCEPT !.copies[k].registered = TRUE]
         [] e.kind = "ResetCopy" ->
              /\ r.registered
              /\ state' = [st EXCEPT !.copies[k] = [EmptyCopy EXCEPT
                                         !.registered = TRUE, !.vote = r.vote]]
         [] e.kind = "OpenGroup" ->
              /\ r.registered
              /\ state' = [st EXCEPT !.copies[k].parked = FALSE]
         [] e.kind = "Vote" -> CanVote(st, k, d) /\ state' = RecordVote(st, k, d)
         [] e.kind = "Append" ->
              /\ ~r.parked /\ CanSplice(st, k, d.entries)
              /\ PreservesApplied(r, d.entries)
              /\ state' = [st EXCEPT !.copies[k] = Splice(r, d.entries)]
         [] e.kind = "Truncate" ->
              /\ d.from > Max(r.base.index, Max(r.applied.index, r.commit.index))
              /\ state' = [st EXCEPT !.copies[k].log = SubSeq(@, 1, d.from - r.base.index - 1)]
         [] e.kind = "DurableCommit" ->
              /\ Covered(r, d) /\ CutLeq(r.commit, d)
              /\ state' = [st EXCEPT !.copies[k].commit = d]
         [] e.kind = "Apply" -> Apply(st, k, d)
         [] e.kind = "Snapshot" ->
              /\ r.registered /\ CutLeq(r.snapshot, d)
              /\ state' = [st EXCEPT !.copies[k].snapshot = d]
         [] e.kind = "BuildSnapshot" ->
              /\ d = r.snapshot /\ CutLeq(d, r.applied)
              /\ state' = st
         [] e.kind = "InstallSnapshot" ->
              /\ d = r.snapshot
              /\ state' = [st EXCEPT !.copies[k].applied = MaxCut(@, d)]
         [] e.kind = "Purge" ->
              /\ CutLeq(r.base, d) /\ CutLeq(d, r.snapshot)
              /\ state' = [st EXCEPT !.copies[k] = Purge(r, d)]
         [] e.kind = "AcceptPark" ->
              /\ d.follower /\ d.localCut.index = d.lastIndex
              /\ MatchingParkCut(d.localVote, d.leaderVote, d.localCut, d.leaderCut)
              /\ state' = st
         [] e.kind = "Park" ->
              /\ r.registered /\ ~r.parked
              /\ state' = [st EXCEPT !.copies[k].parked = TRUE]
         [] e.kind = "LeaseGate" ->
              /\ d.permitted = CurrentLease(d.valid, d.current, TRUE, d.revision < d.below)
              /\ (d.permitted /\ st.activated[e.stream] = st.recovery[e.stream].epoch
                   /\ e.node \in st.recovery[e.stream].fenced) =>
                     d.revision >= st.activated[e.stream]
              /\ state' = st
         [] e.kind = "RecoveryReady" -> RecoveryReady(st, k, d)
         [] e.kind = "Recover" ->
              /\ RecoverAllowed(st, k, d)
              /\ state' = [RecordVote(st, k, d.vote) EXCEPT
                     !.copies[k] = ResetForRecovery(@, d.entries),
                     !.activated[e.stream] = st.ready[k], !.ready[k] = 0,
                     !.recoveries[e.stream] = @ \cup
                        {[term |-> d.vote.term, first |-> d.entries[1].cut.index]}]
         [] e.kind = "RecoveryMarker" ->
              /\ d.epoch = st.recovery[e.stream].epoch /\ d.loss = st.recovery[e.stream].loss
              /\ d.at = d.fenceHead + 1
              /\ \A marker \in st.markers[e.stream] : marker.epoch = d.epoch => marker = d
              /\ state' = [st EXCEPT !.markers[e.stream] = @ \cup {d}]
         [] e.kind = "Upload" ->
              /\ d.first = Max(d.previous + 1, d.floor)
              /\ d.first <= d.last /\ d.last <= d.head
              /\ d.last - d.first + 1 = Len(d.positions)
              /\ \A i \in 1..Len(d.positions) : d.positions[i] = d.first + i - 1
              /\ state' = [st EXCEPT !.uploads[e.stream] = @ \cup
                             {[lineage |-> d.lineage, first |-> d.first, last |-> d.last]}]
         [] e.kind = "Offload" -> Offload(st, e.stream, d) /\ state' = st
         [] OTHER -> FALSE

Step(e) ==
    LET n == e.node
        d == e.data
    IN CASE e.kind = "Media" ->
              state' = [state EXCEPT !.media[n] = d.incarnation, !.leases[n] = NoLease,
                   !.copies = IF state.media[n] = d.incarnation THEN @ ELSE
                               [k \in Keys |-> IF k[1] = n THEN EmptyCopy ELSE @[k]]]
         [] e.kind \in {"Enroll", "Fence", "LeasePolicy", "RecoveryTransaction"} ->
              Catalog(state, e)
         [] e.kind = "LeaseGrant" -> AdoptLease(state, n, d)
         [] e.kind = "LeaseExpiry" ->
              /\ state.leases[n].granted /\ state.leases[n].epoch = d.epoch
              /\ state' = [state EXCEPT !.leases[n] = NoLease]
         [] OTHER -> Replica(state, e)

Init == position = 0 /\ state = Empty
Next ==
    IF position < TraceLength
    THEN /\ Step(EventAt(position + 1))
         /\ position' = position + 1
    ELSE UNCHANGED <<position, state>>

\* TLC checks deadlocks. The terminal self-loop is the only stuttering step.
\* Every earlier state has a successor exactly when its observed action is legal.
=============================================================================
