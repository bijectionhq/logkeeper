---------------------------- MODULE KernelCuts ----------------------------
EXTENDS Naturals, Integers, Sequences

CONSTANTS Mutation, MaxSteps, MaxTime, Capacity
VARIABLE s

Init ==
  s = [seq |-> <<>>, archived |-> <<>>, floor |-> 0, root |-> 0,
       pending |-> 0, pendingErasure |-> FALSE, oldRoot |-> -1, closed |-> FALSE, erasureFloor |-> 0,
       epoch |-> 1, generation |-> 1, writer |-> TRUE, rotated |-> FALSE,
       exactRotation |-> TRUE, currentAppend |-> TRUE,
       hold |-> FALSE, holdThrough |-> 0, capturedHead |-> 0, enrolled |-> TRUE, leaseEnd |-> 0, leaseSafe |-> TRUE, leaseBasisOpen |-> TRUE,
       disposed |-> FALSE, disposedWithLease |-> FALSE, disposalSafe |-> TRUE, now |-> 0,
       fence |-> 0, settled |-> FALSE, settlementSafe |-> TRUE,
       window |-> 1, spent |-> 0, turn |-> 0,
       original |-> <<>>, reply |-> <<>>, retried |-> FALSE, readReplay |-> FALSE,
       readRetried |-> FALSE]

LogLength == Len(s.seq)
Used == LogLength - s.floor
Physical(name) == \E pos \in (s.floor + 1)..LogLength: s.seq[pos].name = name

AppendEntry ==
  /\ s.writer /\ s.pending = 0 /\ LogLength < 2 /\ s.spent < s.window
  /\ \E grant \in 1..2, name \in 0..2:
      /\ (grant = s.epoch \/ Mutation = "stale-writer")
      /\ (s.fence = 0 \/ name = 2 \/ Mutation = "late-reference")
      /\ LET row == [name |-> name, epoch |-> grant, generation |-> s.generation]
             first == <<s.turn + 1, 1, row>>
         IN s' = [s EXCEPT
             !.seq = IF Mutation = "rewrite-prefix" /\ LogLength = 1
                       THEN <<[s.seq[1] EXCEPT !.name = (s.seq[1].name + 1) % 3], row>>
                       ELSE Append(@, row),
             !.currentAppend = grant = s.epoch,
             !.spent = @ + 1, !.turn = @ + 1,
             !.original = IF LogLength = 0 THEN first ELSE @]

RetryMutation ==
  /\ s.original # <<>> /\ ~s.retried
  /\ s' = [s EXCEPT !.reply = IF Mutation = "new-receipt"
           THEN <<s.turn + 1, s.original[2], s.original[3]>> ELSE s.original,
         !.retried = TRUE, !.turn = @ + 1]

Capture ==
  /\ s.enrolled /\ ~s.hold /\ s.floor = 0 /\ s.root = 0 /\ LogLength > 0
  /\ s' = [s EXCEPT !.hold = TRUE, !.capturedHead = LogLength,
           !.holdThrough = IF Mutation = "stale-cut" THEN 0 ELSE LogLength, !.turn = @ + 1]

RetryRead ==
  /\ s.hold /\ ~s.readRetried
  /\ s' = [s EXCEPT !.readRetried = TRUE, !.readReplay = Mutation = "replay-read",
         !.turn = @ + 1]

Renew ==
  LET end == IF Mutation = "shorten-lease" THEN s.now + 1 ELSE s.now + 2 IN
  /\ s.enrolled /\ s.hold /\ s.leaseEnd < s.now + 2 /\ s.now + 2 <= MaxTime
  /\ (s.erasureFloor = 0 \/ Mutation = "renew-erased")
  /\ s' = [s EXCEPT !.leaseEnd = end, !.leaseSafe = end = s.now + 2 /\ s.leaseEnd <= end,
           !.leaseBasisOpen = s.erasureFloor = 0, !.turn = @ + 1]

Prepare ==
  /\ s.writer /\ s.pending = 0 /\ s.root = 0 /\ LogLength > 0
  /\ \E erasure \in BOOLEAN:
      s' = [s EXCEPT !.pending = LogLength, !.pendingErasure = erasure, !.turn = @ + 1]

Select ==
  /\ s.pending > 0 /\ ~s.pendingErasure
  /\ s' = [s EXCEPT !.root = s.pending, !.oldRoot = s.root, !.pending = 0,
         !.turn = @ + 1]

Rotate ==
  /\ s.writer /\ s.pending > 0 /\ s.pendingErasure
  /\ \E cut \in 0..LogLength:
      /\ ((cut = LogLength /\ cut = s.pending) \/ Mutation = "wrong-rotation")
      /\ s' = [s EXCEPT !.rotated = TRUE, !.root = cut, !.erasureFloor = cut,
             !.oldRoot = s.root, !.closed = TRUE, !.pending = 0, !.epoch = @ + 1,
             !.generation = IF Mutation = "no-key-rotation" THEN @ ELSE @ + 1,
             !.exactRotation = cut = LogLength /\ cut = s.pending,
             !.turn = @ + 1]

Withdraw ==
  /\ s.enrolled
  /\ s' = [s EXCEPT !.enrolled = FALSE, !.writer = FALSE, !.turn = @ + 1]

Clock ==
  \E time \in (s.now + 1)..MaxTime:
    s' = [s EXCEPT !.now = time, !.turn = @ + 1]

Dispose ==
  LET due == s.leaseEnd = 0 \/ s.leaseEnd + 1 <= s.now IN
  /\ ~s.enrolled /\ s.hold /\ (due \/ (Mutation = "no-drift" /\ s.leaseEnd <= s.now))
  /\ s' = [s EXCEPT !.hold = FALSE, !.leaseEnd = 0, !.disposed = TRUE,
         !.disposedWithLease = s.leaseEnd # 0, !.disposalSafe = due, !.turn = @ + 1]

Trim ==
  \E cut \in (s.floor + 1)..s.root:
    /\ (~s.hold \/ (Mutation = "live-roots-only" /\ s.leaseEnd <= s.now))
    /\ s' = [s EXCEPT !.floor = cut, !.archived = SubSeq(s.seq, 1, cut), !.turn = @ + 1]

Close ==
  /\ s.oldRoot >= 0 /\ ~s.closed /\ ~s.hold
  /\ s' = [s EXCEPT !.closed = TRUE, !.turn = @ + 1]

Settle ==
  /\ s.oldRoot >= 0 /\ ~s.hold
  /\ \E evidence \in BOOLEAN:
      /\ (s.closed \/ Mutation = "sweep-root")
      /\ (evidence \/ Mutation = "no-disposition")
      /\ s' = [s EXCEPT !.oldRoot = -1, !.settled = TRUE, !.settlementSafe = s.closed /\ evidence,
             !.turn = @ + 1]

Fence ==
  /\ s.fence = 0
  /\ (Mutation = "sweep-name" \/ ~Physical(1))
  /\ (Mutation = "ignore-opaque" \/ ~Physical(0))
  /\ s' = [s EXCEPT !.fence = 7, !.turn = @ + 1]

Fund ==
  /\ s.window = 1
  /\ \E bytes \in 2..3:
      /\ (Used + bytes <= Capacity \/ Mutation = "unchecked-budget")
      /\ s' = [s EXCEPT !.window = bytes, !.spent = 0, !.turn = @ + 1]

Next ==
  /\ s.turn < MaxSteps
  /\ (AppendEntry \/ RetryMutation \/ Capture \/ RetryRead \/ Renew \/ Prepare \/ Select \/ Rotate \/
      Withdraw \/ Clock \/ Dispose \/ Trim \/ Close \/ Settle \/ Fence \/ Fund)

Spec == Init /\ [][Next]_s

WriterSafe == s.currentAppend
HistoryStable ==
  (LogLength > 0 => s.seq[1] = s.original[3]) /\ SubSeq(s.seq, 1, s.floor) = s.archived
ReceiptExact == s.retried => s.reply = s.original
ReadFresh == ~s.readReplay
CaptureExact == s.hold => s.holdThrough = s.capturedHead
LeaseRenewal == s.leaseSafe
LeaseBasisOpen == s.leaseBasisOpen
TrimSafe == s.floor <= s.root /\ (s.hold => s.floor = 0)
Funded == s.spent <= s.window /\ Used + s.window - s.spent <= Capacity
FenceSafe == s.fence # 0 => ~Physical(1) /\ ~Physical(0)
DisposalSafe == s.disposalSafe /\ (s.disposed => ~s.hold /\ s.leaseEnd = 0)
RotationGuard == s.exactRotation
ErasureAtomic ==
  s.rotated => s.generation = 2 /\ s.erasureFloor = s.root /\
    (\A pos \in (s.root + 1)..LogLength: s.seq[pos].generation = s.generation)
SettlementSafe == s.settlementSafe

NoMaintenanceWitness ==
  ~(s.rotated /\ s.floor = 1 /\ s.fence = 7 /\ s.window = 2 /\ s.retried)
NoDisposalWitness == ~s.disposedWithLease
NoSettlementWitness == ~(s.settled /\ ~s.rotated)
NoUnleasedHoldWitness == ~(s.hold /\ s.leaseEnd = 0 /\ s.rotated /\ s.root > 0)
NoDriftWindowWitness == ~(s.hold /\ ~s.enrolled /\ s.leaseEnd > 0 /\ s.now = s.leaseEnd)
=============================================================================
