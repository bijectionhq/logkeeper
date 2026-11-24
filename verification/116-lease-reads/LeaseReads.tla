------------------------------ MODULE LeaseReads ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Design, Fault, Horizon, Term, Drift, OrphanTTL, KeyGrace, SecondRead, Reconfigure

Cuts == 0..2
Epochs == 0..1
Attempts == 1..2
None == 3
Ordered == Design = "barrier"
Fallback == Design = "fallback"

VARIABLES time, journal, serving, reads, leaseWork

vars == <<time, journal, serving, reads, leaseWork>>

Gate(cut, keyStart, end) ==
    [applied |-> cut, chosen |-> cut, keyStart |-> keyStart,
     until |-> end, floor |-> cut]

EmptyRead ==
    [phase |-> "idle", request |-> None, invocation |-> 0,
     cut |-> None, owner |-> None, held |-> FALSE, until |-> 0,
     atCurrent |-> TRUE, atLiveLease |-> TRUE, capturedHead |-> 0,
     useEpoch |-> None, erasedAtUse |-> FALSE, usedMissing |-> FALSE,
     ordered |-> FALSE, releasedByCommand |-> FALSE, rounds |-> 0, entries |-> 0]

Init ==
    /\ time = [now |-> 0, local |-> 0]
    /\ journal = [epoch |-> 0, pending |-> None, appended |-> FALSE,
                   rotation |-> None, revokeAt |-> Horizon + 1,
                   trimmed |-> 0, collected |-> 0]
    /\ serving = [e \in Epochs |-> IF e = 0 THEN Gate(0, 0, Term)
                         ELSE [Gate(0, 0, 0) EXCEPT !.floor = None]]
    /\ reads = [i \in Attempts |-> EmptyRead]
    /\ leaseWork = [renewals |-> 0, rounds |-> 0, entries |-> 0, sampledCuts |-> 0]

Current == journal.epoch
Head == serving[Current].chosen
Resident(cut) == cut >= journal.trimmed /\ cut >= journal.collected
Erased(cut) == cut < journal.rotation /\ time.now >= journal.revokeAt
Least(cuts) == CHOOSE m \in cuts : \A c \in cuts : m <= c

Tick ==
    /\ time.now < Horizon
    /\ LET next == time.now + 1
           clocks == IF Ordered THEN {next}
                     ELSE IF Fault = "slow-clock" THEN time.local..(next + Drift)
                     ELSE {c \in time.local..(next + Drift) : c >= next - Drift}
       IN time' \in {[now |-> next, local |-> c] : c \in clocks}
    /\ UNCHANGED <<journal, serving, reads, leaseWork>>

\* The writer closes its latest-read gate before proposing, including the
\* interval in which the outcome is uncertain. Applying a chosen cut reopens it.
ProposeAppend ==
    /\ ~journal.appended
    /\ journal.pending = None
    /\ journal' = [journal EXCEPT !.pending = Current]
    /\ UNCHANGED <<time, serving, reads, leaseWork>>

ChooseAppend ==
    /\ journal.pending = Current
    /\ journal' = [journal EXCEPT !.pending = None, !.appended = TRUE]
    /\ serving' = [serving EXCEPT ![Current].chosen = @ + 1]
    /\ UNCHANGED <<time, reads, leaseWork>>

Apply ==
    /\ serving[Current].applied < Head
    /\ serving' = [serving EXCEPT ![Current].applied = Head]
    /\ UNCHANGED <<time, journal, reads, leaseWork>>

LocalLease(e) == time.local + Drift < serving[e].until
LocalReady(e) == journal.pending # e /\ serving[e].applied = serving[e].chosen
LocalNamed(e, cut) ==
    LocalLease(e) /\ cut >= serving[e].keyStart /\ cut \in serving[e].floor..serving[e].applied

LocalCuts(e) == {reads[i].cut : i \in {j \in Attempts :
                  reads[j].held /\ ~reads[j].ordered /\ reads[j].owner = e}}

Renew ==
    /\ ~Ordered
    /\ leaseWork.renewals = 0
    /\ LocalLease(Current)
    /\ time.now + Term > serving[Current].until
    /\ LET candidates == LocalCuts(Current) \cup {serving[Current].applied}
       IN serving' = [serving EXCEPT ![Current].until = time.now + Term,
                                     ![Current].floor = Least(candidates)]
    /\ leaseWork' = [renewals |-> 1, rounds |-> 1, sampledCuts |-> Cardinality(LocalCuts(Current)),
                     entries |-> IF Fault = "free-renewal" THEN 0 ELSE 1]
    /\ UNCHANGED <<time, journal, reads>>

\* Both replacement and key rotation must close prior local admission.
\* The predecessor's drain obligation survives installation of the successor.
Install(rotate) ==
    /\ Reconfigure /\ Current = 0
    /\ Ordered \/ time.now >= serving[0].until \/ Fault = "early-install"
    /\ LET next == IF rotate THEN Head + 1 ELSE Head
           keyStart == IF rotate THEN next ELSE serving[0].keyStart
           end == IF Ordered THEN 0 ELSE time.now + Term
       IN /\ journal' = [journal EXCEPT !.epoch = 1, !.pending = None,
                              !.rotation = IF rotate THEN next ELSE @,
                              !.revokeAt = IF rotate THEN time.now + KeyGrace ELSE @]
          /\ serving' = [serving EXCEPT ![1] =
                              [Gate(next, keyStart, end) EXCEPT !.floor =
                                  IF rotate THEN next ELSE journal.trimmed]]
    /\ UNCHANGED <<time, reads, leaseWork>>

DropFloor(e) ==
    /\ ~Ordered
    /\ serving[e].floor # None
    /\ time.now >= serving[e].until
    /\ LocalCuts(e) = {} \/ Fault = "expire-floor"
    /\ serving' = [serving EXCEPT ![e].floor = None]
    /\ UNCHANGED <<time, journal, reads, leaseWork>>

Invoke(i) ==
    /\ reads[i].phase = "idle"
    /\ i = 1 \/ (SecondRead /\ reads[1].cut # None)
    /\ reads' = [reads EXCEPT ![i].phase = "invoked", ![i].invocation = Head,
        ![i].request = IF i = 2 /\ reads[1].phase = "lost" THEN reads[1].cut ELSE None]
    /\ UNCHANGED <<time, journal, serving, leaseWork>>

Capture(i, e, ordered) ==
    LET r == reads[i]
        latest == CASE ordered /\ Fault # "barrier-applied-cut" -> Head
                    [] Fault = "speculative-cut" /\ journal.pending = e -> serving[e].applied + 1
                    [] OTHER -> serving[e].applied
        cut == IF r.request = None \/ Fault = "resample-retry" THEN latest ELSE r.request
        charge == IF ordered \/ Fault = "charge-local" THEN 1 ELSE 0
    IN /\ r.phase = "invoked"
       /\ cut \in serving[e].keyStart..latest
       /\ IF ordered
              THEN /\ e = Current \/ (e < Current /\ Fault = "stale-barrier")
                   /\ Resident(cut)
                   /\ Ordered \/ (Fallback /\ r.request # None /\ ~LocalNamed(e, r.request))
              ELSE /\ ~Ordered
                   /\ LocalLease(e) \/ Fault = "admit-expired"
                   /\ r.request # None \/ LocalReady(e) \/ Fault \in {"lagging-apply", "speculative-cut"}
                   /\ serving[e].floor # None
                   /\ cut >= serving[e].floor \/ (Fault = "periodic-only" /\ Resident(cut))
       /\ reads' = [reads EXCEPT ![i] =
              [r EXCEPT !.phase = "held", !.cut = cut, !.owner = e, !.held = TRUE,
                        !.until = time.now + OrphanTTL, !.atCurrent = (e = Current),
                        !.atLiveLease = (ordered \/ time.now < serving[e].until),
                        !.capturedHead = Head, !.ordered = ordered,
                        !.rounds = charge, !.entries = charge]]
       /\ UNCHANGED <<time, journal, serving, leaseWork>>

\* A fresh named admission can fail if its original basis is no longer eligible.
RefuseNamed(i) ==
    LET r == reads[i]
    IN /\ r.phase = "invoked"
       /\ r.request # None
       /\ \/ r.request < serving[Current].keyStart
          \/ ~Resident(r.request)
          \/ ~Ordered /\ ~Fallback /\ r.request < serving[Current].floor
       /\ reads' = [reads EXCEPT ![i].phase = "refused"]
       /\ UNCHANGED <<time, journal, serving, leaseWork>>

\* The result and the lifetime of its borrow are separate. A held old-generation
\* view participates in the key fence on use, including after lease/epoch change.
Use(i, lose) ==
    LET r == reads[i]
        expired == Erased(r.cut)
        denied == IF Fault = "revoke-on-rotation"
                  THEN r.cut < journal.rotation /\ journal.rotation # None
                  ELSE expired /\ Fault # "skip-key-fence"
        missing == ~Resident(r.cut)
        ok == ~denied /\ ~missing
    IN /\ r.phase = "held"
       /\ lose => (i = 1 /\ ok)
       /\ reads' = [reads EXCEPT ![i].phase =
              CASE denied -> "erased"
                [] missing -> "unavailable"
                [] lose -> "lost"
                [] OTHER -> "replied",
              ![i].until = IF lose THEN @ ELSE 0,
              ![i].useEpoch = Current, ![i].erasedAtUse = expired,
              ![i].usedMissing = missing]
       /\ UNCHANGED <<time, journal, serving, leaseWork>>

Release(i, expire) ==
    LET r == reads[i]
        command == r.ordered /\ ~expire
        charge == IF command /\ Fault # "free-release" THEN 1 ELSE 0
    IN /\ r.held
       /\ IF expire
              THEN r.phase = "lost" /\ time.now >= r.until
              ELSE r.phase \in {"replied", "erased", "unavailable", "lost"}
       /\ reads' = [reads EXCEPT ![i].held = FALSE, ![i].releasedByCommand = command,
                                 ![i].rounds = @ + charge, ![i].entries = @ + charge]
       /\ UNCHANGED <<time, journal, serving, leaseWork>>

ProtectedBelow(cut) ==
    \/ \E i \in Attempts : reads[i].held /\ reads[i].ordered /\ reads[i].cut < cut
    \/ ~Ordered /\ (\E e \in Epochs : serving[e].floor < cut)

\* Each cut has a distinct exact basis (root, suffix and object abstracted as
\* one identity). The current head also has a published checkpoint in this model.
Trim(cut) ==
    /\ cut \in (journal.trimmed + 1)..Head
    /\ ~ProtectedBelow(cut) \/ Fault = "trim-held"
    /\ journal' = [journal EXCEPT !.trimmed = cut]
    /\ UNCHANGED <<time, serving, reads, leaseWork>>

Collect(cut) ==
    /\ cut \in (journal.collected + 1)..Head
    /\ (cut <= journal.trimmed /\ ~ProtectedBelow(cut)) \/ Fault = "collect-held"
    /\ journal' = [journal EXCEPT !.collected = cut]
    /\ UNCHANGED <<time, serving, reads, leaseWork>>

Next ==
    \/ Tick \/ ProposeAppend \/ ChooseAppend \/ Apply \/ Renew
    \/ Install(FALSE) \/ Install(TRUE)
    \/ \E e \in Epochs : DropFloor(e)
    \/ \E cut \in Cuts : Trim(cut) \/ Collect(cut)
    \/ \E i \in Attempts :
          \/ Invoke(i) \/ RefuseNamed(i)
          \/ \E e \in Epochs : Capture(i, e, TRUE) \/ Capture(i, e, FALSE)
          \/ Use(i, FALSE) \/ Use(i, TRUE)
          \/ Release(i, FALSE) \/ Release(i, TRUE)

Spec == Init /\ [][Next]_vars

\* Sampled head and invocation head are ghosts used only to check the interval.
LatestLinearizable ==
    \A r \in {reads[i] : i \in Attempts} :
        r.cut # None /\ r.request = None => r.cut \in r.invocation..r.capturedHead

CommittedPrefix ==
    \A r \in {reads[i] : i \in Attempts} : r.cut # None => r.cut \in 0..r.capturedHead

FreshAuthority == \A i \in Attempts : reads[i].atCurrent
ServingDeadline == \A i \in Attempts : reads[i].atLiveLease

TrimPreservesHolds ==
    \A i \in Attempts : reads[i].held => reads[i].cut >= journal.trimmed

CollectionPreservesHolds ==
    \A i \in Attempts : reads[i].held => reads[i].cut >= journal.collected

ErasureDeadline ==
    \A r \in {reads[i] : i \in Attempts} :
        /\ (r.phase = "erased" => r.erasedAtUse)
        /\ (r.phase \in {"replied", "lost"} => ~r.erasedAtUse /\ ~r.usedMissing)

SameBasisRetry ==
    reads[2].request # None /\ reads[2].cut # None => reads[2].cut = reads[1].cut

RetainedNamedAdmission ==
    \A i \in Attempts :
        LET r == reads[i]
        IN r.phase = "invoked" /\ r.request \in serving[Current].keyStart..Head /\ Resident(r.request)
           => ENABLED (Capture(i, Current, TRUE) \/ Capture(i, Current, FALSE))

CostAccounting ==
    /\ \A r \in {reads[i] : i \in Attempts} :
        LET expected == (IF r.ordered THEN 1 ELSE 0) + (IF r.releasedByCommand THEN 1 ELSE 0)
        IN r.rounds = expected /\ r.entries = expected
    /\ leaseWork.rounds = leaseWork.renewals /\ leaseWork.entries = leaseWork.renewals

\* Each witness is the negation of a reachable history, checked separately.
ServedAndCollectedWitness ==
    ~(reads[1].phase = "replied" /\ ~reads[1].held /\ journal.collected > reads[1].cut)

AcrossReplacementWitness ==
    ~(Current = 1 /\ journal.rotation = None /\ reads[1].phase = "replied" /\
      reads[1].held /\ reads[1].owner = 0 /\ reads[1].useEpoch = 1 /\
      reads[2].phase = "replied" /\ reads[2].owner = 1)

ErasedHeldViewWitness ==
    ~(reads[1].phase = "erased" /\ reads[1].held /\ Current = 1 /\
      reads[1].owner = 0 /\ journal.rotation # None)

CleanAndErasedWitness ==
    ~(reads[1].phase = "erased" /\ reads[1].held /\ journal.rotation # None /\
      reads[2].phase = "replied" /\ reads[2].owner = 1 /\ reads[2].cut >= journal.rotation)

ViewBeforeErasureDeadlineWitness ==
    ~(reads[1].phase = "replied" /\ reads[1].held /\ journal.rotation # None /\
      reads[1].cut < journal.rotation /\ reads[1].useEpoch = 1 /\ time.now < journal.revokeAt)

SameBasisRetryWitness ==
    ~(reads[1].phase = "lost" /\ ~reads[1].held /\ reads[2].phase = "replied" /\
      reads[1].owner = 0 /\ reads[2].owner = 1 /\
      reads[2].request = reads[1].cut /\ reads[2].cut < Head)

OrphanExpiryWitness ==
    ~(reads[1].phase = "lost" /\ ~reads[1].held /\ ~reads[1].releasedByCommand /\
      time.now >= reads[1].until /\ journal.collected > reads[1].cut)

ReportedMinimumWitness ==
    ~(leaseWork.sampledCuts = 2 /\ reads[1].held /\ reads[2].held /\
      reads[1].owner = Current /\ reads[2].owner = Current /\
      reads[1].cut < reads[2].cut /\ serving[Current].floor = reads[1].cut /\
      serving[Current].applied = reads[2].cut)

BelowReportRetryWitness ==
    ~(reads[2].phase = "refused" /\ reads[2].request # None /\ Resident(reads[2].request) /\
      Current = 0 /\ reads[2].request < serving[0].floor /\ leaseWork.renewals = 1)

OrderedFallbackWitness ==
    ~(reads[2].phase = "replied" /\ reads[2].ordered /\ reads[2].request # None /\
      Current = 0 /\ reads[2].request < serving[0].floor /\ leaseWork.renewals = 1)

RenewedBatchWitness ==
    ~(leaseWork.renewals = 1 /\ \A i \in Attempts :
        reads[i].phase = "replied" /\ ~reads[i].held /\ reads[i].rounds = 0)
=============================================================================
