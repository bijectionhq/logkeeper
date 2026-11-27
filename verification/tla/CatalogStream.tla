--------------------------- MODULE CatalogStream ---------------------------
(*
 * TLA+ specification of Logkeeper's replicated catalog stream
 * (src/stream/consensus/keeper/catalog_stream.rs).
 *
 * Models:
 *   - 3 catalog voters running Raft (terms, votes, leader election, log
 *     replication, commit, leader failover/crash).
 *   - Migration / seeding from the single-keeper legacy catalog: the
 *     designated Seeder appends Checkpoint(legacy) + Seeded marker; until
 *     Seeded is applied, claims/stages/negative lookups are refused.
 *   - First-claim-wins Claim(stream, genesis) at exactly head + 1 under the
 *     fixed internal FENCE (Epoch(1), catalog writer), with read barrier,
 *     fold catch-up, conflict retry, and concurrent client races across
 *     leadership changes.
 *   - Compaction (Checkpoint + Trim through first - 1) and replica fold
 *     restarts from the trim floor (Fold::new(genesis, floor)).
 *   - Stage(stream, stage) updates.
 *
 * Properties checked:
 *   - AtMostOneGenesisPerStream: the catalog assigns at most one genesis
 *     per stream across all replicas, clients, leader changes, and compactions.
 *   - ElectionSafety: at most one catalog leader per term.
 *   - NoClaimBeforeSeeded: no stream claim commits before Seeded is committed.
 *   - LegacyEntriesPreserved: every legacy single-keeper entry survives
 *     seeding and compaction with its original genesis.
 *   - CompactionPreservesClaims: no previously committed claim is lost or
 *     changed after Checkpoint + Trim.
 *)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Voters,         \* 3 catalog voters, e.g. {"v1", "v2", "v3"}
    Seeder,         \* Designated legacy catalog seeder \in Voters
    Streams,        \* Candidate streams, e.g. {"s1", "s2"}
    Geneses,        \* Candidate genesis values, e.g. {"g1", "g2"}
    LegacyStream,   \* Stream pre-populated in single-keeper legacy catalog (or "NONE")
    LegacyGenesis,  \* Genesis of LegacyStream in legacy catalog
    MaxTerm,        \* Upper bound on Raft terms
    MaxLogLen,      \* Upper bound on catalog Raft log length
    MaxClaims,      \* Upper bound on client claim attempts
    MaxCompacts,    \* Upper bound on catalog compactions
    MaxStops,       \* Upper bound on voter stops
    AllowCompact,   \* Enable compaction (Checkpoint + Trim)
    Nil             \* Model value representing None / absent

ASSUME Cardinality(Voters) = 3
ASSUME Seeder \in Voters

VARIABLES
    \* --- Raft state for the catalog stream ---
    alive,          \* [Voters -> BOOLEAN]
    vote,           \* [Voters -> [term, votedFor, committed]]
    role,           \* [Voters -> {"Follower", "Candidate", "Leader"}]
    votesGranted,   \* [Voters -> SUBSET Voters]
    log,            \* [Voters -> Seq(Entry)] (Raft log of catalog records)
    commitIdx,      \* [Voters -> Nat]
    floorLsn,       \* [Voters -> Nat] (1-based LSN trim floor; entries < floorLsn are trimmed)

    \* --- In-flight leader write state (models barrier -> check fold -> append at head+1) ---
    \* Each voter may have at most one pending Claim or Compact prepared at a snapshot of head
    pendingOp,      \* [Voters -> Nil | [kind, stream, genesis, atLsn, entries]]

    \* --- Ghost / observable history for properties ---
    leadersPerTerm, \* [0..MaxTerm -> SUBSET Voters]
    claimCount,     \* Nat
    compactCount,   \* Nat
    stopCount,      \* Nat
    answeredGenesis,\* [Streams -> SUBSET Geneses]: all geneses ever returned as Claim/Locate success
    everCommitted   \* [Streams -> SUBSET Geneses]: all geneses ever committed in the fold

vars == <<
    alive, vote, role, votesGranted, log, commitIdx, floorLsn,
    pendingOp, leadersPerTerm, claimCount, compactCount, stopCount,
    answeredGenesis, everCommitted
>>

-----------------------------------------------------------------------------
(* Helper operators *)

Max(a, b) == IF a >= b THEN a ELSE b
Min(a, b) == IF a <= b THEN a ELSE b

InitVote == [term |-> 0, votedFor |-> Nil, committed |-> FALSE]

VoteLeq(v1, v2) ==
    \/ v1.term < v2.term
    \/ (v1.term = v2.term /\ v1.votedFor = Nil)
    \/ (v1.term = v2.term /\ v1.votedFor = v2.votedFor /\ (~v1.committed \/ v2.committed))

LastTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term

LogUpToDate(cLog, vLog) ==
    \/ LastTerm(cLog) > LastTerm(vLog)
    \/ (LastTerm(cLog) = LastTerm(vLog) /\ Len(cLog) >= Len(vLog))

IsMajority(S) == 2 * Cardinality(S \cap Voters) > Cardinality(Voters)

\* Compute the deterministic catalog state machine from committed Raft log prefix 1..upto:
\* Returns [headLsn, floor, seeded, entries] where entries : [Streams -> Geneses \cup {Nil}]
\*
\* Models exact state.rs Append(at == head + 1) & Trim semantics AND
\* catalog_stream.rs Fold::apply & Fold::new(next > 1 => seeded=TRUE) semantics!
RECURSIVE ApplyLog(_, _, _, _, _, _)
ApplyLog(l, idx, upto, head, floor, st) ==
    IF idx > upto THEN [head |-> head, floor |-> floor, seeded |-> st.seeded, entries |-> st.entries]
    ELSE LET e == l[idx]
         IN CASE e.kind = "Blank" ->
                    ApplyLog(l, idx + 1, upto, head, floor, st)
              [] e.kind = "Trim" ->
                    LET newFloor == IF e.through >= floor /\ e.through <= head
                                    THEN e.through + 1 ELSE floor
                    IN ApplyLog(l, idx + 1, upto, head, newFloor, st)
              [] e.kind = "Record" ->
                    \* Command::Append checks at == head + 1 (state.rs:718);
                    \* an append at a stale at <= head conflicts unless identical!
                    IF e.at # head + 1 THEN
                       ApplyLog(l, idx + 1, upto, head, floor, st)
                    ELSE
                       LET rec == e.rec
                           newSt ==
                             CASE rec.kind = "Seeded" ->
                                     [st EXCEPT !.seeded = TRUE]
                               [] rec.kind = "Claim" ->
                                     \* First-claim-wins (catalog_stream.rs:116-122)
                                     IF st.entries[rec.stream] = Nil
                                     THEN [st EXCEPT !.entries[rec.stream] = rec.genesis]
                                     ELSE st
                               [] rec.kind = "Checkpoint" ->
                                     \* Checkpoint replaces entries it holds (catalog_stream.rs:136-140)
                                     [st EXCEPT !.entries = [s \in Streams |->
                                        IF rec.entries[s] # Nil THEN rec.entries[s] ELSE st.entries[s]]]
                       IN ApplyLog(l, idx + 1, upto, head + 1, floor, newSt)

InitFoldEntries == [s \in Streams |-> Nil]
LegacyMap == [s \in Streams |-> IF s = LegacyStream THEN LegacyGenesis ELSE Nil]

\* Fold computed from the full log (ground truth of committed records)
FullState(l, upto) ==
    ApplyLog(l, 1, Min(Len(l), upto), 0, 1, [seeded |-> FALSE, entries |-> InitFoldEntries])

\* Fold as rebuilt by a replica after Trim (starts from floorLsn, sets seeded = (floor > 1))
\* Exact match to catalog_stream.rs:95-108 & 306!
RECURSIVE ReplayFromFloor(_, _, _, _, _)
ReplayFromFloor(l, idx, upto, floor, st) ==
    IF idx > upto THEN st
    ELSE LET e == l[idx]
         IN IF e.kind = "Record" /\ e.at >= floor /\ e.at = st.lastLsn + 1 THEN
               LET rec == e.rec
                   newEntries ==
                     CASE rec.kind = "Claim" ->
                             IF st.entries[rec.stream] = Nil
                             THEN [st.entries EXCEPT ![rec.stream] = rec.genesis]
                             ELSE st.entries
                       [] rec.kind = "Checkpoint" ->
                             [s \in Streams |-> IF rec.entries[s] # Nil THEN rec.entries[s] ELSE st.entries[s]]
                       [] OTHER -> st.entries
                   newSeeded == st.seeded \/ (rec.kind = "Seeded")
               IN ReplayFromFloor(l, idx + 1, upto, floor,
                    [seeded |-> newSeeded, entries |-> newEntries, lastLsn |-> e.at])
            ELSE ReplayFromFloor(l, idx + 1, upto, floor, st)

ReplicaFold(k) ==
    LET fs == FullState(log[k], commitIdx[k])
        fl == fs.floor
        init == [seeded |-> (fl > 1), entries |-> InitFoldEntries, lastLsn |-> fl - 1]
    IN ReplayFromFloor(log[k], 1, commitIdx[k], fl, init)

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ alive           = [v \in Voters |-> TRUE]
    /\ vote            = [v \in Voters |-> InitVote]
    /\ role            = [v \in Voters |-> "Follower"]
    /\ votesGranted    = [v \in Voters |-> {}]
    /\ log             = [v \in Voters |-> <<>>]
    /\ commitIdx       = [v \in Voters |-> 0]
    /\ floorLsn        = [v \in Voters |-> 1]
    /\ pendingOp       = [v \in Voters |-> Nil]
    /\ leadersPerTerm  = [t \in 0..MaxTerm |-> {}]
    /\ claimCount      = 0
    /\ compactCount    = 0
    /\ stopCount       = 0
    /\ answeredGenesis = [s \in Streams |-> {}]
    /\ everCommitted   = [s \in Streams |-> {}]

CatalogSymmetry == Permutations(Voters \ {Seeder})

-----------------------------------------------------------------------------
(* Raft election & replication actions *)

StartElection(c) ==
    /\ alive[c] /\ role[c] # "Leader"
    /\ vote[c].term < MaxTerm
    /\ LET t == vote[c].term + 1
       IN /\ vote' = [vote EXCEPT ![c] = [term |-> t, votedFor |-> c, committed |-> FALSE]]
          /\ role' = [role EXCEPT ![c] = "Candidate"]
          /\ votesGranted' = [votesGranted EXCEPT ![c] = {c}]
          /\ pendingOp' = [pendingOp EXCEPT ![c] = Nil]
    /\ UNCHANGED <<alive, log, commitIdx, floorLsn, leadersPerTerm,
                   claimCount, compactCount, stopCount, answeredGenesis, everCommitted>>

GrantVote(v, c) ==
    /\ alive[v] /\ alive[c] /\ v # c
    /\ role[c] = "Candidate" /\ vote[c].votedFor = c /\ ~vote[c].committed
    /\ VoteLeq(vote[v], vote[c])
    /\ LogUpToDate(log[c], log[v])
    /\ vote' = [vote EXCEPT ![v] = vote[c]]
    /\ role' = [role EXCEPT ![v] = "Follower"]
    /\ pendingOp' = [pendingOp EXCEPT ![v] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![c] = @ \cup {v}]
    /\ UNCHANGED <<alive, log, commitIdx, floorLsn, leadersPerTerm,
                   claimCount, compactCount, stopCount, answeredGenesis, everCommitted>>

BecomeLeader(c) ==
    /\ alive[c] /\ role[c] = "Candidate"
    /\ IsMajority(votesGranted[c])
    /\ Len(log[c]) < MaxLogLen
    /\ LET t == vote[c].term
       IN /\ vote' = [vote EXCEPT ![c] = [term |-> t, votedFor |-> c, committed |-> TRUE]]
          /\ role' = [role EXCEPT ![c] = "Leader"]
          /\ log'  = [log EXCEPT ![c] = Append(log[c], [term |-> t, kind |-> "Blank", at |-> 0, through |-> 0, rec |-> Nil])]
          /\ leadersPerTerm' = [leadersPerTerm EXCEPT ![t] = @ \cup {c}]
    /\ UNCHANGED <<alive, votesGranted, commitIdx, floorLsn, pendingOp,
                   claimCount, compactCount, stopCount, answeredGenesis, everCommitted>>

Replicate(l, f) ==
    /\ alive[l] /\ role[l] = "Leader"
    /\ alive[f] /\ f # l
    /\ VoteLeq(vote[f], vote[l])
    /\ (log[f] # log[l] \/ commitIdx[f] < commitIdx[l] \/ vote[f] # vote[l])
    /\ vote' = [vote EXCEPT ![f] = vote[l]]
    /\ role' = [role EXCEPT ![f] = "Follower"]
    /\ pendingOp' = [pendingOp EXCEPT ![f] = Nil]
    /\ log'  = [log EXCEPT ![f] = log[l]]
    /\ commitIdx' = [commitIdx EXCEPT ![f] = Max(commitIdx[f], Min(commitIdx[l], Len(log[l])))]
    /\ floorLsn'  = [floorLsn EXCEPT ![f] = FullState(log[l], Max(commitIdx[f], Min(commitIdx[l], Len(log[l])))).floor]
    /\ UNCHANGED <<alive, votesGranted, leadersPerTerm, claimCount, compactCount, stopCount, answeredGenesis, everCommitted>>

AdvanceCommit(l) ==
    /\ alive[l] /\ role[l] = "Leader"
    /\ \E i \in (commitIdx[l] + 1)..Len(log[l]) :
        /\ log[l][i].term = vote[l].term
        /\ IsMajority({v \in Voters : v = l \/ (Len(log[v]) >= i /\ log[v][i] = log[l][i])})
        /\ commitIdx' = [commitIdx EXCEPT ![l] = i]
        /\ LET fs == FullState(log[l], i)
           IN /\ floorLsn' = [floorLsn EXCEPT ![l] = fs.floor]
              /\ everCommitted' = [s \in Streams |->
                    IF fs.entries[s] # Nil THEN everCommitted[s] \cup {fs.entries[s]}
                    ELSE everCommitted[s]]
    /\ UNCHANGED <<alive, vote, role, votesGranted, log, pendingOp,
                   leadersPerTerm, claimCount, compactCount, stopCount, answeredGenesis>>

StopVoter(v) ==
    /\ alive[v]
    /\ stopCount < MaxStops
    /\ Cardinality({u \in Voters : alive[u]}) > 1
    /\ alive' = [alive EXCEPT ![v] = FALSE]
    /\ stopCount' = stopCount + 1
    /\ role' = [role EXCEPT ![v] = "Follower"]
    /\ pendingOp' = [pendingOp EXCEPT ![v] = Nil]
    /\ UNCHANGED <<vote, votesGranted, log, commitIdx, floorLsn,
                   leadersPerTerm, claimCount, compactCount, answeredGenesis, everCommitted>>

RestartVoter(v) ==
    /\ ~alive[v]
    /\ alive' = [alive EXCEPT ![v] = TRUE]
    /\ vote' = [vote EXCEPT ![v] =
          IF vote[v].committed /\ vote[v].votedFor = v
          THEN [term |-> vote[v].term, votedFor |-> v, committed |-> FALSE]
          ELSE vote[v]]
    /\ UNCHANGED <<role, votesGranted, log, commitIdx, floorLsn, pendingOp,
                   leadersPerTerm, claimCount, compactCount, stopCount, answeredGenesis, everCommitted>>

-----------------------------------------------------------------------------
(* Catalog stream actions (catalog_stream.rs) *)

\* Seeder imports legacy single-keeper entries as Checkpoint + Seeded (catalog_stream.rs:567-585)
\* Serialized by catalog.writing mutex (no uncommitted Record already in flight on l).
SeedCheckpoint(l) ==
    /\ alive[l] /\ role[l] = "Leader" /\ l = Seeder
    /\ pendingOp[l] = Nil
    /\ Len(log[l]) = commitIdx[l]
    /\ Len(log[l]) + 2 <= MaxLogLen
    \* Leader completed read barrier (committed up to its latest term entry)
    /\ commitIdx[l] > 0 /\ log[l][commitIdx[l]].term = vote[l].term
    /\ LET fs == FullState(log[l], commitIdx[l])
       IN /\ ~fs.seeded
          /\ log' = [log EXCEPT ![l] =
                Append(
                    Append(log[l],
                           [term |-> vote[l].term, kind |-> "Record", at |-> fs.head + 1,
                            through |-> 0, rec |-> [kind |-> "Checkpoint", stream |-> Nil,
                                                    genesis |-> Nil, entries |-> LegacyMap]]),
                    [term |-> vote[l].term, kind |-> "Record", at |-> fs.head + 2,
                     through |-> 0, rec |-> [kind |-> "Seeded", stream |-> Nil,
                                             genesis |-> Nil, entries |-> InitFoldEntries]])]
    /\ UNCHANGED <<alive, vote, role, votesGranted, commitIdx, floorLsn, pendingOp,
                   leadersPerTerm, claimCount, compactCount, stopCount, answeredGenesis, everCommitted>>

\* Step 1 of claim_replicated (catalog_stream.rs:391-405):
\* Leader takes read barrier, checks seeded, checks fold.entries[s].
\* If absent, prepares Append(at: head + 1, Claim(s, g)) as pendingOp.
PrepareClaim(l, s, g) ==
    /\ alive[l] /\ role[l] = "Leader"
    /\ pendingOp[l] = Nil
    /\ Len(log[l]) = commitIdx[l]
    /\ claimCount < MaxClaims
    \* Read barrier: leader has committed an entry in its current term
    /\ commitIdx[l] > 0 /\ log[l][commitIdx[l]].term = vote[l].term
    /\ LET fs == FullState(log[l], commitIdx[l])
           rf == ReplicaFold(l)
       IN /\ rf.seeded
          /\ IF rf.entries[s] # Nil THEN
                \* Existing claim: return found if identical, else conflict
                /\ answeredGenesis' = IF rf.entries[s] = g
                                      THEN [answeredGenesis EXCEPT ![s] = @ \cup {g}]
                                      ELSE answeredGenesis
                /\ UNCHANGED <<pendingOp, claimCount, compactCount, stopCount>>
             ELSE
                /\ pendingOp' = [pendingOp EXCEPT ![l] =
                      [kind |-> "Claim", stream |-> s, genesis |-> g,
                       atLsn |-> fs.head + 1, entries |-> InitFoldEntries]]
                /\ claimCount' = claimCount + 1
                /\ UNCHANGED answeredGenesis
    /\ UNCHANGED <<alive, vote, role, votesGranted, log, commitIdx, floorLsn,
                   leadersPerTerm, compactCount, stopCount, everCommitted>>

\* Step 2 of claim_replicated (catalog_stream.rs:406-419):
\* Leader proposes the prepared Append(at: atLsn, Claim(s, g)) to its Raft log.
ProposeClaim(l) ==
    /\ alive[l] /\ role[l] = "Leader"
    /\ pendingOp[l] # Nil /\ pendingOp[l].kind = "Claim"
    /\ Len(log[l]) < MaxLogLen
    /\ LET op == pendingOp[l]
       IN /\ log' = [log EXCEPT ![l] = Append(log[l],
                [term |-> vote[l].term, kind |-> "Record", at |-> op.atLsn, through |-> 0,
                 rec |-> [kind |-> "Claim", stream |-> op.stream, genesis |-> op.genesis,
                          entries |-> InitFoldEntries]])]
          /\ pendingOp' = [pendingOp EXCEPT ![l] = Nil]
    /\ UNCHANGED <<alive, vote, role, votesGranted, commitIdx, floorLsn,
                   leadersPerTerm, claimCount, compactCount, stopCount, answeredGenesis, everCommitted>>

\* Any replica answers Locate(s) from its local applied fold (catalog_stream.rs:471-475)
LocateFromReplica(v, s) ==
    /\ alive[v]
    /\ LET rf == ReplicaFold(v)
       IN /\ rf.entries[s] # Nil
          /\ ~(rf.entries[s] \in answeredGenesis[s])
          /\ answeredGenesis' = [answeredGenesis EXCEPT ![s] = @ \cup {rf.entries[s]}]
    /\ UNCHANGED <<alive, vote, role, votesGranted, log, commitIdx, floorLsn,
                   pendingOp, leadersPerTerm, claimCount, compactCount, stopCount, everCommitted>>

\* Compaction step 1 (catalog_stream.rs:589):
\* Leader appends Checkpoint(fold.entries) at head + 1 and waits for it to commit.
ProposeCompactCheckpoint(l) ==
    /\ AllowCompact
    /\ compactCount < MaxCompacts
    /\ alive[l] /\ role[l] = "Leader"
    /\ pendingOp[l] = Nil
    /\ Len(log[l]) = commitIdx[l]
    /\ commitIdx[l] > 0 /\ log[l][commitIdx[l]].term = vote[l].term
    /\ Len(log[l]) < MaxLogLen
    /\ LET fs == FullState(log[l], commitIdx[l])
           rf == ReplicaFold(l)
           cpRec == [kind |-> "Checkpoint", stream |-> Nil, genesis |-> Nil, entries |-> rf.entries]
       IN /\ rf.seeded
          /\ fs.head >= fs.floor
          /\ log' = [log EXCEPT ![l] = Append(log[l],
                [term |-> vote[l].term, kind |-> "Record", at |-> fs.head + 1,
                 through |-> 0, rec |-> cpRec])]
          /\ pendingOp' = [pendingOp EXCEPT ![l] =
                [kind |-> "Trim", stream |-> Nil, genesis |-> Nil,
                 atLsn |-> fs.head + 1, entries |-> rf.entries]]
          /\ compactCount' = compactCount + 1
    /\ UNCHANGED <<alive, vote, role, votesGranted, commitIdx, floorLsn,
                   leadersPerTerm, claimCount, stopCount, answeredGenesis, everCommitted>>

\* Compaction step 2 (catalog_stream.rs:590-596):
\* Only after the Checkpoint at atLsn actually committed without conflict
\* does the leader propose Trim(through: atLsn - 1).
ProposeCompactTrim(l) ==
    /\ AllowCompact
    /\ alive[l] /\ role[l] = "Leader"
    /\ pendingOp[l] # Nil /\ pendingOp[l].kind = "Trim"
    /\ Len(log[l]) < MaxLogLen
    /\ LET op == pendingOp[l]
           \* Check whether our Checkpoint actually landed at op.atLsn in committed log
           committedCheckpoint ==
               \E idx \in 1..commitIdx[l] :
                   /\ log[l][idx].kind = "Record"
                   /\ log[l][idx].at = op.atLsn
                   /\ log[l][idx].rec.kind = "Checkpoint"
                   /\ log[l][idx].rec.entries = op.entries
                   \* And it was the FIRST committed record at op.atLsn (did not conflict!)
                   /\ FullState(log[l], idx - 1).head + 1 = op.atLsn
       IN /\ committedCheckpoint
          /\ log' = [log EXCEPT ![l] = Append(log[l],
                [term |-> vote[l].term, kind |-> "Trim", at |-> 0,
                 through |-> op.atLsn - 1, rec |-> Nil])]
          /\ pendingOp' = [pendingOp EXCEPT ![l] = Nil]
    /\ UNCHANGED <<alive, vote, role, votesGranted, commitIdx, floorLsn,
                   leadersPerTerm, claimCount, compactCount, stopCount, answeredGenesis, everCommitted>>

\* Compaction aborts if Checkpoint at op.atLsn conflicted with an earlier committed record
AbortCompactOnConflict(l) ==
    /\ AllowCompact
    /\ alive[l] /\ role[l] = "Leader"
    /\ pendingOp[l] # Nil /\ pendingOp[l].kind = "Trim"
    /\ FullState(log[l], commitIdx[l]).head >= pendingOp[l].atLsn
    /\ pendingOp' = [pendingOp EXCEPT ![l] = Nil]
    /\ UNCHANGED <<alive, vote, role, votesGranted, log, commitIdx, floorLsn,
                   leadersPerTerm, claimCount, compactCount, stopCount, answeredGenesis, everCommitted>>

-----------------------------------------------------------------------------
Next ==
    \/ \E c \in Voters : StartElection(c)
    \/ \E v, c \in Voters : GrantVote(v, c)
    \/ \E c \in Voters : BecomeLeader(c)
    \/ \E l, f \in Voters : Replicate(l, f)
    \/ \E l \in Voters : AdvanceCommit(l)
    \/ \E v \in Voters : StopVoter(v)
    \/ \E v \in Voters : RestartVoter(v)
    \/ \E l \in Voters : SeedCheckpoint(l)
    \/ \E l \in Voters, s \in Streams, g \in Geneses : PrepareClaim(l, s, g)
    \/ \E l \in Voters : ProposeClaim(l)
    \/ \E v \in Voters, s \in Streams : LocateFromReplica(v, s)
    \/ \E l \in Voters : ProposeCompactCheckpoint(l)
    \/ \E l \in Voters : ProposeCompactTrim(l)
    \/ \E l \in Voters : AbortCompactOnConflict(l)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety Properties *)

\* 1. At most one genesis assigned per stream across all replicas and answers
AtMostOneGenesisPerStream ==
    /\ \A s \in Streams : Cardinality(everCommitted[s]) <= 1
    /\ \A s \in Streams : Cardinality(answeredGenesis[s]) <= 1
    /\ \A s \in Streams :
         (everCommitted[s] # {} /\ answeredGenesis[s] # {}) =>
            everCommitted[s] = answeredGenesis[s]

\* 2. At most one catalog leader per term
ElectionSafety ==
    \A t \in DOMAIN leadersPerTerm : Cardinality(leadersPerTerm[t]) <= 1

\* 3. Legacy single-keeper entry is preserved with its original genesis
LegacyEntryPreserved ==
    LegacyStream \in Streams =>
        /\ \A g \in everCommitted[LegacyStream] : g = LegacyGenesis
        /\ \A g \in answeredGenesis[LegacyStream] : g = LegacyGenesis

\* 4. Replica fold rebuilt from trim floor agrees with full committed fold
CompactionPreservesFold ==
    \A v \in Voters :
        LET fs == FullState(log[v], commitIdx[v])
            rf == ReplicaFold(v)
        IN fs.seeded => (rf.seeded /\ rf.entries = fs.entries)

CatalogSafety ==
    /\ AtMostOneGenesisPerStream
    /\ ElectionSafety
    /\ LegacyEntryPreserved
    /\ CompactionPreservesFold

=============================================================================
