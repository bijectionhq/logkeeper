------------------------- MODULE LogkeeperProtocol -------------------------
(*
 * TLA+ specification of Logkeeper's consensus keeper protocol additions on
 * top of OpenRaft 0.10.1.
 *
 * Modeled components and their Rust counterparts:
 *   - Raft core with OpenRaft 0.10 votes (term, votedFor, committed),
 *     pre-vote, leader lease, quorum-loss step-down, restart vote demotion
 *     (decisions::demotes_vote), snapshots, and joint consensus.
 *   - Idle parking / unparking, parking past a dead follower, and the
 *     holder-driven wake sweep (keeper/park.rs, keeper/liveness.rs,
 *     keeper/ingress.rs).
 *   - Keeper liveness pings, leader-driven repair, staged replacement with
 *     Ownership high-water/generation tracking, aborted replacements, and
 *     stale learner removal (keeper/repair.rs, keeper/replacement.rs,
 *     keeper/replicas.rs, ownership.rs).
 *   - Self-retirement on certified placement proof and sender exclusion
 *     (decisions::excludes_sender, keeper/repair.rs::retire_removed,
 *     keeper/replicas.rs::retire_copy).
 *   - Keeper wipe-and-reinitialize under the same keeper ID (calibration for
 *     the confirmed Raft amnesia bug, commit 98f32fe).
 *   - Offline operator recovery: allows_recovery, StageRecovered, atomic
 *     Record::Recover at T' = max + RecoveryGap, recovery fence and
 *     acknowledgement, returning 1 or 2 lost voters, and client read
 *     observations (keeper/recovery.rs, decisions.rs, client/reading.rs).
 *)
EXTENDS Naturals, Sequences, FiniteSets, TLC, KeeperSafety

CONSTANTS
    Keepers,          \* Finite set of keeper IDs (e.g. {"k1","k2","k3","k4"})
    GenesisVoters,    \* Initial 3-keeper voter subset of Keepers
    Values,           \* Finite set of application record values
    MaxTerm,          \* Upper bound on normal Raft terms
    RecoveryGap,      \* Term jump for operator recovery (abstracts 2^32)
    MaxLogLen,        \* Upper bound on per-replica log length
    MaxAppends,       \* Upper bound on client appends (keeps state space finite)
    AllowPark,        \* Enable parking, unparking, and wake sweep
    AllowReplace,     \* Enable liveness death, leader-driven repair, staged joint replacement
    AllowRetire,      \* Enable heard-timeout, sender exclusion, and self-retirement on proof
    AllowAbortedReplace, \* Allow replacement to abort after StageReplica / add_learner
    AllowStaleLearner,\* Enable stale learner removal
    AllowWipe,        \* Enable wipe-and-reinitialize under the same ID
    AllowRecovery,    \* Enable offline operator recovery
    MaxReturningLost, \* Max lost voters allowed to restart after recovery (0, 1, or 2)
    AllowSurvivorStopAfterRecovery, \* Allow survivor to stop after recovery commits
    AllowSnapshot,    \* Allow local snapshot creation (persists applied state across restart)
    AllowClientReads, \* Enable client ReadAt observations (checks NoMixedHistory)
    AllowStop,        \* Allow keepers to stop/crash
    MaxStopped,       \* Upper bound on simultaneously stopped keepers
    MaxCrashes,       \* Upper bound on total StopKeeper events (keeps liveness sound)
    Nil               \* Model value representing None / absent

ASSUME GenesisVoters \subseteq Keepers
ASSUME Cardinality(GenesisVoters) = 3

VARIABLES
    \* --- Process & liveness state ---
    alive,            \* [Keepers -> BOOLEAN]
    deadView,         \* [Keepers -> SUBSET Keepers] (keeper_dead table)
    crashCount,       \* Nat: total StopKeeper transitions taken

    \* --- Durable disk state (storage/wal.rs, ownership.rs) ---
    registered,       \* [Keepers -> BOOLEAN] (disk.genesis exists)
    vote,             \* [Keepers -> [term, votedFor, committed]]
    log,              \* [Keepers -> Seq(Entry)]
    snapIdx,          \* [Keepers -> 0..MaxLogLen] (selected local snapshot index)
    ownership,        \* [Keepers -> [high, gen, current, retiredGens]]

    \* --- Volatile group state (keeper.rs, park.rs, repair.rs) ---
    groupState,       \* [Keepers -> {"Closed", "Open", "Parked"}]
    closedCfg,        \* [Keepers -> SUBSET Keepers] (closed_states finalized voters when parked)
    role,             \* [Keepers -> {"Follower", "Candidate", "Leader"}]
    commitIdx,        \* [Keepers -> 0..MaxLogLen]
    appliedIdx,       \* [Keepers -> 0..MaxLogLen]
    lease,            \* [Keepers -> Keepers \cup {Nil}] (OpenRaft leader lease holder)
    excluded,         \* [Keepers -> Keepers \cup {Nil}] (group.excluded)
    heardLeader,      \* [Keepers -> BOOLEAN] (FALSE => heard timeout >= repair_after)
    votesGranted,     \* [Keepers -> SUBSET Keepers] (votes collected by candidate in current term)
    activeStage,      \* [Keepers -> Stage \cup {Nil}] (leader's in-progress replacement stage)
    staleLearners,    \* [Keepers -> SUBSET Keepers] (learners past STALE_LEARNER)

    \* --- Operator recovery & ghost history state for invariants ---
    recovered,        \* BOOLEAN: operator recovery has been written
    recoveryAcked,    \* BOOLEAN: Command::AcknowledgeRecovery committed
    lostVoters,       \* SUBSET Keepers: the two voters excluded by recovery
    returnedLost,     \* SUBSET Keepers: lost voters that have restarted post-recovery
    survivorId,       \* Keepers \cup {Nil}: the survivor chosen by recovery
    appendCount,      \* Nat: number of client appends issued
    leadersPerTerm,   \* [Nat -> SUBSET Keepers]: all leaders ever elected per term
    committedApps,    \* SUBSET [lsn, val, term]: pre-recovery committed apps not acknowledged lost
    lostSuffix,       \* SUBSET [lsn, val, term]: committed apps acknowledged lost by recovery
    postRecApps,      \* SUBSET [lsn, val, term]: apps committed after recovery
    readerHistory,    \* SUBSET [lsn, val, term]: entries observed by readers after recovery
    retiredVoted,     \* BOOLEAN: a retired copy ever granted a vote

    \* --- Media incarnations and placement certification (keeper/incarnation.rs,
    \*     keeper/certify.rs) ---
    reused,           \* [Keepers -> BOOLEAN] keeper ID reused on new media (6d75fec)
    certified,        \* [Keepers -> BOOLEAN] copy certified since it opened (volatile)
    fenced,           \* [Keepers -> BOOLEAN] the catalog fenced this copy's configuration
    catalogStage      \* Nil or [stage, recovery]: the catalog's latest staged move

vars == <<
    alive, deadView, crashCount, registered, vote, log, snapIdx, ownership,
    groupState, closedCfg, role, commitIdx, appliedIdx, lease,
    excluded, heardLeader, votesGranted, activeStage, staleLearners,
    recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
    appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
    readerHistory, retiredVoted, reused, certified, fenced, catalogStage
>>

fenceVars == <<reused, certified, fenced, catalogStage>>

-----------------------------------------------------------------------------
(* Helper operators *)

Max(a, b) == IF a >= b THEN a ELSE b
Min(a, b) == IF a <= b THEN a ELSE b

InitVote == [term |-> 0, votedFor |-> Nil, committed |-> FALSE]

\* OpenRaft 0.10 standard Raft vote partial order (leader_id_std):
\* within the same term, a committed leader supersedes an uncommitted
\* candidate, including a different one (OpenRaft RefVote).
TermLess(a, b) == a < b
VoteLeq(v1, v2) == RaftVoteLeq(v1, v2, Nil, TermLess)

\* decisions::demotes_vote (decisions.rs:228, storage/mod.rs:136)
DemoteVote(k, v) ==
    IF v.committed /\ v.votedFor = k
    THEN [term |-> v.term, votedFor |-> k, committed |-> FALSE]
    ELSE v

LastLogIndex(l) == Len(l)
LastLogTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term

LogUpToDate(candLog, voterLog) ==
    \/ LastLogTerm(candLog) > LastLogTerm(voterLog)
    \/ (LastLogTerm(candLog) = LastLogTerm(voterLog) /\ LastLogIndex(candLog) >= LastLogIndex(voterLog))

IsCfgEntry(e) == e.kind \in {"InitCfg", "JointCfg", "FinalCfg"}

\* Last membership entry in prefix 1..upto of sequence l
MembershipIn(l, upto) ==
    LET idxs == {i \in 1..Min(Len(l), upto) : IsCfgEntry(l[i])}
    IN IF idxs = {}
       THEN [configured |-> FALSE, isJoint |-> FALSE, voters1 |-> {}, voters2 |-> {}, learners |-> {}, rev |-> 0]
       ELSE LET m == l[CHOOSE i \in idxs : \A j \in idxs : i >= j]
            IN [configured |-> TRUE,
                isJoint |-> (m.kind = "JointCfg"),
                voters1 |-> m.voters,
                voters2 |-> m.joint,
                learners |-> m.learners,
                rev |-> m.rev]

EffectiveMembership(k) == MembershipIn(log[k], Len(log[k]))
AppliedMembership(k)   == MembershipIn(log[k], appliedIdx[k])

AllVoters(m) == m.voters1 \cup m.voters2
AllNodes(m)  == m.voters1 \cup m.voters2 \cup m.learners

IsMajority(S, V) == Majority(S, V)

IsQuorum(S, m) ==
    /\ m.configured
    /\ IsMajority(S, m.voters1)
    /\ (m.isJoint => IsMajority(S, m.voters2))

\* decisions::excludes_sender (decisions.rs:299, ingress.rs:471)
ExcludesSender(recv, sender, senderTerm) ==
    LET m == EffectiveMembership(recv)
    IN m.configured /\ ~(sender \in AllNodes(m)) /\ senderTerm < vote[recv].term

\* Recovering replacement copy predicate (ingress.rs:518-526)
IsRecoveringCopy(k) ==
    LET cur == ownership[k].current
        m   == EffectiveMembership(k)
    IN /\ cur # Nil
       /\ cur.installed
       /\ cur.isRecovery
       /\ cur.stage # Nil
       /\ ( ~m.configured
            \/ (~m.isJoint /\ m.voters1 = cur.stage.old) )

\* decisions::votes (decisions.rs:316, ingress.rs:527)
CanVote(k) ==
    LET cur == ownership[k].current
        m   == EffectiveMembership(k)
        installed == (cur # Nil /\ cur.installed)
        member    == (k \in AllVoters(m))
        genVoter  == (k \in GenesisVoters)
    IN installed /\ (IsRecoveringCopy(k) \/ (IF m.configured THEN member ELSE genVoter))

\* decisions::fences_copy (keeper/certify.rs): the catalog's latest staged move
\* fences a copy whose effective configuration is neither side of that move.
\* A recovery fences its lost configuration too: only its target goes on.
\* A copy without a configuration (an empty recovery replacement) cannot
\* campaign or serve, so it is never fenced.
FencedByCatalog(k) ==
    LET m == EffectiveMembership(k)
        cs == catalogStage
    IN /\ cs # Nil
       /\ m.configured
       /\ IF cs.recovery
          THEN ~(~m.isJoint /\ m.voters1 = cs.stage.target)
          ELSE ~( (~m.isJoint /\ m.voters1 \in {cs.stage.old, cs.stage.target})
                \/ (m.isJoint /\ m.voters1 = cs.stage.old /\ m.voters2 = cs.stage.target))

\* Application entries contained in prefix 1..upto of log l, as [lsn, val, term] triples
AppEntriesWithTermIn(l, upto) ==
    LET lim == Min(Len(l), upto)
        appIdxs == {i \in 1..lim : l[i].kind = "App"}
    IN {[lsn |-> l[i].lsn, val |-> l[i].val, term |-> l[i].term] : i \in appIdxs}

\* Application entries contained in prefix 1..upto of log l, as [lsn, val] pairs
AppEntriesIn(l, upto) ==
    LET lim == Min(Len(l), upto)
        appIdxs == {i \in 1..lim : l[i].kind = "App"}
    IN {[lsn |-> l[i].lsn, val |-> l[i].val] : i \in appIdxs}

\* Highest LSN of App entries in prefix 1..upto
HeadLsnIn(l, upto) ==
    LET apps == AppEntriesIn(l, upto)
    IN IF apps = {} THEN 0
       ELSE (CHOOSE a \in apps : \A b \in apps : a.lsn >= b.lsn).lsn

\* Whether prefix 1..upto contains an unacknowledged recovery fence
HasRecoveryFence(l, upto) ==
    LET lim == Min(Len(l), upto)
        recIdxs == {i \in 1..lim : l[i].kind = "Recover"}
        ackIdxs == {i \in 1..lim : l[i].kind = "AckRec"}
    IN IF recIdxs = {} THEN FALSE
       ELSE IF ackIdxs = {} THEN TRUE
       ELSE (CHOOSE i \in recIdxs : \A j \in recIdxs : i >= j) >
            (CHOOSE i \in ackIdxs : \A j \in ackIdxs : i >= j)

\* Whether leader l has an uncommitted membership or staging entry in flight
\* (serialized by group.membership mutex in replacement.rs / repair.rs)
HasPendingMgmt(l) ==
    \E i \in (commitIdx[l] + 1)..Len(log[l]) :
        log[l][i].kind \in {"StageOwned", "InitCfg", "JointCfg", "FinalCfg"}

\* Latest staged receipt in applied log (StageOwned or Recover before FinalCfg)
AppliedStage(k) ==
    LET lim == Min(Len(log[k]), appliedIdx[k])
        idxs == {i \in 1..lim : log[k][i].kind \in {"StageOwned", "Recover", "FinalCfg"}}
    IN IF idxs = {} THEN Nil
       ELSE LET e == log[k][CHOOSE i \in idxs : \A j \in idxs : i >= j]
            IN IF e.kind = "FinalCfg" THEN Nil ELSE e.stage

\* Construct log entry records concisely
InitCfgEntry ==
    [term |-> 0, kind |-> "InitCfg", lsn |-> 0, val |-> Nil,
     voters |-> GenesisVoters, joint |-> {}, learners |-> {}, rev |-> 0, stage |-> Nil]

BlankEntry(t) ==
    [term |-> t, kind |-> "Blank", lsn |-> 0, val |-> Nil,
     voters |-> {}, joint |-> {}, learners |-> {}, rev |-> 0, stage |-> Nil]

AppEntry(t, lsn, v) ==
    [term |-> t, kind |-> "App", lsn |-> lsn, val |-> v,
     voters |-> {}, joint |-> {}, learners |-> {}, rev |-> 0, stage |-> Nil]

StageOwnedEntry(t, st) ==
    [term |-> t, kind |-> "StageOwned", lsn |-> 0, val |-> Nil,
     voters |-> {}, joint |-> {}, learners |-> {}, rev |-> 0, stage |-> st]

RecoverEntry(t, st) ==
    [term |-> t, kind |-> "Recover", lsn |-> 0, val |-> Nil,
     voters |-> {}, joint |-> {}, learners |-> {}, rev |-> 0, stage |-> st]

AckRecEntry(t) ==
    [term |-> t, kind |-> "AckRec", lsn |-> 0, val |-> Nil,
     voters |-> {}, joint |-> {}, learners |-> {}, rev |-> 0, stage |-> Nil]

CfgEntry(t, kind, v1, v2, lrns, rev) ==
    [term |-> t, kind |-> kind, lsn |-> 0, val |-> Nil,
     voters |-> v1, joint |-> v2, learners |-> lrns, rev |-> rev, stage |-> Nil]

DefaultOwnership ==
    [high |-> 0, gen |-> 0,
     current |-> [gen |-> 0, rev |-> 0, stage |-> Nil, installed |-> TRUE, isRecovery |-> FALSE],
     retiredGens |-> {}]

EmptyOwnership ==
    [high |-> 0, gen |-> 0, current |-> Nil, retiredGens |-> {}]

\* Whether a term is within allowed bounds (normal or post-recovery window)
TermAllowed(t) ==
    IF ~recovered THEN t <= MaxTerm
    ELSE t <= MaxTerm \/ (t >= RecoveryGap /\ t <= RecoveryGap + (IF AllowSurvivorStopAfterRecovery THEN 2 ELSE 1))

-----------------------------------------------------------------------------
(* Initial state: genesis voters bootstrapped at index 1 with InitCfg *)

Init ==
    /\ alive         = [k \in Keepers |-> TRUE]
    /\ deadView      = [k \in Keepers |-> {}]
    /\ crashCount    = 0
    /\ registered    = [k \in Keepers |-> (k \in GenesisVoters)]
    /\ vote          = [k \in Keepers |-> InitVote]
    /\ log           = [k \in Keepers |-> IF k \in GenesisVoters THEN <<InitCfgEntry>> ELSE <<>>]
    /\ snapIdx       = [k \in Keepers |-> 0]
    /\ ownership     = [k \in Keepers |-> IF k \in GenesisVoters THEN DefaultOwnership ELSE EmptyOwnership]
    /\ groupState    = [k \in Keepers |-> IF k \in GenesisVoters THEN "Open" ELSE "Closed"]
    /\ closedCfg     = [k \in Keepers |-> IF k \in GenesisVoters THEN GenesisVoters ELSE {}]
    /\ role          = [k \in Keepers |-> "Follower"]
    /\ commitIdx     = [k \in Keepers |-> IF k \in GenesisVoters THEN 1 ELSE 0]
    /\ appliedIdx    = [k \in Keepers |-> IF k \in GenesisVoters THEN 1 ELSE 0]
    /\ lease         = [k \in Keepers |-> Nil]
    /\ excluded      = [k \in Keepers |-> Nil]
    /\ heardLeader   = [k \in Keepers |-> TRUE]
    /\ votesGranted  = [k \in Keepers |-> {}]
    /\ activeStage   = [k \in Keepers |-> Nil]
    /\ staleLearners = [k \in Keepers |-> {}]
    /\ recovered     = FALSE
    /\ recoveryAcked = FALSE
    /\ lostVoters    = {}
    /\ returnedLost  = {}
    /\ survivorId    = Nil
    /\ appendCount   = 0
    /\ leadersPerTerm = [t \in 0..(IF AllowRecovery THEN MaxTerm + RecoveryGap + 3 ELSE MaxTerm + 1) |-> {}]
    /\ committedApps = {}
    /\ lostSuffix    = {}
    /\ postRecApps   = {}
    /\ readerHistory = {}
    /\ retiredVoted  = FALSE
    /\ reused        = [k \in Keepers |-> FALSE]
    /\ certified     = [k \in Keepers |-> k \in GenesisVoters]
    /\ fenced        = [k \in Keepers |-> FALSE]
    /\ catalogStage  = Nil

Symmetry == Permutations(GenesisVoters) \cup Permutations(Keepers \ GenesisVoters)

-----------------------------------------------------------------------------
(* 1. Raft leader election with Pre-Vote and OpenRaft 0.10 leader lease *)

\* Whether voter v would grant a PreVote for candidate c at proposed term tProp
PreVoteWouldGrant(v, c, tProp) ==
    /\ alive[v]
    /\ ((registered[v] /\ ownership[v].current # Nil)
        \/ (~registered[v] /\ v \in GenesisVoters /\ ~reused[v]))
    /\ ~ExcludesSender(v, c, tProp)
    /\ IF registered[v] THEN CanVote(v) ELSE (v \in GenesisVoters)
    /\ (lease[v] = Nil \/ lease[v] = c)
    /\ VoteLeq(vote[v], [term |-> tProp, votedFor |-> c, committed |-> FALSE])
    /\ LogUpToDate(log[c], log[v])

\* Pre-vote probe triggers sender exclusion if a receiver excludes candidate c
\* (ingress.rs:464-478, network.rs:975-980)
PreVoteExcluded(c, v) ==
    /\ AllowRetire
    /\ alive[c] /\ groupState[c] = "Open" /\ role[c] # "Leader"
    /\ excluded[c] # v
    /\ alive[v] /\ v # c
    /\ groupState[v] \in {"Open", "Parked"}
    /\ LET m == EffectiveMembership(c)
           tProp == vote[c].term + 1
       IN /\ m.configured /\ c \in AllVoters(m)
          /\ v \in AllVoters(m)
          /\ ExcludesSender(v, c, tProp)
          \* PreVote unparks a parked receiver (ingress.rs:451)
          /\ groupState' = IF groupState[v] = "Parked"
                           THEN [groupState EXCEPT ![v] = "Open"]
                           ELSE groupState
          /\ vote' = IF groupState[v] = "Parked"
                     THEN [vote EXCEPT ![v] = DemoteVote(v, vote[v])]
                     ELSE vote
          /\ commitIdx' = IF groupState[v] = "Parked" THEN [commitIdx EXCEPT ![v] = snapIdx[v]] ELSE commitIdx
          /\ appliedIdx' = IF groupState[v] = "Parked" THEN [appliedIdx EXCEPT ![v] = snapIdx[v]] ELSE appliedIdx
          /\ excluded' = [excluded EXCEPT ![c] = v]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, log, snapIdx, ownership, closedCfg,
                   role, lease, heardLeader, votesGranted, activeStage, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Candidate starts an election after PreVote succeeds (or campaign_after_wake)
StartCampaign(c) ==
    /\ alive[c] /\ groupState[c] = "Open" /\ role[c] # "Leader"
    /\ ownership[c].current # Nil /\ ownership[c].current.installed
    \* network.rs: an uncertified copy sends no vote or pre-vote
    /\ certified[c]
    /\ LET m == EffectiveMembership(c)
           tNew == vote[c].term + 1
       IN /\ m.configured /\ c \in AllVoters(m)
          /\ TermAllowed(tNew)
          \* OpenRaft 0.10 pre-vote: candidate only raises term if a quorum would grant
          /\ \E Q \in SUBSET AllVoters(m) :
                /\ IsQuorum(Q, m)
                /\ c \in Q
                /\ \A v \in Q \ {c} : PreVoteWouldGrant(v, c, tNew)
          /\ vote' = [vote EXCEPT ![c] = [term |-> tNew, votedFor |-> c, committed |-> FALSE]]
          /\ role' = [role EXCEPT ![c] = "Candidate"]
          /\ votesGranted' = [votesGranted EXCEPT ![c] = {c}]
          /\ lease' = [lease EXCEPT ![c] = Nil]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, log, snapIdx, ownership,
                   groupState, closedCfg, commitIdx, appliedIdx, excluded,
                   heardLeader, activeStage, staleLearners, recovered, recoveryAcked,
                   lostVoters, returnedLost, survivorId, appendCount, leadersPerTerm,
                   committedApps, lostSuffix, postRecApps, readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Voter v handles VoteRequest from candidate c.
\* Models:
\*   - unparking on Vote (ingress.rs:451)
\*   - auto-registration on first peer message for wiped/fresh genesis voters (keeper.rs:685)
\*   - decisions::excludes_sender (ingress.rs:471)
\*   - decisions::votes (ingress.rs:527)
\*   - OpenRaft leader lease refusal
\*   - Raft vote ordering & log up-to-date check
HandleVote(v, c) ==
    /\ alive[v] /\ v # c
    /\ alive[c] /\ groupState[c] = "Open" /\ role[c] = "Candidate"
    /\ ~(v \in votesGranted[c])
    /\ vote[c].votedFor = c /\ ~vote[c].committed
    /\ LET cMem == EffectiveMembership(c)
           cTerm == vote[c].term
       IN /\ cMem.configured /\ v \in AllVoters(cMem)
          \* Step 1: group(genesis) admission (keeper.rs:669-690)
          \* Detached replica (registered /\ current = Nil) is refused ("replica is detached")
          /\ (registered[v] => ownership[v].current # Nil)
          /\ (~registered[v] => (v \in GenesisVoters /\ ~reused[v]))
          /\ LET regV == TRUE
                 ownV == IF registered[v] THEN ownership[v] ELSE DefaultOwnership
                 \* If parked, reopen and demote self-committed vote
                 wasParked == (groupState[v] = "Parked")
                 baseVote == IF wasParked THEN DemoteVote(v, vote[v]) ELSE vote[v]
                 mV == EffectiveMembership(v)
                 excl == mV.configured /\ ~(c \in AllNodes(mV)) /\ cTerm < baseVote.term
                 \* decisions::votes on opened/registered replica
                 curV == ownV.current
                 recCopy == /\ curV # Nil /\ curV.installed /\ curV.isRecovery /\ curV.stage # Nil
                            /\ (~mV.configured \/ (~mV.isJoint /\ mV.voters1 = curV.stage.old))
                 canV == /\ curV # Nil /\ curV.installed
                         /\ (recCopy \/ (IF mV.configured THEN (v \in AllVoters(mV)) ELSE (v \in GenesisVoters)))
             IN IF excl THEN
                   \* Refused with EXCLUDED without revealing v's term
                   /\ registered' = [registered EXCEPT ![v] = regV]
                   /\ ownership'  = [ownership EXCEPT ![v] = ownV]
                   /\ groupState' = [groupState EXCEPT ![v] = "Open"]
                   /\ vote'       = [vote EXCEPT ![v] = baseVote]
                   /\ commitIdx'  = IF wasParked THEN [commitIdx EXCEPT ![v] = snapIdx[v]] ELSE commitIdx
                   /\ appliedIdx' = IF wasParked THEN [appliedIdx EXCEPT ![v] = snapIdx[v]] ELSE appliedIdx
                   /\ excluded'   = [excluded EXCEPT ![c] = v]
                   /\ UNCHANGED <<role, lease, votesGranted, retiredVoted>>
                ELSE
                   /\ canV
                   /\ (lease[v] = Nil \/ lease[v] = c)
                   /\ VoteLeq(baseVote, vote[c])
                   /\ LogUpToDate(log[c], log[v])
                   /\ registered' = [registered EXCEPT ![v] = regV]
                   /\ ownership'  = [ownership EXCEPT ![v] = ownV]
                   /\ groupState' = [groupState EXCEPT ![v] = "Open"]
                   /\ vote'       = [vote EXCEPT ![v] = vote[c]]
                   /\ role'       = [role EXCEPT ![v] = "Follower"]
                   /\ lease'      = [lease EXCEPT ![v] = c]
                   /\ commitIdx'  = IF wasParked THEN [commitIdx EXCEPT ![v] = snapIdx[v]] ELSE commitIdx
                   /\ appliedIdx' = IF wasParked THEN [appliedIdx EXCEPT ![v] = snapIdx[v]] ELSE appliedIdx
                   /\ votesGranted' = [votesGranted EXCEPT ![c] = votesGranted[c] \cup {v}]
                   /\ retiredVoted' = (retiredVoted \/ (curV.gen \in ownV.retiredGens))
                   /\ UNCHANGED excluded
    /\ UNCHANGED <<alive, crashCount, deadView, log, snapIdx, closedCfg, heardLeader,
                   activeStage, staleLearners, recovered, recoveryAcked,
                   lostVoters, returnedLost, survivorId, appendCount,
                   leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory>>
    /\ UNCHANGED fenceVars

\* Candidate c wins election once a quorum of its effective membership granted votes.
\* OpenRaft commits vote and appends Blank no-op entry (or commits in new term).
BecomeLeader(c) ==
    /\ alive[c] /\ groupState[c] = "Open" /\ role[c] = "Candidate"
    /\ vote[c].votedFor = c /\ ~vote[c].committed
    /\ LET m == EffectiveMembership(c)
           t == vote[c].term
       IN /\ IsQuorum(votesGranted[c], m)
          /\ Len(log[c]) < MaxLogLen
          /\ vote' = [vote EXCEPT ![c] = [term |-> t, votedFor |-> c, committed |-> TRUE]]
          /\ role' = [role EXCEPT ![c] = "Leader"]
          /\ lease' = [lease EXCEPT ![c] = c]
          /\ log' = [log EXCEPT ![c] = Append(log[c], BlankEntry(t))]
          /\ leadersPerTerm' = [leadersPerTerm EXCEPT ![t] = @ \cup {c}]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, snapIdx, ownership,
                   groupState, closedCfg, commitIdx, appliedIdx, excluded,
                   heardLeader, votesGranted, activeStage, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Leader lease expires on follower k (allows new elections / pre-votes)
ExpireLease(k) ==
    /\ alive[k] /\ groupState[k] = "Open" /\ role[k] # "Leader"
    /\ lease[k] # Nil
    /\ (~alive[lease[k]] \/ groupState[lease[k]] # "Open" \/ role[lease[k]] # "Leader")
    /\ lease' = [lease EXCEPT ![k] = Nil]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, log, snapIdx, ownership,
                   groupState, closedCfg, role, commitIdx, appliedIdx,
                   excluded, heardLeader, votesGranted, activeStage, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* OpenRaft 0.10 quorum_loss_probe_interval: leader steps down when it cannot reach a quorum
LeaderStepDown(l) ==
    /\ alive[l] /\ groupState[l] = "Open" /\ role[l] = "Leader"
    /\ LET m == EffectiveMembership(l)
           liveVoters == {v \in AllVoters(m) : alive[v] /\ groupState[v] = "Open"}
       IN ~IsQuorum(liveVoters, m)
    /\ role' = [role EXCEPT ![l] = "Follower"]
    /\ lease' = [lease EXCEPT ![l] = Nil]
    /\ activeStage' = [activeStage EXCEPT ![l] = Nil]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, log, snapIdx, ownership,
                   groupState, closedCfg, commitIdx, appliedIdx,
                   excluded, heardLeader, votesGranted, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

-----------------------------------------------------------------------------
(* 2. Client writes, log replication, commit, and apply *)

\* Leader appends a client application record (fenced during unacknowledged recovery)
ClientAppend(l, v) ==
    /\ alive[l] /\ groupState[l] = "Open" /\ role[l] = "Leader"
    /\ appendCount < MaxAppends
    /\ Len(log[l]) < MaxLogLen
    /\ ~HasRecoveryFence(log[l], Len(log[l]))
    /\ LET nextLsn == HeadLsnIn(log[l], Len(log[l])) + 1
       IN log' = [log EXCEPT ![l] = Append(log[l], AppEntry(vote[l].term, nextLsn, v))]
    /\ appendCount' = appendCount + 1
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, snapIdx, ownership,
                   groupState, closedCfg, role, commitIdx, appliedIdx, lease,
                   excluded, heardLeader, votesGranted, activeStage, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Administrator or writer acknowledges an operator recovery (clears recovery fence)
AcknowledgeRecovery(l) ==
    /\ AllowRecovery /\ recovered /\ ~recoveryAcked
    /\ alive[l] /\ groupState[l] = "Open" /\ role[l] = "Leader"
    /\ HasRecoveryFence(log[l], appliedIdx[l])
    /\ Len(log[l]) < MaxLogLen
    /\ log' = [log EXCEPT ![l] = Append(log[l], AckRecEntry(vote[l].term))]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, snapIdx, ownership,
                   groupState, closedCfg, role, commitIdx, appliedIdx, lease,
                   excluded, heardLeader, votesGranted, activeStage, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Leader l replicates entries (or sends empty heartbeat) to follower/learner f.
\* Models:
\*   - parked follower returning Busy on empty heartbeat (ingress.rs:447)
\*   - parked follower reopening on non-empty entries (ingress.rs:451)
\*   - auto-registration for wiped genesis voter (keeper.rs:685)
\*   - decisions::excludes_sender (ingress.rs:471)
\*   - Raft log matching & truncation of conflicting uncommitted suffix
ReplicateOrHeartbeat(l, f) ==
    /\ alive[l] /\ groupState[l] = "Open" /\ role[l] = "Leader"
    /\ alive[f] /\ f # l
    /\ LET mL == EffectiveMembership(l)
       IN f \in AllNodes(mL)
    /\ (registered[f] => ownership[f].current # Nil)
    /\ (~registered[f] => (f \in GenesisVoters /\ ~reused[f]))
    /\ LET isEmpty == (log[f] = log[l])
           wasParked == (groupState[f] = "Parked")
       IN IF wasParked /\ isEmpty THEN
             \* Parked follower answers empty heartbeat Busy without opening!
             FALSE \* No state change (stuttering)
          ELSE
             LET ownF == IF registered[f] THEN ownership[f] ELSE DefaultOwnership
                 baseVote == IF wasParked THEN DemoteVote(f, vote[f]) ELSE vote[f]
                 mF == EffectiveMembership(f)
                 excl == mF.configured /\ ~(l \in AllNodes(mF)) /\ vote[l].term < baseVote.term
             IN IF excl THEN
                   /\ registered' = [registered EXCEPT ![f] = TRUE]
                   /\ ownership'  = [ownership EXCEPT ![f] = ownF]
                   /\ groupState' = [groupState EXCEPT ![f] = "Open"]
                   /\ vote'       = [vote EXCEPT ![f] = baseVote]
                   /\ commitIdx'  = IF wasParked THEN [commitIdx EXCEPT ![f] = snapIdx[f]] ELSE commitIdx
                   /\ appliedIdx' = IF wasParked THEN [appliedIdx EXCEPT ![f] = snapIdx[f]] ELSE appliedIdx
                   /\ excluded'   = [excluded EXCEPT ![l] = f]
                   /\ UNCHANGED <<log, role, lease, heardLeader, certified>>
                ELSE
                   /\ VoteLeq(baseVote, vote[l])
                   \* Avoid pure stuttering when f already matches l's vote, log, commit, and lease
                   /\ (wasParked \/ vote[f] # vote[l] \/ log[f] # log[l]
                       \/ commitIdx[f] < Min(commitIdx[l], Len(log[l]))
                       \/ ~heardLeader[f] \/ lease[f] # l)
                   /\ registered' = [registered EXCEPT ![f] = TRUE]
                   /\ groupState' = [groupState EXCEPT ![f] = "Open"]
                   /\ vote'       = [vote EXCEPT ![f] = vote[l]]
                   /\ role'       = [role EXCEPT ![f] = "Follower"]
                   /\ lease'      = [lease EXCEPT ![f] = l]
                   /\ heardLeader' = [heardLeader EXCEPT ![f] = TRUE]
                   \* keeper/certify.rs: an append its leader's vote outranks
                   \* certifies the follower's copy
                   /\ certified' = [certified EXCEPT ![f] = TRUE]
                   /\ log'        = [log EXCEPT ![f] = log[l]]
                   /\ LET newCommit == Min(commitIdx[l], Len(log[l]))
                          baseCommit == IF wasParked THEN snapIdx[f] ELSE commitIdx[f]
                          effCommit == Max(baseCommit, newCommit)
                          mApp == MembershipIn(log[l], effCommit)
                          curF == ownF.current
                          obsOwn == IF mApp.configured /\ curF # Nil /\ mApp.rev > ownF.high
                                    THEN [ownF EXCEPT !.high = mApp.rev, !.current.rev = Max(@, mApp.rev)]
                                    ELSE ownF
                      IN /\ commitIdx' = [commitIdx EXCEPT ![f] = effCommit]
                         /\ appliedIdx' = [appliedIdx EXCEPT ![f] = effCommit]
                         /\ ownership' = [ownership EXCEPT ![f] = obsOwn]
                   /\ UNCHANGED excluded
    /\ UNCHANGED <<alive, crashCount, deadView, snapIdx, closedCfg, votesGranted, activeStage,
                   staleLearners, recovered, recoveryAcked, lostVoters, returnedLost,
                   survivorId, appendCount, leadersPerTerm, committedApps, lostSuffix,
                   postRecApps, readerHistory, retiredVoted>>
    /\ UNCHANGED <<reused, fenced, catalogStage>>

\* A leader or candidate l sends f any frame that carries its vote (append,
\* snapshot chunk, vote, pre-vote, hand-off or park) and f answers with its
\* own, newer vote, so l adopts f's term and becomes a follower. A frame
\* that f excludes (decisions::excludes_sender) gets no Raft answer and
\* teaches l nothing. Before the snapshot fix, keeper/ingress.rs checked only
\* appends, votes and pre-votes, so a lost leader's snapshot chunk taught it
\* the recovery term (recovery::the_survivor_refuses_a_lost_voters_snapshot_
\* without_its_term); with every vote-carrying frame checked, this one
\* action stands for all of them.
LearnHigherTerm(l, f) ==
    /\ alive[l] /\ groupState[l] = "Open" /\ role[l] \in {"Leader", "Candidate"}
    /\ alive[f] /\ f # l /\ groupState[f] = "Open"
    /\ registered[f] /\ ownership[f].current # Nil
    /\ vote[f].term > vote[l].term
    /\ ~ExcludesSender(f, l, vote[l].term)
    /\ vote' = [vote EXCEPT ![l] = [term |-> vote[f].term, votedFor |-> Nil, committed |-> FALSE]]
    /\ role' = [role EXCEPT ![l] = "Follower"]
    /\ lease' = [lease EXCEPT ![l] = Nil]
    /\ activeStage' = [activeStage EXCEPT ![l] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![l] = {}]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, log, snapIdx, ownership,
                   groupState, closedCfg, commitIdx, appliedIdx, excluded,
                   heardLeader, staleLearners, recovered, recoveryAcked,
                   lostVoters, returnedLost, survivorId, appendCount, leadersPerTerm,
                   committedApps, lostSuffix, postRecApps, readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Leader advances commitIdx when a quorum of its effective membership holds entry i
\* from its current term (Raft commit rule + joint consensus quorum).
AdvanceCommit(l) ==
    /\ alive[l] /\ groupState[l] = "Open" /\ role[l] = "Leader"
    /\ LET m == EffectiveMembership(l)
           t == vote[l].term
       IN \E i \in (commitIdx[l] + 1)..Len(log[l]) :
            /\ log[l][i].term = t
            /\ LET holders == {k \in AllVoters(m) :
                    \/ k = l
                    \/ (Len(log[k]) >= i /\ log[k][i] = log[l][i])}
               IN IsQuorum(holders, m)
            /\ commitIdx' = [commitIdx EXCEPT ![l] = i]
            /\ appliedIdx' = [appliedIdx EXCEPT ![l] = i]
            /\ LET mApp == MembershipIn(log[l], i)
                   curL == ownership[l].current
                   obsOwn == IF mApp.configured /\ curL # Nil /\ mApp.rev > ownership[l].high
                             THEN [ownership[l] EXCEPT !.high = mApp.rev, !.current.rev = Max(@, mApp.rev)]
                             ELSE ownership[l]
               IN ownership' = [ownership EXCEPT ![l] = obsOwn]
            /\ LET newApps == AppEntriesIn(log[l], i)
                   newAppsT == AppEntriesWithTermIn(log[l], i)
                   \* Distinguish pre-recovery vs post-recovery commits
                   isPostRec == recovered /\ (\E r \in 1..i : log[l][r].kind = "Recover")
                   hasAck == \E a \in 1..i : log[l][a].kind = "AckRec"
                   prePairs == {[lsn |-> e.lsn, val |-> e.val] : e \in committedApps}
                   IN /\ IF ~recovered THEN
                            /\ committedApps' = committedApps \cup newAppsT
                            /\ UNCHANGED <<postRecApps, lostSuffix>>
                         ELSE IF isPostRec THEN
                            /\ postRecApps' = postRecApps \cup {x \in newAppsT : ~([lsn |-> x.lsn, val |-> x.val] \in prePairs)}
                            /\ UNCHANGED <<committedApps, lostSuffix>>
                         ELSE
                            /\ lostSuffix' = lostSuffix \cup {x \in newAppsT : ~([lsn |-> x.lsn, val |-> x.val] \in prePairs)}
                            /\ UNCHANGED <<committedApps, postRecApps>>
                      /\ recoveryAcked' = (recoveryAcked \/ (isPostRec /\ hasAck))
    /\ UNCHANGED <<alive, deadView, crashCount, registered, vote, log, snapIdx,
                   groupState, closedCfg, role, lease, excluded,
                   heardLeader, votesGranted, activeStage, staleLearners,
                   recovered, lostVoters, returnedLost, survivorId, appendCount,
                   leadersPerTerm, readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Replica applies committed entries and updates Ownership::Observe high-water mark
\* (storage/snapshot.rs:686-706)
ApplyEntries(k) ==
    /\ alive[k] /\ groupState[k] = "Open"
    /\ appliedIdx[k] < commitIdx[k]
    /\ LET newApp == commitIdx[k]
           m == MembershipIn(log[k], newApp)
           cur == ownership[k].current
           newOwn == IF m.configured /\ cur # Nil /\ m.rev > ownership[k].high
                     THEN [ownership[k] EXCEPT !.high = m.rev,
                                               !.current.rev = Max(@, m.rev)]
                     ELSE ownership[k]
       IN /\ appliedIdx' = [appliedIdx EXCEPT ![k] = newApp]
          /\ ownership' = [ownership EXCEPT ![k] = newOwn]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, log, snapIdx,
                   groupState, closedCfg, role, commitIdx, lease, excluded,
                   heardLeader, votesGranted, activeStage, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Replica takes a local snapshot of its applied state (persists applied state across restart)
TakeSnapshot(k) ==
    /\ AllowSnapshot
    /\ alive[k] /\ groupState[k] = "Open"
    /\ appliedIdx[k] > snapIdx[k]
    /\ snapIdx' = [snapIdx EXCEPT ![k] = appliedIdx[k]]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, log, ownership,
                   groupState, closedCfg, role, commitIdx, appliedIdx, lease,
                   excluded, heardLeader, votesGranted, activeStage, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

-----------------------------------------------------------------------------
(* 3. Parking, unparking, keeper liveness, and wake sweep (park.rs, liveness.rs) *)

\* Leader parks an idle, settled, non-joint stream, skipping followers in deadView[l]
\* (park.rs:58-134). Followers already parked accept idempotently (ingress.rs:450).
ParkStream(l) ==
    /\ AllowPark
    /\ alive[l] /\ groupState[l] = "Open" /\ role[l] = "Leader"
    /\ appliedIdx[l] = Len(log[l]) /\ commitIdx[l] = Len(log[l])
    /\ LET m == EffectiveMembership(l)
       IN /\ m.configured /\ ~m.isJoint
          /\ LET followers == m.voters1 \ {l}
                 liveFollowers == {f \in followers : ~(f \in deadView[l])}
             IN /\ \A f \in liveFollowers :
                     /\ alive[f]
                     /\ \/ groupState[f] = "Parked"
                        \/ ( /\ groupState[f] = "Open"
                             /\ role[f] = "Follower"
                             /\ MatchingParkCut(vote[f], vote[l], appliedIdx[f], Len(log[l]))
                             /\ log[f] = log[l] )
                /\ LET toPark == liveFollowers \cup {l}
                   IN /\ groupState' = [k \in Keepers |-> IF k \in toPark THEN "Parked" ELSE groupState[k]]
                      /\ closedCfg'  = [k \in Keepers |-> IF k \in toPark THEN m.voters1 ELSE closedCfg[k]]
                      /\ role'       = [k \in Keepers |-> IF k \in toPark THEN "Follower" ELSE role[k]]
                      /\ lease'      = [k \in Keepers |-> IF k \in toPark THEN Nil ELSE lease[k]]
                      /\ commitIdx'  = [k \in Keepers |-> IF k \in toPark THEN snapIdx[k] ELSE commitIdx[k]]
                      /\ appliedIdx' = [k \in Keepers |-> IF k \in toPark THEN snapIdx[k] ELSE appliedIdx[k]]
                      /\ activeStage' = [activeStage EXCEPT ![l] = Nil]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, log, snapIdx, ownership,
                   excluded, heardLeader, votesGranted, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Holder-driven wake sweep (liveness.rs:158-245):
\* Reopens a parked copy whose finalized config names exactly 1 dead keeper.
WakeForDead(k) ==
    /\ AllowPark
    /\ alive[k] /\ groupState[k] = "Parked"
    /\ Cardinality({v \in closedCfg[k] : v \in deadView[k]}) = 1
    /\ groupState' = [groupState EXCEPT ![k] = "Open"]
    /\ vote'       = [vote EXCEPT ![k] = DemoteVote(k, vote[k])]
    /\ commitIdx'  = [commitIdx EXCEPT ![k] = snapIdx[k]]
    /\ appliedIdx' = [appliedIdx EXCEPT ![k] = snapIdx[k]]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, log, snapIdx, ownership, closedCfg,
                   role, lease, excluded, heardLeader, votesGranted, activeStage,
                   staleLearners, recovered, recoveryAcked, lostVoters, returnedLost,
                   survivorId, appendCount, leadersPerTerm, committedApps, lostSuffix,
                   postRecApps, readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Client request arrives at a parked replica and reopens it (keeper.rs:933)
ClientUnpark(k) ==
    /\ AllowPark
    /\ alive[k] /\ groupState[k] = "Parked"
    /\ groupState' = [groupState EXCEPT ![k] = "Open"]
    /\ vote'       = [vote EXCEPT ![k] = DemoteVote(k, vote[k])]
    /\ commitIdx'  = [commitIdx EXCEPT ![k] = snapIdx[k]]
    /\ appliedIdx' = [appliedIdx EXCEPT ![k] = snapIdx[k]]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, log, snapIdx, ownership, closedCfg,
                   role, lease, excluded, heardLeader, votesGranted, activeStage,
                   staleLearners, recovered, recoveryAcked, lostVoters, returnedLost,
                   survivorId, appendCount, leadersPerTerm, committedApps, lostSuffix,
                   postRecApps, readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Liveness ping table updates (liveness.rs:124-151)
DetectDead(k, j) ==
    /\ (AllowReplace \/ AllowPark)
    /\ alive[k] /\ registered[k] /\ ~alive[j] /\ j # k /\ ~(j \in deadView[k])
    /\ deadView' = [deadView EXCEPT ![k] = @ \cup {j}]
    /\ UNCHANGED <<alive, crashCount, registered, vote, log, snapIdx, ownership,
                   groupState, closedCfg, role, commitIdx, appliedIdx, lease,
                   excluded, heardLeader, votesGranted, activeStage, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

DetectAlive(k, j) ==
    /\ (AllowReplace \/ AllowPark)
    /\ alive[k] /\ alive[j] /\ j \in deadView[k]
    /\ deadView' = [deadView EXCEPT ![k] = @ \ {j}]
    /\ UNCHANGED <<alive, crashCount, registered, vote, log, snapIdx, ownership,
                   groupState, closedCfg, role, commitIdx, appliedIdx, lease,
                   excluded, heardLeader, votesGranted, activeStage, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

-----------------------------------------------------------------------------
(* 4. Leader-driven repair, staged joint replacement, stale learners, retirement *)

\* Leader commits StageOwned(stage) for replacing deadV with repl (replacement.rs:72-77)
ProposeStageOwned(l, deadV, repl) ==
    /\ AllowReplace
    /\ alive[l] /\ groupState[l] = "Open" /\ role[l] = "Leader"
    /\ ~HasPendingMgmt(l)
    /\ appliedIdx[l] = commitIdx[l]
    /\ Len(log[l]) < MaxLogLen
    /\ LET m == AppliedMembership(l)
       IN /\ m.configured /\ ~m.isJoint
          /\ deadV \in m.voters1 /\ deadV # l
          /\ deadV \in deadView[l]
          /\ Cardinality({v \in m.voters1 : v = l \/ ~(v \in deadView[l])}) >= 2
          /\ repl \in Keepers \ m.voters1
          /\ alive[repl] /\ ~(repl \in deadView[l])
          /\ LET st == [source |-> m.rev, old |-> m.voters1, target |-> (m.voters1 \ {deadV}) \cup {repl}]
             IN /\ AppliedStage(l) # st
                /\ log' = [log EXCEPT ![l] = Append(log[l], StageOwnedEntry(vote[l].term, st))]
                /\ activeStage' = [activeStage EXCEPT ![l] = st]
                \* replacement.rs: the catalog records the stage before StageOwned
                /\ catalogStage' = [stage |-> st, recovery |-> FALSE]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, snapIdx, ownership,
                   groupState, closedCfg, role, commitIdx, appliedIdx, lease,
                   excluded, heardLeader, votesGranted, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED <<reused, certified, fenced>>

\* Replacement executes StageReplica on target repl and adds repl as learner (replacement.rs:85-115,
\* replicas.rs:81-110, ownership.rs:129-148).
\* ownership.rs Change::Stage: revision = stage.source + 1 <= high is refused
\* (stale), except decisions::restages_replacement: a copy that another
\* ordinary move from the same source and configuration staged is restaged
\* into a new generation. The authority's committed proof names this stage at
\* that source with no joint configuration, so the other move's joint
\* configuration can never commit. The durable vote is the stream's, not the
\* generation's (storage/wal.rs Record::Ownership), so the restage keeps it.
StageReplicaAndAddLearner(l, repl) ==
    /\ AllowReplace
    /\ alive[l] /\ groupState[l] = "Open" /\ role[l] = "Leader"
    /\ ~HasPendingMgmt(l)
    /\ alive[repl]
    /\ LET m == AppliedMembership(l)
           st == AppliedStage(l)
       IN /\ m.configured /\ ~m.isJoint /\ st # Nil
          /\ activeStage[l] = st
          /\ st.source = m.rev /\ st.old = m.voters1
          /\ repl \in st.target \ st.old
          /\ LET own == ownership[repl]
                 sameStage == (own.current # Nil /\ own.current.stage = st)
                 newRev == st.source + 1
                 restage == /\ own.current # Nil
                            /\ own.current.stage # Nil
                            /\ ~own.current.isRecovery
                            /\ own.current.stage.source = st.source
                            /\ own.current.stage.old = st.old
                            /\ newRev = own.high
                 allowed == sameStage \/ newRev > own.high \/ restage
                 newGen == IF sameStage THEN own.gen ELSE own.gen + 1
                 newOwn == IF sameStage THEN own
                           ELSE [high |-> newRev,
                                 gen |-> newGen,
                                 current |-> [gen |-> newGen, rev |-> newRev,
                                              stage |-> st, installed |-> FALSE,
                                              isRecovery |-> FALSE],
                                 retiredGens |-> IF own.current # Nil
                                                 THEN own.retiredGens \cup {own.current.gen}
                                                 ELSE own.retiredGens]
             IN /\ allowed
                /\ registered' = [registered EXCEPT ![repl] = TRUE]
                /\ ownership'  = [ownership EXCEPT ![repl] = newOwn]
                /\ log' = IF ~(repl \in m.learners) /\ Len(log[l]) < MaxLogLen
                          THEN [log EXCEPT ![repl] = IF sameStage THEN log[repl] ELSE <<>>,
                                           ![l] = Append(log[l], CfgEntry(vote[l].term, "InitCfg",
                                                   m.voters1, {}, m.learners \cup {repl}, m.rev))]
                          ELSE [log EXCEPT ![repl] = IF sameStage THEN log[repl] ELSE <<>>]
                /\ snapIdx' = IF sameStage THEN snapIdx ELSE [snapIdx EXCEPT ![repl] = 0]
                /\ groupState' = IF sameStage THEN groupState ELSE [groupState EXCEPT ![repl] = "Open"]
                /\ commitIdx'  = IF sameStage THEN commitIdx ELSE [commitIdx EXCEPT ![repl] = 0]
                /\ appliedIdx' = IF sameStage THEN appliedIdx ELSE [appliedIdx EXCEPT ![repl] = 0]
                /\ role'       = IF sameStage THEN role ELSE [role EXCEPT ![repl] = "Follower"]
                /\ activeStage' = [activeStage EXCEPT ![l] = st]
                \* A new generation is a new copy: it is certified afresh.
                /\ certified' = IF sameStage THEN certified ELSE [certified EXCEPT ![repl] = FALSE]
                /\ fenced'    = IF sameStage THEN fenced ELSE [fenced EXCEPT ![repl] = FALSE]
    /\ UNCHANGED <<alive, crashCount, deadView, vote, closedCfg, lease, excluded, heardLeader,
                   votesGranted, staleLearners, recovered, recoveryAcked,
                   lostVoters, returnedLost, survivorId, appendCount, leadersPerTerm,
                   committedApps, lostSuffix, postRecApps, readerHistory, retiredVoted>>
    /\ UNCHANGED <<reused, catalogStage>>

\* Replacement aborts after StageReplica (e.g., deadline expires before InstallReplica/joint)
AbortReplacement(l) ==
    /\ AllowReplace /\ AllowAbortedReplace
    /\ alive[l] /\ groupState[l] = "Open" /\ role[l] = "Leader"
    /\ activeStage[l] # Nil
    /\ activeStage' = [activeStage EXCEPT ![l] = Nil]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, log, snapIdx, ownership,
                   groupState, closedCfg, role, commitIdx, appliedIdx, lease,
                   excluded, heardLeader, votesGranted, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Leader sends InstallReplica once learner repl has matched log[l], then proposes JointCfg
\* (replacement.rs:136-167, replicas.rs:170-204)
InstallAndProposeJoint(l, repl) ==
    /\ AllowReplace
    /\ alive[l] /\ groupState[l] = "Open" /\ role[l] = "Leader"
    /\ ~HasPendingMgmt(l)
    /\ alive[repl] /\ groupState[repl] = "Open"
    /\ Len(log[l]) < MaxLogLen
    /\ LET m == AppliedMembership(l)
           st == AppliedStage(l)
           cur == ownership[repl].current
       IN /\ m.configured /\ ~m.isJoint /\ st # Nil
          /\ activeStage[l] = st
          /\ repl \in st.target \ st.old
          /\ repl \in m.learners
          /\ cur # Nil /\ cur.stage = st
          /\ log[repl] = log[l]
          /\ ownership' = [ownership EXCEPT ![repl].current.installed = TRUE]
          /\ log' = [log EXCEPT ![l] = Append(log[l],
                       CfgEntry(vote[l].term, "JointCfg", m.voters1, st.target, m.learners \ {repl}, m.rev))]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, snapIdx, groupState, closedCfg,
                   role, commitIdx, appliedIdx, lease, excluded, heardLeader,
                   votesGranted, activeStage, staleLearners, recovered, recoveryAcked,
                   lostVoters, returnedLost, survivorId, appendCount, leadersPerTerm,
                   committedApps, lostSuffix, postRecApps, readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Leader finalizes a committed joint configuration (Work::Joint / replacement.rs:167,262)
ProposeFinalize(l) ==
    /\ AllowReplace
    /\ alive[l] /\ groupState[l] = "Open" /\ role[l] = "Leader"
    /\ ~HasPendingMgmt(l)
    /\ Len(log[l]) < MaxLogLen
    /\ LET m == AppliedMembership(l)
       IN /\ m.configured /\ m.isJoint
          /\ log' = [log EXCEPT ![l] = Append(log[l],
                       CfgEntry(vote[l].term, "FinalCfg", m.voters2, {}, m.learners, m.rev + 1))]
          /\ activeStage' = [activeStage EXCEPT ![l] = Nil]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, snapIdx, ownership,
                   groupState, closedCfg, role, commitIdx, appliedIdx, lease,
                   excluded, heardLeader, votesGranted, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Stale learner removal (repair.rs:215-229, 354-374):
\* Leader removes a learner left by an aborted replacement (activeStage[l] = Nil).
RemoveStaleLearner(l, lrn) ==
    /\ AllowReplace /\ AllowStaleLearner
    /\ alive[l] /\ groupState[l] = "Open" /\ role[l] = "Leader"
    /\ ~HasPendingMgmt(l)
    /\ activeStage[l] = Nil
    /\ Len(log[l]) < MaxLogLen
    /\ LET m == AppliedMembership(l)
       IN /\ m.configured /\ ~m.isJoint
          /\ lrn \in m.learners
          /\ log' = [log EXCEPT ![l] = Append(log[l],
                       CfgEntry(vote[l].term, "InitCfg", m.voters1, {}, m.learners \ {lrn}, m.rev))]
          /\ staleLearners' = [staleLearners EXCEPT ![l] = @ \ {lrn}]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, snapIdx, ownership,
                   groupState, closedCfg, role, commitIdx, appliedIdx, lease,
                   excluded, heardLeader, votesGranted, activeStage,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Follower's heard-from-leader timer expires (>= repair_after) when no live leader
\* of k's membership is heartbeating k.
HeardTimeout(k) ==
    /\ AllowRetire
    /\ alive[k] /\ groupState[k] = "Open" /\ role[k] # "Leader"
    /\ heardLeader[k]
    /\ ~(\E l \in Keepers :
            alive[l] /\ groupState[l] = "Open" /\ role[l] = "Leader"
            /\ k \in AllVoters(EffectiveMembership(l)))
    /\ heardLeader' = [heardLeader EXCEPT ![k] = FALSE]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, log, snapIdx, ownership,
                   groupState, closedCfg, role, commitIdx, appliedIdx, lease,
                   excluded, votesGranted, activeStage, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Self-retirement on certified placement proof (repair.rs:565-623, replicas.rs:206-247,
\* ownership.rs:164-182).
\* Note: auth must be a live Leader so its ReadIndex barrier for PlacementProof succeeds.
RetireRemoved(k, auth) ==
    /\ AllowRetire
    /\ alive[k] /\ groupState[k] = "Open"
    /\ ownership[k].current # Nil
    \* repair.rs retire_removed: excluded by a peer, silent past the repair
    \* delay, or fenced by the catalog (keeper/certify.rs)
    /\ (excluded[k] # Nil \/ fenced[k] \/ (role[k] # "Leader" /\ ~heardLeader[k]))
    /\ alive[auth] /\ auth # k /\ groupState[auth] = "Open" /\ role[auth] = "Leader"
    \* If excluded[k] is itself a live leader, it is asked first (repair.rs:592)
    /\ (excluded[k] # Nil /\ alive[excluded[k]] /\ groupState[excluded[k]] = "Open"
        /\ role[excluded[k]] = "Leader") => (auth = excluded[k])
    /\ LET proof == AppliedMembership(auth)
           cur == ownership[k].current
       IN /\ proof.configured
          /\ IF k \in AllVoters(proof) THEN
                \* Authority still names k: clear excluded flag (repair.rs:605-607)
                /\ excluded' = [excluded EXCEPT ![k] = Nil]
                /\ fenced' = [fenced EXCEPT ![k] = FALSE]
                /\ UNCHANGED <<ownership, log, snapIdx, groupState, role, commitIdx, appliedIdx, lease,
                               certified>>
             ELSE
                \* ownership.rs:171-182 Change::Detach check:
                /\ proof.rev >= ownership[k].high
                /\ cur.installed
                /\ proof.rev >= cur.rev
                /\ ownership' = [ownership EXCEPT ![k] = [
                        high |-> proof.rev,
                        gen |-> @.gen,
                        current |-> Nil,
                        retiredGens |-> @.retiredGens \cup {cur.gen}]]
                \* wal.rs:222-227: detach clears log & snapshot but keeps durable vote!
                /\ log' = [log EXCEPT ![k] = <<>>]
                /\ snapIdx' = [snapIdx EXCEPT ![k] = 0]
                /\ groupState' = [groupState EXCEPT ![k] = "Closed"]
                /\ role' = [role EXCEPT ![k] = "Follower"]
                /\ commitIdx' = [commitIdx EXCEPT ![k] = 0]
                /\ appliedIdx' = [appliedIdx EXCEPT ![k] = 0]
                /\ lease' = [lease EXCEPT ![k] = Nil]
                /\ excluded' = [excluded EXCEPT ![k] = Nil]
                /\ certified' = [certified EXCEPT ![k] = FALSE]
                /\ fenced' = [fenced EXCEPT ![k] = FALSE]
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, closedCfg, heardLeader,
                   votesGranted, activeStage, staleLearners, recovered, recoveryAcked,
                   lostVoters, returnedLost, survivorId, appendCount, leadersPerTerm,
                   committedApps, lostSuffix, postRecApps, readerHistory, retiredVoted>>
    /\ UNCHANGED <<reused, catalogStage>>

-----------------------------------------------------------------------------
(* 5. Stop, restart, and wipe-and-reinitialize under same ID *)

StopKeeper(k) ==
    /\ AllowStop
    /\ alive[k]
    /\ crashCount < MaxCrashes
    /\ Cardinality({j \in Keepers : ~alive[j]}) < MaxStopped
    /\ (recovered /\ k = survivorId) => AllowSurvivorStopAfterRecovery
    /\ alive' = [alive EXCEPT ![k] = FALSE]
    /\ crashCount' = crashCount + 1
    /\ deadView' = [deadView EXCEPT ![k] = {}]
    /\ groupState' = [groupState EXCEPT ![k] = "Closed"]
    /\ role' = [role EXCEPT ![k] = "Follower"]
    /\ commitIdx' = [commitIdx EXCEPT ![k] = 0]
    /\ appliedIdx' = [appliedIdx EXCEPT ![k] = 0]
    /\ lease' = [lease EXCEPT ![k] = Nil]
    /\ excluded' = [excluded EXCEPT ![k] = Nil]
    /\ heardLeader' = [heardLeader EXCEPT ![k] = TRUE]
    /\ votesGranted' = [votesGranted EXCEPT ![k] = {}]
    /\ activeStage' = [activeStage EXCEPT ![k] = Nil]
    /\ staleLearners' = [staleLearners EXCEPT ![k] = {}]
    \* Certification is in memory: a restarted copy is certified afresh.
    /\ certified' = [certified EXCEPT ![k] = FALSE]
    /\ fenced' = [fenced EXCEPT ![k] = FALSE]
    /\ UNCHANGED <<registered, vote, log, snapIdx, ownership, closedCfg,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED <<reused, catalogStage>>

\* Restart keeper k: opens registered non-detached stream with vote demotion
\* (keeper.rs:437-445, storage/mod.rs:125-145).
RestartKeeper(k) ==
    /\ ~alive[k]
    \* In PreRecovery scenarios, lost voters stay stopped until recovery runs
    /\ (AllowRecovery /\ ~recovered) => FALSE
    \* Bound returning lost voters after recovery according to MaxReturningLost
    /\ (recovered /\ k \in lostVoters) =>
         (k \in returnedLost \/ Cardinality(returnedLost) < MaxReturningLost)
    /\ alive' = [alive EXCEPT ![k] = TRUE]
    /\ LET opens == registered[k] /\ ownership[k].current # Nil
       IN /\ groupState' = [groupState EXCEPT ![k] = IF opens THEN "Open" ELSE "Closed"]
          /\ vote'       = [vote EXCEPT ![k] = IF opens THEN DemoteVote(k, vote[k]) ELSE vote[k]]
          /\ commitIdx'  = [commitIdx EXCEPT ![k] = IF opens THEN snapIdx[k] ELSE 0]
          /\ appliedIdx' = [appliedIdx EXCEPT ![k] = IF opens THEN snapIdx[k] ELSE 0]
          /\ returnedLost' = IF recovered /\ k \in lostVoters
                             THEN returnedLost \cup {k}
                             ELSE returnedLost
    /\ UNCHANGED <<deadView, crashCount, registered, log, snapIdx, ownership, closedCfg, role,
                   lease, excluded, heardLeader, votesGranted, activeStage,
                   staleLearners, recovered, recoveryAcked, lostVoters, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED fenceVars

\* Keeper k loses both its data and registry volumes and is re-initialized under
\* its old ID k. It rejoins with empty disk state (vote=0, log=<<>>, unregistered).
\* Before 6d75fec it registered an empty voter on its first peer RPC because
\* k \in GenesisVoters (the amnesia bug, CE-1). Since 6d75fec its peers report
\* that they first saw it under another media incarnation, it marks itself
\* reused, and decisions::registers refuses every registration from peer
\* traffic: it takes replicas only through staging (keeper/incarnation.rs).
WipeAndReinit(k) ==
    /\ AllowWipe
    /\ ~alive[k]
    /\ alive' = [alive EXCEPT ![k] = TRUE]
    /\ registered' = [registered EXCEPT ![k] = FALSE]
    /\ vote' = [vote EXCEPT ![k] = InitVote]
    /\ log' = [log EXCEPT ![k] = <<>>]
    /\ snapIdx' = [snapIdx EXCEPT ![k] = 0]
    /\ ownership' = [ownership EXCEPT ![k] = EmptyOwnership]
    /\ groupState' = [groupState EXCEPT ![k] = "Closed"]
    /\ closedCfg' = [closedCfg EXCEPT ![k] = {}]
    /\ reused' = [reused EXCEPT ![k] = TRUE]
    /\ certified' = [certified EXCEPT ![k] = FALSE]
    /\ fenced' = [fenced EXCEPT ![k] = FALSE]
    /\ UNCHANGED <<deadView, crashCount, role, commitIdx, appliedIdx, lease, excluded,
                   heardLeader, votesGranted, activeStage, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED catalogStage

-----------------------------------------------------------------------------
(* 6. Offline operator recovery (recovery.rs, decisions.rs, replicas.rs) *)

OperatorRecover(surv, r1, r2) ==
    /\ AllowRecovery /\ ~recovered
    /\ ~alive[surv]                         \* runs on stopped survivor under media lock
    /\ registered[surv]
    /\ ownership[surv].current # Nil /\ ownership[surv].current.installed
    /\ Len(log[surv]) + 2 <= MaxLogLen
    /\ LET m == EffectiveMembership(surv)   \* replays survivor's whole local log
       IN /\ m.configured /\ ~m.isJoint
          /\ surv \in m.voters1
          /\ LET others == m.voters1 \ {surv}
                 \* decisions::allows_recovery: 0 other voters answer healthy
                 healthyOthers == {v \in others : alive[v] /\ registered[v] /\ ownership[v].current # Nil}
             IN /\ healthyOthers = {}
                /\ r1 \in Keepers \ m.voters1
                /\ r2 \in Keepers \ m.voters1
                /\ r1 # r2
                /\ alive[r1] /\ alive[r2]
                /\ LET target == {surv, r1, r2}
                       st == [source |-> m.rev, old |-> m.voters1, target |-> target]
                       newRev == m.rev + 1
                       tRec == Max(vote[surv].term, LastLogTerm(log[surv])) + RecoveryGap
                       \* replicas.rs:144-160 StageRecovered check on r1, r2
                       canStage(r) ==
                           /\ ~(groupState[r] = "Open" /\ r \in AllVoters(EffectiveMembership(r)))
                           /\ ((ownership[r].current # Nil /\ ownership[r].current.stage = st)
                               \/ newRev > ownership[r].high)
                       stageOwn(r) ==
                           LET own == ownership[r]
                               same == own.current # Nil /\ own.current.stage = st
                               g == IF same THEN own.gen ELSE own.gen + 1
                           IN IF same
                              THEN [own EXCEPT !.current.installed = TRUE, !.current.isRecovery = TRUE]
                              ELSE [high |-> newRev, gen |-> g,
                                    current |-> [gen |-> g, rev |-> newRev, stage |-> st,
                                                 installed |-> TRUE, isRecovery |-> TRUE],
                                    retiredGens |-> IF own.current # Nil
                                                    THEN own.retiredGens \cup {own.current.gen}
                                                    ELSE own.retiredGens]
                       survApps == AppEntriesIn(log[surv], Len(log[surv]))
                   IN /\ canStage(r1) /\ canStage(r2)
                      \* Atomic Record::Recover on survivor + StageRecovered on r1, r2
                      /\ registered' = [registered EXCEPT ![r1] = TRUE, ![r2] = TRUE]
                      /\ ownership'  = [ownership EXCEPT ![r1] = stageOwn(r1), ![r2] = stageOwn(r2)]
                      /\ vote'       = [vote EXCEPT ![surv] = [term |-> tRec, votedFor |-> surv, committed |-> TRUE]]
                      /\ log'        = [log EXCEPT
                            ![surv] = Append(Append(log[surv], RecoverEntry(tRec, st)),
                                             CfgEntry(tRec, "FinalCfg", target, {}, {}, newRev)),
                            ![r1]   = <<>>,
                            ![r2]   = <<>>]
                      /\ snapIdx'    = [snapIdx EXCEPT ![r1] = 0, ![r2] = 0]
                      /\ groupState' = [groupState EXCEPT ![r1] = "Closed", ![r2] = "Closed"]
                      /\ commitIdx'  = [commitIdx EXCEPT ![r1] = 0, ![r2] = 0]
                      /\ appliedIdx' = [appliedIdx EXCEPT ![r1] = 0, ![r2] = 0]
                      /\ recovered'  = TRUE
                      \* recovery.rs: the catalog must record the recovery stage
                      \* before the survivor's durable round, or the command refuses
                      /\ catalogStage' = [stage |-> st, recovery |-> TRUE]
                      /\ certified'  = [certified EXCEPT ![r1] = FALSE, ![r2] = FALSE]
                      /\ fenced'     = [fenced EXCEPT ![r1] = FALSE, ![r2] = FALSE]
                      /\ lostVoters' = others
                      /\ survivorId' = surv
                      \* Explicitly separate acknowledged lost suffix from survivor's preserved history
                      /\ lostSuffix'    = {e \in committedApps :
                                             ~([lsn |-> e.lsn, val |-> e.val] \in survApps)}
                      /\ committedApps' = {e \in committedApps :
                                             [lsn |-> e.lsn, val |-> e.val] \in survApps}
    /\ UNCHANGED <<alive, crashCount, deadView, closedCfg, role, lease, excluded, heardLeader,
                   votesGranted, activeStage, staleLearners, recoveryAcked,
                   returnedLost, appendCount, leadersPerTerm, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED reused

-----------------------------------------------------------------------------
(* 6b. Placement certification against the catalog (keeper/certify.rs) *)

\* An uncertified open copy asks the catalog for the stream's latest staged
\* move before it campaigns or serves reads. A copy the move fences is marked
\* for retirement; any other copy is certified until it closes.
CatalogCheck(k) ==
    /\ alive[k] /\ groupState[k] = "Open"
    /\ ownership[k].current # Nil /\ ownership[k].current.installed
    /\ ~certified[k] /\ ~fenced[k]
    /\ IF FencedByCatalog(k)
       THEN /\ fenced' = [fenced EXCEPT ![k] = TRUE]
            /\ UNCHANGED certified
       ELSE /\ certified' = [certified EXCEPT ![k] = TRUE]
            /\ UNCHANGED fenced
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, log, snapIdx, ownership,
                   groupState, closedCfg, role, commitIdx, appliedIdx, lease,
                   excluded, heardLeader, votesGranted, activeStage, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   readerHistory, retiredVoted>>
    /\ UNCHANGED <<reused, catalogStage>>

-----------------------------------------------------------------------------
(* 7. Client ReadAt observation (keeper.rs:955-983, client/reading.rs) *)

\* A reader calls ReadAt on any live keeper k with an open group where
\* serves_applied_pages(k) holds: k is a voter in its applied membership and
\* its copy is certified (decisions::serves_reads, the CE-3 fix). ReadAt still
\* needs no quorum or leader barrier.
ClientRead(k) ==
    /\ AllowClientReads /\ recovered
    /\ alive[k] /\ groupState[k] = "Open"
    /\ ownership[k].current # Nil /\ ownership[k].current.installed
    /\ certified[k]
    /\ LET m == AppliedMembership(k)
           appsT == AppEntriesWithTermIn(log[k], appliedIdx[k])
           relevant == appsT \cap (lostSuffix \cup postRecApps)
       IN /\ m.configured /\ k \in AllVoters(m)
          /\ relevant \ readerHistory # {}
          /\ readerHistory' = readerHistory \cup relevant
    /\ UNCHANGED <<alive, crashCount, deadView, registered, vote, log, snapIdx, ownership,
                   groupState, closedCfg, role, commitIdx, appliedIdx, lease,
                   excluded, heardLeader, votesGranted, activeStage, staleLearners,
                   recovered, recoveryAcked, lostVoters, returnedLost, survivorId,
                   appendCount, leadersPerTerm, committedApps, lostSuffix, postRecApps,
                   retiredVoted>>
    /\ UNCHANGED fenceVars

-----------------------------------------------------------------------------
(* Next-state relation *)

Next ==
    \/ \E c, v \in Keepers : PreVoteExcluded(c, v)
    \/ \E c \in Keepers : StartCampaign(c)
    \/ \E v, c \in Keepers : HandleVote(v, c)
    \/ \E c \in Keepers : BecomeLeader(c)
    \/ \E k \in Keepers : ExpireLease(k)
    \/ \E l \in Keepers : LeaderStepDown(l)
    \/ \E l \in Keepers, v \in Values : ClientAppend(l, v)
    \/ \E l \in Keepers : AcknowledgeRecovery(l)
    \/ \E l, f \in Keepers : ReplicateOrHeartbeat(l, f)
    \/ \E l \in Keepers : AdvanceCommit(l)
    \/ \E l, f \in Keepers : LearnHigherTerm(l, f)
    \/ \E k \in Keepers : TakeSnapshot(k)
    \/ \E l \in Keepers : ParkStream(l)
    \/ \E k \in Keepers : WakeForDead(k)
    \/ \E k \in Keepers : ClientUnpark(k)
    \/ \E k, j \in Keepers : DetectDead(k, j)
    \/ \E k, j \in Keepers : DetectAlive(k, j)
    \/ \E l, d, r \in Keepers : ProposeStageOwned(l, d, r)
    \/ \E l, r \in Keepers : StageReplicaAndAddLearner(l, r)
    \/ \E l \in Keepers : AbortReplacement(l)
    \/ \E l, r \in Keepers : InstallAndProposeJoint(l, r)
    \/ \E l \in Keepers : ProposeFinalize(l)
    \/ \E l, lrn \in Keepers : RemoveStaleLearner(l, lrn)
    \/ \E k \in Keepers : HeardTimeout(k)
    \/ \E k, a \in Keepers : RetireRemoved(k, a)
    \/ \E k \in Keepers : StopKeeper(k)
    \/ \E k \in Keepers : RestartKeeper(k)
    \/ \E k \in Keepers : WipeAndReinit(k)
    \/ \E s, r1, r2 \in Keepers : OperatorRecover(s, r1, r2)
    \/ \E k \in Keepers : ClientRead(k)
    \/ \E k \in Keepers : CatalogCheck(k)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety Properties *)

\* 1. At most one leader per term
ElectionSafety ==
    \A t \in DOMAIN leadersPerTerm : Cardinality(leadersPerTerm[t]) <= 1

\* 2. Committed entries are never lost (Leader Completeness):
\*    Every entry committed in term t_c (and not explicitly acknowledged lost by
\*    operator recovery) must be present in the log of every active-branch leader
\*    whose term is >= t_c.
CommittedEntriesPreserved ==
    \A l \in Keepers :
        (alive[l] /\ groupState[l] = "Open" /\ role[l] = "Leader"
         /\ ~(recovered /\ l \in lostVoters)) =>
            LET lApps == AppEntriesIn(log[l], Len(log[l]))
            IN /\ \A e \in committedApps :
                    e.term <= vote[l].term => ([lsn |-> e.lsn, val |-> e.val] \in lApps)
               /\ ((\E r \in 1..Len(log[l]) : log[l][r].kind = "Recover") =>
                    \A e \in postRecApps :
                        e.term <= vote[l].term => ([lsn |-> e.lsn, val |-> e.val] \in lApps))

\* 3. A retired copy never votes again
RetiredNeverVotes == ~retiredVoted

\* 4. After recovery, no reader observes a history mixing the lost suffix with
\*    the post-recovery log (nor observes conflicting entries for the same LSN).
NoMixedHistory ==
    /\ ~(readerHistory \cap lostSuffix # {} /\ readerHistory \cap postRecApps # {})
    /\ \A a, b \in readerHistory : a.lsn = b.lsn => (a.term = b.term /\ a.val = b.val)

\* 5. Log Matching: if two logs contain an entry with the same index and term,
\*    their prefixes up to that index are identical.
LogMatching ==
    \A a, b \in Keepers :
        \A i \in 1..Min(Len(log[a]), Len(log[b])) :
            log[a][i].term = log[b][i].term =>
                \A j \in 1..i : log[a][j] = log[b][j]

\* 6. A lost voter's copy never learns a term of the recovered history
\*    (Lean RecoveryFence.lost_replicas_stay_below_the_recovery_term).
LostStayBelowRecoveryTerm ==
    recovered =>
        \A k \in lostVoters :
            ownership[k].current # Nil => vote[k].term < RecoveryGap

\* Combined core safety invariant
Safety ==
    /\ ElectionSafety
    /\ CommittedEntriesPreserved
    /\ RetiredNeverVotes
    /\ NoMixedHistory
    /\ LostStayBelowRecoveryTerm

-----------------------------------------------------------------------------
(* Liveness Properties (checked under fairness in focused liveness configs) *)

\* A parked stream whose finalized voters include exactly 1 permanently dead
\* keeper (with a live eligible replacement available) is eventually repaired
\* (its finalized membership no longer contains any dead keeper).
ParkedWithOneDeadVoter ==
    \E V \in SUBSET Keepers :
        /\ Cardinality(V) = 3
        /\ Cardinality({v \in V : ~alive[v]}) = 1
        /\ \E repl \in Keepers \ V : alive[repl]
        /\ \A v \in V : alive[v] => (groupState[v] = "Parked" /\ closedCfg[v] = V)

StreamRepaired ==
    \E l \in Keepers :
        /\ alive[l] /\ groupState[l] = "Open"
        /\ LET m == AppliedMembership(l)
           IN m.configured /\ ~m.isJoint /\ (\A v \in m.voters1 : alive[v])

ParkedDeadVoterEventuallyRepaired ==
    [](ParkedWithOneDeadVoter => <>StreamRepaired)

\* After recovery, returning lost voters eventually retire
LostVotersEventuallyRetire ==
    \A k \in Keepers :
        []((recovered /\ k \in lostVoters /\ alive[k] /\ groupState[k] = "Open")
           => <>(ownership[k].current = Nil))

\* Single combined progress step for fast, sound TLC liveness checking.
\* Because terms (MaxTerm) and log length (MaxLogLen) are finite, no progress
\* action can loop infinitely and starve another enabled progress action.
ProgressStep ==
    \/ \E k, j \in Keepers : DetectDead(k, j)
    \/ \E k, j \in Keepers : DetectAlive(k, j)
    \/ \E k \in Keepers : WakeForDead(k)
    \/ \E k \in Keepers : ExpireLease(k)
    \/ \E c \in Keepers : StartCampaign(c)
    \/ \E v, c \in Keepers : HandleVote(v, c)
    \/ \E c \in Keepers : BecomeLeader(c)
    \/ \E l, f \in Keepers : ReplicateOrHeartbeat(l, f)
    \/ \E l \in Keepers : AdvanceCommit(l)
    \/ \E l, d, r \in Keepers : ProposeStageOwned(l, d, r)
    \/ \E l, r \in Keepers : StageReplicaAndAddLearner(l, r)
    \/ \E l, r \in Keepers : InstallAndProposeJoint(l, r)
    \/ \E l \in Keepers : ProposeFinalize(l)
    \/ \E k \in Keepers : HeardTimeout(k)
    \/ \E k, a \in Keepers : RetireRemoved(k, a)
    \/ \E c, v \in Keepers : PreVoteExcluded(c, v)
    \/ \E k \in Keepers : CatalogCheck(k)

RepairFairness == WF_vars(ProgressStep)

FairSpec == Spec /\ RepairFairness

-----------------------------------------------------------------------------
(* Reachable scenario initial states for tractable exhaustive liveness and
 * operator-recovery verification. Each state below is reachable from Init
 * in a short sequence of standard Raft + Logkeeper transitions. *)

\* Reachable state: {k1,k2,k3} elected k1 in term 1, replicated Blank, parked
\* on {k1,k2,k3}, and k3 then stopped permanently while k4 is live & eligible.
InitParkedDead ==
    LET k1 == CHOOSE x \in GenesisVoters : TRUE
        k2 == CHOOSE x \in GenesisVoters \ {k1} : TRUE
        k3 == CHOOSE x \in GenesisVoters \ {k1, k2} : TRUE
    IN /\ alive         = [k \in Keepers |-> (k # k3)]
        /\ deadView      = [k \in Keepers |-> {}]
        /\ crashCount    = 1
        /\ registered    = [k \in Keepers |-> (k \in GenesisVoters)]
        /\ vote          = [k \in Keepers |-> IF k \in GenesisVoters
                                              THEN [term |-> 1, votedFor |-> k1, committed |-> TRUE]
                                              ELSE InitVote]
        /\ log           = [k \in Keepers |-> IF k \in GenesisVoters
                                              THEN <<InitCfgEntry, BlankEntry(1)>>
                                              ELSE <<>>]
        /\ snapIdx       = [k \in Keepers |-> 0]
        /\ ownership     = [k \in Keepers |-> IF k \in GenesisVoters THEN DefaultOwnership ELSE EmptyOwnership]
        /\ groupState    = [k \in Keepers |-> IF k \in {k1, k2} THEN "Parked" ELSE "Closed"]
        /\ closedCfg     = [k \in Keepers |-> IF k \in {k1, k2} THEN GenesisVoters ELSE {}]
        /\ role          = [k \in Keepers |-> "Follower"]
        /\ commitIdx     = [k \in Keepers |-> 0]
        /\ appliedIdx    = [k \in Keepers |-> 0]
        /\ lease         = [k \in Keepers |-> Nil]
        /\ excluded      = [k \in Keepers |-> Nil]
        /\ heardLeader   = [k \in Keepers |-> TRUE]
        /\ votesGranted  = [k \in Keepers |-> {}]
        /\ activeStage   = [k \in Keepers |-> Nil]
        /\ staleLearners = [k \in Keepers |-> {}]
        /\ recovered     = FALSE
        /\ recoveryAcked = FALSE
        /\ lostVoters    = {}
        /\ returnedLost  = {}
        /\ survivorId    = Nil
        /\ appendCount   = 0
        /\ leadersPerTerm = [t \in 0..(MaxTerm + 1) |-> IF t = 1 THEN {k1} ELSE {}]
        /\ committedApps = {}
        /\ lostSuffix    = {}
        /\ postRecApps   = {}
        /\ readerHistory = {}
        /\ retiredVoted  = FALSE
        /\ reused        = [k \in Keepers |-> FALSE]
        /\ certified     = [k \in Keepers |-> k \in {k1, k2}]
        /\ fenced        = [k \in Keepers |-> FALSE]
        /\ catalogStage  = Nil

\* Next-state relation for parked-stream repair liveness: excludes ClientUnpark
\* and repeated re-parking so we verify that the automatic wake sweep + repair
\* alone repairs a parked stream with a dead voter.
ParkedRepairNext ==
    \/ \E k, j \in Keepers : DetectDead(k, j)
    \/ \E k, j \in Keepers : DetectAlive(k, j)
    \/ \E k \in Keepers : WakeForDead(k)
    \/ \E k \in Keepers : ExpireLease(k)
    \/ \E c \in Keepers : StartCampaign(c)
    \/ \E v, c \in Keepers : HandleVote(v, c)
    \/ \E c \in Keepers : BecomeLeader(c)
    \/ \E l, f \in Keepers : ReplicateOrHeartbeat(l, f)
    \/ \E l \in Keepers : AdvanceCommit(l)
    \/ \E l, d, r \in Keepers : ProposeStageOwned(l, d, r)
    \/ \E l, r \in Keepers : StageReplicaAndAddLearner(l, r)
    \/ \E l, r \in Keepers : InstallAndProposeJoint(l, r)
    \/ \E l \in Keepers : ProposeFinalize(l)
    \/ \E k \in Keepers : CatalogCheck(k)

FairParkedDeadSpec ==
    InitParkedDead /\ [][ParkedRepairNext]_vars
    /\ WF_vars(ParkedRepairNext)
    /\ WF_vars(\E c \in Keepers : BecomeLeader(c))
    /\ WF_vars(\E l \in Keepers : AdvanceCommit(l))

\* Reachable state: {k1,k2,k3} at rev 0 started replacing k3 with k4 (StageReplica
\* set ownership[k4].high = 1, installed = FALSE), then aborted before joint
\* consensus; k3 is alive, k1 later died, and {k2,k3} parked the stream.
InitAbortedReplace ==
    LET k1 == CHOOSE x \in GenesisVoters : TRUE
        k2 == CHOOSE x \in GenesisVoters \ {k1} : TRUE
        k3 == CHOOSE x \in GenesisVoters \ {k1, k2} : TRUE
        k4 == CHOOSE x \in Keepers \ GenesisVoters : TRUE
        abortedStage == [source |-> 0, old |-> GenesisVoters, target |-> {k1, k2, k4}]
        k4Own == [high |-> 1, gen |-> 1,
                  current |-> [gen |-> 1, rev |-> 1, stage |-> abortedStage,
                               installed |-> FALSE, isRecovery |-> FALSE],
                  retiredGens |-> {}]
        baseLog == <<InitCfgEntry, BlankEntry(1), StageOwnedEntry(1, abortedStage)>>
    IN /\ alive         = [k \in Keepers |-> (k # k1)]
       /\ deadView      = [k \in Keepers |-> {}]
       /\ crashCount    = 1
       /\ registered    = [k \in Keepers |-> TRUE]
       /\ vote          = [k \in Keepers |-> IF k \in GenesisVoters
                                             THEN [term |-> 1, votedFor |-> k2, committed |-> TRUE]
                                             ELSE InitVote]
       /\ log           = [k \in Keepers |-> IF k \in GenesisVoters THEN baseLog ELSE <<>>]
       /\ snapIdx       = [k \in Keepers |-> 0]
       /\ ownership     = [k \in Keepers |-> IF k \in GenesisVoters THEN DefaultOwnership ELSE k4Own]
       /\ groupState    = [k \in Keepers |-> IF k \in {k2, k3} THEN "Parked" ELSE "Closed"]
       /\ closedCfg     = [k \in Keepers |-> IF k \in {k2, k3} THEN GenesisVoters ELSE {}]
       /\ role          = [k \in Keepers |-> "Follower"]
       /\ commitIdx     = [k \in Keepers |-> 0]
       /\ appliedIdx    = [k \in Keepers |-> 0]
       /\ lease         = [k \in Keepers |-> Nil]
       /\ excluded      = [k \in Keepers |-> Nil]
       /\ heardLeader   = [k \in Keepers |-> TRUE]
       /\ votesGranted  = [k \in Keepers |-> {}]
       /\ activeStage   = [k \in Keepers |-> Nil]
       /\ staleLearners = [k \in Keepers |-> {}]
       /\ recovered     = FALSE
       /\ recoveryAcked = FALSE
       /\ lostVoters    = {}
       /\ returnedLost  = {}
       /\ survivorId    = Nil
       /\ appendCount   = 0
       /\ leadersPerTerm = [t \in 0..(MaxTerm + 1) |-> IF t = 1 THEN {k2} ELSE {}]
       /\ committedApps = {}
       /\ lostSuffix    = {}
       /\ postRecApps   = {}
       /\ readerHistory = {}
       /\ retiredVoted  = FALSE
       /\ reused        = [k \in Keepers |-> FALSE]
       /\ certified     = [k \in Keepers |-> k \in {k2, k3}]
       /\ fenced        = [k \in Keepers |-> FALSE]
       /\ catalogStage  = [stage |-> abortedStage, recovery |-> FALSE]

FairAbortedReplaceSpec ==
    InitAbortedReplace /\ [][ParkedRepairNext]_vars
    /\ WF_vars(ParkedRepairNext)
    /\ WF_vars(\E l \in Keepers : AdvanceCommit(l))

\* Reachable state for CE-2 safety: k2 led {k1,k2,k3} in term 1, committed
\* StageOwned(S1) replacing k3 with k4, staged and installed k4, and appended
\* the joint configuration of S1 on itself and k4 only. Then k2 stopped, so
\* the joint entry is uncommitted while k4 has voted under it in term 1. A
\* later leader of {k1,k3} may move k2 off onto k4 from the same source,
\* which restages k4's installed copy of S1.
InitAbortedJoint ==
    LET k1 == CHOOSE x \in GenesisVoters : TRUE
        k2 == CHOOSE x \in GenesisVoters \ {k1} : TRUE
        k3 == CHOOSE x \in GenesisVoters \ {k1, k2} : TRUE
        k4 == CHOOSE x \in Keepers \ GenesisVoters : TRUE
        s1 == [source |-> 0, old |-> GenesisVoters, target |-> {k1, k2, k4}]
        base == <<InitCfgEntry, BlankEntry(1), StageOwnedEntry(1, s1)>>
        learn == Append(base, CfgEntry(1, "InitCfg", GenesisVoters, {}, {k4}, 0))
        joint == Append(learn, CfgEntry(1, "JointCfg", GenesisVoters, s1.target, {}, 0))
        k4Own == [high |-> 1, gen |-> 1,
                  current |-> [gen |-> 1, rev |-> 1, stage |-> s1,
                               installed |-> TRUE, isRecovery |-> FALSE],
                  retiredGens |-> {}]
    IN /\ alive         = [k \in Keepers |-> (k # k2)]
       /\ deadView      = [k \in Keepers |-> {}]
       /\ crashCount    = 1
       /\ registered    = [k \in Keepers |-> k \in GenesisVoters \cup {k4}]
       /\ vote          = [k \in Keepers |-> IF k \in GenesisVoters \cup {k4}
                                             THEN [term |-> 1, votedFor |-> k2, committed |-> TRUE]
                                             ELSE InitVote]
       /\ log           = [k \in Keepers |->
                             IF k \in {k2, k4} THEN joint
                             ELSE IF k = k1 THEN learn
                             ELSE IF k = k3 THEN base
                             ELSE <<>>]
       /\ snapIdx       = [k \in Keepers |-> 0]
       /\ ownership     = [k \in Keepers |->
                             IF k \in GenesisVoters THEN DefaultOwnership
                             ELSE IF k = k4 THEN k4Own
                             ELSE EmptyOwnership]
       /\ groupState    = [k \in Keepers |-> IF k \in {k1, k3, k4} THEN "Open" ELSE "Closed"]
       /\ closedCfg     = [k \in Keepers |-> IF k \in GenesisVoters THEN GenesisVoters ELSE {}]
       /\ role          = [k \in Keepers |-> "Follower"]
       /\ commitIdx     = [k \in Keepers |-> IF k \in {k1, k4} THEN 4 ELSE IF k = k3 THEN 3 ELSE 0]
       /\ appliedIdx    = [k \in Keepers |-> IF k \in {k1, k4} THEN 4 ELSE IF k = k3 THEN 3 ELSE 0]
       /\ lease         = [k \in Keepers |-> Nil]
       /\ excluded      = [k \in Keepers |-> Nil]
       /\ heardLeader   = [k \in Keepers |-> TRUE]
       /\ votesGranted  = [k \in Keepers |-> {}]
       /\ activeStage   = [k \in Keepers |-> Nil]
       /\ staleLearners = [k \in Keepers |-> {}]
       /\ recovered     = FALSE
       /\ recoveryAcked = FALSE
       /\ lostVoters    = {}
       /\ returnedLost  = {}
       /\ survivorId    = Nil
       /\ appendCount   = 0
       /\ leadersPerTerm = [t \in 0..(MaxTerm + 1) |-> IF t = 1 THEN {k2} ELSE {}]
       /\ committedApps = {}
       /\ lostSuffix    = {}
       /\ postRecApps   = {}
       /\ readerHistory = {}
       /\ retiredVoted  = FALSE
       /\ reused        = [k \in Keepers |-> FALSE]
       /\ certified     = [k \in Keepers |-> k \in {k1, k3, k4}]
       /\ fenced        = [k \in Keepers |-> FALSE]
       /\ catalogStage  = [stage |-> s1, recovery |-> FALSE]

AbortedJointSpec == InitAbortedJoint /\ [][Next]_vars

\* Reachable pre-recovery state: {k1,k2,k3} elected k2 in term 1 and committed
\* App(lsn=1, "v1") on {k2,k3}; survivor k1 missed that entry (holds only InitCfg).
\* When AllowSnapshot=TRUE, k2 also persisted a local snapshot at index 3.
\* All three genesis voters are stopped (k2,k3 lost; k1 stopped for recover-stream)
\* while replacements k4,k5 are live.
\* To avoid symmetric dead branches, OperatorRecover only recovers the lagging
\* survivor k1 (where lostSuffix is non-empty).
OperatorRecoverFrom(surv, r1, r2) ==
    /\ OperatorRecover(surv, r1, r2)
    /\ (lostSuffix' # {} \/ committedApps = {})

InitPreRecovery ==
    LET k1 == CHOOSE x \in GenesisVoters : TRUE
        k2 == CHOOSE x \in GenesisVoters \ {k1} : TRUE
        k3 == CHOOSE x \in GenesisVoters \ {k1, k2} : TRUE
        v1 == CHOOSE v \in Values : TRUE
        lostLog == <<InitCfgEntry, BlankEntry(1), AppEntry(1, 1, v1)>>
    IN /\ alive         = [k \in Keepers |-> ~(k \in GenesisVoters)]
       /\ deadView      = [k \in Keepers |-> {}]
       /\ crashCount    = 3
       /\ registered    = [k \in Keepers |-> (k \in GenesisVoters)]
       /\ vote          = [k \in Keepers |->
                             IF k \in {k2, k3} THEN [term |-> 1, votedFor |-> k2, committed |-> TRUE]
                             ELSE InitVote]
       /\ log           = [k \in Keepers |->
                             IF k \in {k2, k3} THEN lostLog
                             ELSE IF k = k1 THEN <<InitCfgEntry>>
                             ELSE <<>>]
       /\ snapIdx       = [k \in Keepers |-> IF AllowSnapshot /\ k = k2 THEN 3 ELSE 0]
       /\ ownership     = [k \in Keepers |-> IF k \in GenesisVoters THEN DefaultOwnership ELSE EmptyOwnership]
       /\ groupState    = [k \in Keepers |-> "Closed"]
       /\ closedCfg     = [k \in Keepers |-> IF k \in GenesisVoters THEN GenesisVoters ELSE {}]
       /\ role          = [k \in Keepers |-> "Follower"]
       /\ commitIdx     = [k \in Keepers |-> 0]
       /\ appliedIdx    = [k \in Keepers |-> 0]
       /\ lease         = [k \in Keepers |-> Nil]
       /\ excluded      = [k \in Keepers |-> Nil]
       /\ heardLeader   = [k \in Keepers |-> TRUE]
       /\ votesGranted  = [k \in Keepers |-> {}]
       /\ activeStage   = [k \in Keepers |-> Nil]
       /\ staleLearners = [k \in Keepers |-> {}]
       /\ recovered     = FALSE
       /\ recoveryAcked = FALSE
       /\ lostVoters    = {}
       /\ returnedLost  = {}
       /\ survivorId    = Nil
       /\ appendCount   = 1
       /\ leadersPerTerm = [t \in 0..(MaxTerm + RecoveryGap + 3) |-> IF t = 1 THEN {k2} ELSE {}]
       /\ committedApps = {[lsn |-> 1, val |-> v1, term |-> 1]}
       /\ lostSuffix    = {}
       /\ postRecApps   = {}
       /\ readerHistory = {}
       /\ retiredVoted  = FALSE
       /\ reused        = [k \in Keepers |-> FALSE]
       /\ certified     = [k \in Keepers |-> FALSE]
       /\ fenced        = [k \in Keepers |-> FALSE]
       /\ catalogStage  = Nil

PreRecoveryNext ==
    \/ (\E s, r1, r2 \in Keepers : OperatorRecoverFrom(s, r1, r2))
    \/ (recovered /\ Next)

PreRecoverySpec == InitPreRecovery /\ [][PreRecoveryNext]_vars
FairPreRecoverySpec ==
    InitPreRecovery /\ [][PreRecoveryNext]_vars /\ RepairFairness
    /\ WF_vars(\E s \in Keepers : recovered /\ s = survivorId /\ RestartKeeper(s))

\* Reachable post-recovery state: recovery committed on {k1,k4,k5} in term 11,
\* k1 subsequently stopped (or was replaced), and k4 leads {k1,k4,k5} in term 12
\* (with k5 as follower, serving valid PlacementProof at rev 1). Lost voters
\* k2 and k3 now restart!
InitPostRecovery ==
    LET k1 == CHOOSE x \in GenesisVoters : TRUE
        k2 == CHOOSE x \in GenesisVoters \ {k1} : TRUE
        k3 == CHOOSE x \in GenesisVoters \ {k1, k2} : TRUE
        k4 == CHOOSE x \in Keepers \ GenesisVoters : TRUE
        k5 == CHOOSE x \in Keepers \ (GenesisVoters \cup {k4}) : TRUE
        v1 == CHOOSE v \in Values : TRUE
        target == {k1, k4, k5}
        st == [source |-> 0, old |-> GenesisVoters, target |-> target]
        lostLog == <<InitCfgEntry, BlankEntry(1), AppEntry(1, 1, v1)>>
        recLog  == <<InitCfgEntry, RecoverEntry(RecoveryGap, st),
                     CfgEntry(RecoveryGap, "FinalCfg", target, {}, {}, 1),
                     BlankEntry(RecoveryGap + 1), BlankEntry(RecoveryGap + 2)>>
        recOwn  == [high |-> 1, gen |-> 1,
                    current |-> [gen |-> 1, rev |-> 1, stage |-> st,
                                 installed |-> TRUE, isRecovery |-> TRUE],
                    retiredGens |-> {}]
        survOwn == [high |-> 1, gen |-> 0,
                    current |-> [gen |-> 0, rev |-> 1, stage |-> Nil,
                                 installed |-> TRUE, isRecovery |-> FALSE],
                    retiredGens |-> {}]
        retSet  == IF MaxReturningLost = 1 THEN {k2} ELSE {k2, k3}
    IN /\ alive         = [k \in Keepers |-> (k \in {k4, k5} \cup retSet)]
       /\ deadView      = [k \in Keepers |-> {}]
       /\ crashCount    = 4
       /\ registered    = [k \in Keepers |-> TRUE]
       /\ vote          = [k \in Keepers |->
                             IF k \in {k4, k5} THEN [term |-> RecoveryGap + 2, votedFor |-> k4, committed |-> TRUE]
                             ELSE IF k = k1 THEN [term |-> RecoveryGap + 1, votedFor |-> k1, committed |-> TRUE]
                             ELSE [term |-> 1, votedFor |-> k2, committed |-> FALSE]]
       /\ log           = [k \in Keepers |->
                             IF k \in {k4, k5} THEN recLog
                             ELSE IF k = k1 THEN SubSeq(recLog, 1, 4)
                             ELSE lostLog]
       /\ snapIdx       = [k \in Keepers |-> 0]
       /\ ownership     = [k \in Keepers |->
                             IF k \in {k4, k5} THEN recOwn
                             ELSE IF k = k1 THEN survOwn
                             ELSE DefaultOwnership]
       /\ groupState    = [k \in Keepers |-> IF k \in {k4, k5} \cup retSet THEN "Open" ELSE "Closed"]
       /\ closedCfg     = [k \in Keepers |-> IF k \in GenesisVoters THEN GenesisVoters ELSE target]
       /\ role          = [k \in Keepers |-> IF k = k4 THEN "Leader" ELSE "Follower"]
       /\ commitIdx     = [k \in Keepers |-> IF k \in {k4, k5} THEN 5 ELSE 0]
       /\ appliedIdx    = [k \in Keepers |-> IF k \in {k4, k5} THEN 5 ELSE 0]
       /\ lease         = [k \in Keepers |-> IF k \in {k4, k5} THEN k4 ELSE Nil]
       /\ excluded      = [k \in Keepers |-> Nil]
       /\ heardLeader   = [k \in Keepers |-> TRUE]
       /\ votesGranted  = [k \in Keepers |-> IF k = k4 THEN {k4, k5} ELSE {}]
       /\ activeStage   = [k \in Keepers |-> Nil]
       /\ staleLearners = [k \in Keepers |-> {}]
       /\ recovered     = TRUE
       /\ recoveryAcked = FALSE
       /\ lostVoters    = {k2, k3}
       /\ returnedLost  = retSet
       /\ survivorId    = k1
       /\ appendCount   = 1
       /\ leadersPerTerm = [t \in 0..(MaxTerm + RecoveryGap + 3) |->
                             IF t = 1 THEN {k2}
                             ELSE IF t = RecoveryGap + 1 THEN {k1}
                             ELSE IF t = RecoveryGap + 2 THEN {k4}
                             ELSE {}]
       /\ committedApps = {}
       /\ lostSuffix    = {[lsn |-> 1, val |-> v1, term |-> 1]}
       /\ postRecApps   = {}
       /\ readerHistory = {}
       /\ retiredVoted  = FALSE
       /\ reused        = [k \in Keepers |-> FALSE]
       /\ certified     = [k \in Keepers |-> k \in {k4, k5}]
       /\ fenced        = [k \in Keepers |-> FALSE]
       /\ catalogStage  = [stage |-> st, recovery |-> TRUE]

PostRecRetireNext ==
    \/ \E c, v \in Keepers : PreVoteExcluded(c, v)
    \/ \E c \in Keepers : StartCampaign(c)
    \/ \E v, c \in Keepers : HandleVote(v, c)
    \/ \E c \in Keepers : BecomeLeader(c)
    \/ \E l, f \in Keepers : ReplicateOrHeartbeat(l, f)
    \/ \E l \in Keepers : AdvanceCommit(l)
    \/ \E k \in Keepers : HeardTimeout(k)
    \/ \E k, a \in Keepers : RetireRemoved(k, a)
    \/ \E k \in Keepers : CatalogCheck(k)

FairPostRecoverySpec ==
    InitPostRecovery /\ [][PostRecRetireNext]_vars /\ WF_vars(PostRecRetireNext)

=============================================================================
