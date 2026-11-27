----------------------------- MODULE EpochLeases -----------------------------
(*
 * The endgame configuration authority: keeper liveness leases with epochs,
 * derived from the catalog, gating campaign, lead and read
 * (logkeeper-consensus-design.md, "Endgame: a configuration authority with
 * epoch leases", approved 2026-11-27).
 *
 * One stream. Raft is modeled compactly in the style of LogkeeperProtocol
 * (direct RPCs between reachable processes, full-log replication, commit by
 * inspection of the holders' logs), with what the endgame adds on top:
 *
 *   - explicit time: a global real-time tick and a local tick per process.
 *     Every interval a process measures (a lease since its grant, a wait-out
 *     since the recovery commit) is an anchor [le, d]: le is the local time
 *     elapsed since the anchor and d = local - real elapsed. Ticks keep
 *     |d| <= D for every live anchor, which is what bounded clock-rate drift
 *     gives over an interval no longer than a lease plus the wait-out
 *     (D = rho * (L + M + D)). No clock is synchronized with any other.
 *   - keeper liveness leases: one record per keeper in the catalog
 *     {epoch, fenced_streams}. A renewal is granted only when the keeper's
 *     incarnation epoch is the catalog's, and carries whether this stream is
 *     in the keeper's fenced_streams. The holder treats it as valid while
 *     its local elapsed time is below L - M.
 *   - gating: Campaign, BecomeLeader, Append, Replicate, Commit and Read need
 *     a valid lease of the current epoch whose fenced_streams omit the
 *     stream, and a finished wait-out. Voting and following are not gated.
 *   - recovery as one catalog transaction: bump the stream's configuration,
 *     install the new membership, add the stream to the fenced_streams of
 *     every old member outside it (or only of the keepers named by --lost,
 *     under FenceRule = "NamedOnly", the spec's wording), bump the epochs of
 *     the named keepers if the operator declares them dead, and write the
 *     survivors' recovery round. Every member of the new configuration then
 *     waits out L + M on its own clock before it campaigns, leads or reads.
 *     The --lost argument is chosen nondeterministically: it may be absent,
 *     partial or wrong.
 *   - partitions: every process and the catalog sit on one of two sides,
 *     and a bounded number of arbitrary re-partitions happen at any time.
 *   - catalog outage: the catalog may go down for good.
 *   - media reuse: a second incarnation of one keeper ID (ReusedProc) can
 *     register with the catalog under a bumped epoch while the first
 *     incarnation keeps running or stops.
 *
 * Renewals are atomic at the catalog's grant: the holder's anchor starts
 * when the catalog grants, not when the holder sent the request, which only
 * lengthens leases, and a delayed reply is simulated by a later grant
 * (README.md, "Epoch leases").
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Procs,            \* processes; one per keeper ID, plus ReusedProc
    ReusedProc,       \* a second incarnation of ReusedId, or NoProc
    ReusedId,         \* the keeper ID ReusedProc reuses
    OldVoters,        \* the stream's configuration before recovery (IDs)
    Survivors,        \* the voters the recovery keeps (IDs)
    Replacements,     \* the fresh voters the recovery adds (IDs)
    L,                \* lease duration, in ticks
    M,                \* drift margin, in ticks
    D,                \* drift bound: |local - real elapsed| over one anchor
    WaitOut,          \* the recovered configuration waits out L + M
    FenceRule,        \* "AllOld" or "NamedOnly"
    ExcludeLostIds,   \* a recovered copy refuses the lost voters whatever their term
    RecoveryGap,      \* the recovery's term jump (2^32 in the code)
    MaxTerm,          \* bound on terms reached before recovery and by lost voters
    MaxNewTerms,      \* bound on elections after the recovery term
    MaxLogLen,
    MaxAppends,
    MaxPartitionChanges,
    PartitionAfterRecovery, \* re-partitions happen only once the recovery committed
    AllowRecovery,
    AllowCatalogOutage,
    AllowReincarnation,
    RefuseReusedRegistration, \* 6d75fec: a reused ID never registers from peer traffic
    AllowStop,        \* the first incarnation of ReusedId may stop
    LeasedProcs,      \* processes whose leases are modeled; the others always hold one
    NoProc,
    Nil

IdOf(p) == IF p = ReusedProc THEN ReusedId ELSE p
Ids == {IdOf(p) : p \in Procs}
NewVoters == Survivors \cup Replacements
Cat == "catalog"
Nodes == Procs \cup {Cat}

ASSUME Survivors \subseteq OldVoters
ASSUME Replacements \cap OldVoters = {}
ASSUME FenceRule \in {"AllOld", "NamedOnly"}
ASSUME L > M /\ M >= 0 /\ D >= 0

VARIABLES
    side, catUp, partChanges,
    alive, copy, term, votedFor, log, commit, role, votes,
    lease, wait, myEpoch,
    catEpoch, catFenced, catMembers, cfgEpoch,
    recovered, survHist, recTerm, lostIds, reportedHead,
    appendCount, committedOld, committedNew, leaders,
    newSeen, newObs, mixed

netVars == <<side, catUp, partChanges>>
raftVars == <<alive, copy, term, votedFor, log, commit, role, votes>>
leaseVars == <<lease, wait, myEpoch>>
catVars == <<catEpoch, catFenced, catMembers, cfgEpoch>>
ghostVars == <<recovered, survHist, recTerm, lostIds, reportedHead,
               appendCount, committedOld, committedNew, leaders,
               newSeen, newObs, mixed>>
vars == <<netVars, raftVars, leaseVars, catVars, ghostVars>>

-----------------------------------------------------------------------------
(* Entries, configurations and logs *)

CfgE(t, mem) == [term |-> t, kind |-> "Cfg", lsn |-> 0, val |-> 0, mem |-> mem]
\* The recovery record: the first entry of the stream configuration epoch
\* `e` the catalog transaction installs (one recovery record; offload's
\* lineage is the same epoch).
RecE(t, mem, e) == [term |-> t, kind |-> "Rec", lsn |-> 0, val |-> e, mem |-> mem]
BlankE(t, id) == [term |-> t, kind |-> "Blank", lsn |-> 0, val |-> id, mem |-> {}]
AppE(t, lsn, v) == [term |-> t, kind |-> "App", lsn |-> lsn, val |-> v, mem |-> {}]

Max(a, b) == IF a >= b THEN a ELSE b
Min(a, b) == IF a <= b THEN a ELSE b
MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x

LastTerm(lg) == IF Len(lg) = 0 THEN 0 ELSE lg[Len(lg)].term
UpToDate(cand, voter) ==
    \/ LastTerm(cand) > LastTerm(voter)
    \/ (LastTerm(cand) = LastTerm(voter) /\ Len(cand) >= Len(voter))

CfgIdx(lg) == {i \in 1..Len(lg) : lg[i].kind \in {"Cfg", "Rec"}}
ConfigOf(lg) == IF CfgIdx(lg) = {} THEN {} ELSE lg[MaxOf(CfgIdx(lg))].mem
Config(p) == ConfigOf(log[p])
HasRec(lg) == \E i \in 1..Len(lg) : lg[i].kind = "Rec"

HeadLsn(lg) == LET a == {i \in 1..Len(lg) : lg[i].kind = "App"}
               IN IF a = {} THEN 0 ELSE lg[MaxOf(a)].lsn
AppsUpTo(lg, n) == {[lsn |-> lg[i].lsn, val |-> lg[i].val, term |-> lg[i].term] :
                      i \in {j \in 1..n : lg[j].kind = "App"}}
Apps(lg) == AppsUpTo(lg, Len(lg))

IsPrefix(a, b) == Len(a) <= Len(b) /\ SubSeq(b, 1, Len(a)) = a

\* A log of the recovered world extends the survivors' recovery round.
NewWorld(lg) == recovered /\ IsPrefix(survHist, lg)

Quorum(S, mem) == mem # {} /\ 2 * Cardinality(S \cap mem) > Cardinality(mem)

-----------------------------------------------------------------------------
(* Network, leases and gating *)

Reach(p, q) == alive[p] /\ alive[q] /\ side[p] = side[q]
CatReach(p) == catUp /\ alive[p] /\ side[p] = side[Cat]

NoLease == [on |-> FALSE, le |-> 0, d |-> 0, epoch |-> 0, fenced |-> FALSE]
NoWait == [st |-> "none", le |-> 0, d |-> 0]
DoneWait == [st |-> "done", le |-> 0, d |-> 0]
RunWait == [st |-> "run", le |-> 0, d |-> 0]

LeaseValid(p) ==
    /\ lease[p].on
    /\ lease[p].epoch = myEpoch[p]
    /\ ~lease[p].fenced

\* One wait-out clock stands for every recovered member's: the one that
\* finishes first. Letting every member act once it finishes only adds
\* behaviors (README.md, "Epoch leases").
WaitDone(p) == ~(IdOf(p) \in NewVoters /\ wait.st = "run")

\* Rule 3: campaign, lead and serve reads only under a valid lease of the
\* current epoch that does not fence the stream, after any wait-out.
\* A process outside LeasedProcs is treated as always holding a valid,
\* unfenced lease: that only adds behaviors, so safety checked with it holds
\* with leases modeled for every keeper.
Gate(p) == alive[p] /\ copy[p] /\ (p \in LeasedProcs => LeaseValid(p)) /\ WaitDone(p)

\* decisions::excludes_sender, plus (ExcludeLostIds) a recovered copy's
\* refusal of the recovery's lost voters at any term.
Excludes(recv, sender) ==
    /\ Config(recv) # {}
    /\ IdOf(sender) \notin Config(recv)
    /\ \/ term[sender] < term[recv]
       \/ (ExcludeLostIds /\ recovered /\ IdOf(sender) \in lostIds /\ HasRec(log[recv]))

\* A process without a copy registers one from peer traffic unless it is a
\* reused ID (6d75fec).
CanRegister(p) == ~(p = ReusedProc /\ RefuseReusedRegistration)
Accepts(p) == copy[p] \/ CanRegister(p)

TermOK(t) == t <= MaxTerm \/ (recovered /\ t <= recTerm + MaxNewTerms)

-----------------------------------------------------------------------------
(* Raft *)

\* In a recovery configuration with PartitionAfterRecovery the survivors and
\* replacements are cut off from the lost voters until the recovery and
\* cannot win an election; letting them campaign would only raise the
\* recovery term, so they wait (the lowest recovery term is the hard case).
Campaign(c) ==
    /\ Gate(c) /\ role[c] # "Leader"
    /\ (recovered \/ IdOf(c) \notin NewVoters \/ ~PartitionAfterRecovery \/ ~AllowRecovery)
    /\ IdOf(c) \in Config(c)
    /\ TermOK(term[c] + 1)
    /\ term' = [term EXCEPT ![c] = term[c] + 1]
    /\ votedFor' = [votedFor EXCEPT ![c] = IdOf(c)]
    /\ role' = [role EXCEPT ![c] = "Candidate"]
    /\ votes' = [votes EXCEPT ![c] = {IdOf(c)}]
    /\ UNCHANGED <<netVars, alive, copy, log, commit, leaseVars, catVars, ghostVars>>

Vote(v, c) ==
    /\ v # c /\ IdOf(v) # IdOf(c) /\ Reach(v, c)
    /\ role[c] = "Candidate"
    /\ IdOf(v) \in Config(c) /\ IdOf(v) \notin votes[c]
    /\ Accepts(v)
    /\ ~Excludes(v, c)
    /\ \/ term[c] > term[v]
       \/ (term[c] = term[v] /\ votedFor[v] \in {Nil, IdOf(c)})
    /\ UpToDate(log[c], log[v])
    /\ copy' = [copy EXCEPT ![v] = TRUE]
    /\ term' = [term EXCEPT ![v] = term[c]]
    /\ votedFor' = [votedFor EXCEPT ![v] = IdOf(c)]
    /\ role' = [role EXCEPT ![v] = "Follower"]
    /\ votes' = [votes EXCEPT ![c] = votes[c] \cup {IdOf(v)}]
    /\ UNCHANGED <<netVars, alive, log, commit, leaseVars, catVars, ghostVars>>

\* A candidate or leader adopts a newer term from an unexcluded answer.
LearnHigherTerm(l, f) ==
    /\ l # f /\ Reach(l, f) /\ copy[f]
    /\ role[l] \in {"Candidate", "Leader"}
    /\ IdOf(f) \in Config(l)
    /\ term[f] > term[l]
    /\ ~Excludes(f, l)
    /\ term' = [term EXCEPT ![l] = term[f]]
    /\ votedFor' = [votedFor EXCEPT ![l] = Nil]
    /\ role' = [role EXCEPT ![l] = "Follower"]
    /\ votes' = [votes EXCEPT ![l] = {}]
    /\ UNCHANGED <<netVars, alive, copy, log, commit, leaseVars, catVars, ghostVars>>

BecomeLeader(c) ==
    /\ Gate(c) /\ role[c] = "Candidate"
    /\ Quorum(votes[c], Config(c))
    /\ Len(log[c]) < MaxLogLen
    /\ role' = [role EXCEPT ![c] = "Leader"]
    /\ log' = [log EXCEPT ![c] = Append(log[c], BlankE(term[c], IdOf(c)))]
    /\ leaders' = leaders \cup {[term |-> term[c], id |-> IdOf(c), world |-> NewWorld(log[c])]}
    /\ UNCHANGED <<netVars, alive, copy, term, votedFor, commit, votes, leaseVars, catVars>>
    /\ UNCHANGED <<recovered, survHist, recTerm, lostIds, reportedHead,
                   appendCount, committedOld, committedNew, newSeen, newObs, mixed>>

\* A leader may step down at any time; fairness makes one whose lease lapsed
\* step down.
StepDown(l) ==
    /\ role[l] = "Leader"
    /\ role' = [role EXCEPT ![l] = "Follower"]
    /\ UNCHANGED <<netVars, alive, copy, term, votedFor, log, commit, votes,
                   leaseVars, catVars, ghostVars>>

ClientAppend(l) ==
    /\ Gate(l) /\ role[l] = "Leader"
    /\ appendCount < MaxAppends /\ Len(log[l]) < MaxLogLen
    /\ log' = [log EXCEPT ![l] = Append(log[l], AppE(term[l], HeadLsn(log[l]) + 1, appendCount + 1))]
    /\ appendCount' = appendCount + 1
    /\ UNCHANGED <<netVars, alive, copy, term, votedFor, commit, role, votes,
                   leaseVars, catVars>>
    /\ UNCHANGED <<recovered, survHist, recTerm, lostIds, reportedHead,
                   committedOld, committedNew, leaders, newSeen, newObs, mixed>>

Replicate(l, f) ==
    /\ Gate(l) /\ role[l] = "Leader"
    /\ l # f /\ IdOf(f) # IdOf(l) /\ Reach(l, f)
    /\ IdOf(f) \in Config(l)
    /\ Accepts(f)
    /\ ~Excludes(f, l)
    /\ term[f] <= term[l]
    /\ (log[f] # log[l] \/ term[f] < term[l] \/ commit[f] < commit[l]
        \/ role[f] # "Follower" \/ ~copy[f])
    /\ copy' = [copy EXCEPT ![f] = TRUE]
    /\ term' = [term EXCEPT ![f] = term[l]]
    /\ votedFor' = [votedFor EXCEPT ![f] = IdOf(l)]
    /\ role' = [role EXCEPT ![f] = "Follower"]
    /\ log' = [log EXCEPT ![f] = log[l]]
    /\ commit' = [commit EXCEPT ![f] = Min(Max(commit[f], commit[l]), Len(log[l]))]
    /\ UNCHANGED <<netVars, alive, votes, leaseVars, catVars, ghostVars>>

Commit(l) ==
    /\ Gate(l) /\ role[l] = "Leader"
    /\ \E i \in (commit[l] + 1)..Len(log[l]) :
        /\ log[l][i].term = term[l]
        /\ Quorum({IdOf(q) : q \in {x \in Procs : copy[x] /\ Len(log[x]) >= i
                                                   /\ log[x][i] = log[l][i]}},
                  Config(l))
        /\ commit' = [commit EXCEPT ![l] = i]
        /\ LET fresh == {[app |-> e, cterm |-> term[l]] :
                            e \in AppsUpTo(log[l], i) \ AppsUpTo(log[l], commit[l])}
           IN IF NewWorld(log[l])
              THEN /\ committedNew' = committedNew \cup fresh
                   /\ UNCHANGED committedOld
              ELSE /\ committedOld' = committedOld \cup fresh
                   /\ UNCHANGED committedNew
    /\ UNCHANGED <<netVars, alive, copy, term, votedFor, log, role, votes, leaseVars, catVars>>
    /\ UNCHANGED <<recovered, survHist, recTerm, lostIds, reportedHead,
                   appendCount, leaders, newSeen, newObs, mixed>>

\* A reader's ReadAt or lease read: the committed prefix of a gated voter.
\* After a read of the recovered history, any read of a history the recovery
\* did not keep, or of a diverging recovered history, is a mixed history.
Read(p) ==
    /\ recovered
    /\ Gate(p) /\ IdOf(p) \in Config(p)
    /\ LET obs == SubSeq(log[p], 1, commit[p])
       IN IF NewWorld(obs)
          THEN /\ newSeen' = TRUE
               /\ newObs' = IF Len(obs) > Len(newObs) THEN obs ELSE newObs
               /\ mixed' = (mixed \/ ~(IsPrefix(obs, newObs) \/ IsPrefix(newObs, obs)))
          ELSE /\ mixed' = (mixed \/ (newSeen /\ ~IsPrefix(obs, survHist)))
               /\ UNCHANGED <<newSeen, newObs>>
    /\ UNCHANGED <<netVars, raftVars, leaseVars, catVars>>
    /\ UNCHANGED <<recovered, survHist, recTerm, lostIds, reportedHead,
                   appendCount, committedOld, committedNew, leaders>>

-----------------------------------------------------------------------------
(* Time and leases *)

LeaseOn(p) == lease[p].on
WaitOn == wait.st = "run"
HasAnchor(p) == LeaseOn(p)

\* Real time advances; every live anchor's local clock falls behind by one.
RealTick ==
    /\ (\E p \in Procs : HasAnchor(p)) \/ WaitOn
    /\ \A p \in Procs : LeaseOn(p) => lease[p].d - 1 >= -D
    /\ WaitOn => wait.d - 1 >= -D
    /\ lease' = [p \in Procs |-> IF LeaseOn(p)
                                 THEN [lease[p] EXCEPT !.d = @ - 1] ELSE lease[p]]
    /\ wait' = IF WaitOn THEN [wait EXCEPT !.d = @ - 1] ELSE wait
    /\ UNCHANGED <<netVars, raftVars, myEpoch, catVars, ghostVars>>

\* Process p's monotonic clock advances. A lease lapses once its holder has
\* measured L - M since the grant; a wait-out ends after L + M.
LocalTick(p) ==
    /\ alive[p] /\ HasAnchor(p)
    /\ LeaseOn(p) => lease[p].d + 1 <= D
    /\ lease' = [lease EXCEPT ![p] =
                    IF ~@.on THEN @
                    ELSE IF @.le + 1 >= L - M THEN NoLease
                    ELSE [@ EXCEPT !.le = @ + 1, !.d = @ + 1]]
    /\ UNCHANGED <<netVars, raftVars, wait, myEpoch, catVars, ghostVars>>

\* The wait-out clock advances.
WaitTick ==
    /\ WaitOn /\ wait.d + 1 <= D
    /\ wait' = IF wait.le + 1 >= L + M THEN DoneWait
               ELSE [wait EXCEPT !.le = @ + 1, !.d = @ + 1]
    /\ UNCHANGED <<netVars, raftVars, lease, myEpoch, catVars, ghostVars>>

\* Rule 2: the catalog grants a renewal only to the current incarnation; the
\* lease says whether the stream is in the keeper's fenced_streams.
Renew(p) ==
    /\ p \in LeasedProcs
    /\ CatReach(p) /\ copy[p]
    /\ catEpoch[IdOf(p)] = myEpoch[p]
    /\ LET g == [on |-> TRUE, le |-> 0, d |-> 0, epoch |-> myEpoch[p], fenced |-> catFenced[IdOf(p)]]
       IN /\ lease[p] # g
          /\ lease' = [lease EXCEPT ![p] = g]
    /\ UNCHANGED <<netVars, raftVars, wait, myEpoch, catVars, ghostVars>>

-----------------------------------------------------------------------------
(* Environment *)

AnchorId == CHOOSE k \in Survivors : TRUE

Repartition ==
    /\ partChanges < MaxPartitionChanges
    /\ PartitionAfterRecovery => recovered
    \* Up to relabeling the sides: the replacements stay with the first
    \* survivor, and every other keeper and the catalog pick a side.
    /\ \E s \in [Nodes -> {1, 2}] :
        /\ s # side
        /\ \A p \in Procs : IdOf(p) \in Replacements \cup {AnchorId} => s[p] = 1
        /\ side' = s
    /\ partChanges' = partChanges + 1
    /\ UNCHANGED <<catUp, raftVars, leaseVars, catVars, ghostVars>>

CatalogDown ==
    /\ AllowCatalogOutage /\ catUp
    /\ catUp' = FALSE
    /\ UNCHANGED <<side, partChanges, raftVars, leaseVars, catVars, ghostVars>>

\* The first incarnation of a reused ID stops; it loses its in-memory lease.
Stop(p) ==
    /\ AllowStop /\ alive[p] /\ p # ReusedProc /\ IdOf(p) = ReusedId
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ role' = [role EXCEPT ![p] = "Follower"]
    /\ lease' = [lease EXCEPT ![p] = NoLease]
    /\ UNCHANGED <<netVars, copy, term, votedFor, log, commit, votes, wait, myEpoch,
                   catVars, ghostVars>>

\* Rule 2: a new disk under the same keeper ID registers with the catalog,
\* which bumps the ID's epoch. The first incarnation may still be running.
Reincarnate ==
    /\ AllowReincarnation /\ ~alive[ReusedProc]
    /\ catUp /\ side[ReusedProc] = side[Cat]
    /\ alive' = [alive EXCEPT ![ReusedProc] = TRUE]
    /\ myEpoch' = [myEpoch EXCEPT ![ReusedProc] = catEpoch[ReusedId] + 1]
    /\ catEpoch' = [catEpoch EXCEPT ![ReusedId] = @ + 1]
    /\ UNCHANGED <<netVars, copy, term, votedFor, log, commit, role, votes,
                   lease, wait, catFenced, catMembers, cfgEpoch, ghostVars>>

-----------------------------------------------------------------------------
(* Rule 4: recovery is one catalog transaction *)

SurvivorProcs == {p \in Procs : IdOf(p) \in Survivors /\ p # ReusedProc}
ReplacementProcs == {p \in Procs : IdOf(p) \in Replacements}

FenceSet(named) ==
    IF FenceRule = "AllOld" \/ named = {} THEN OldVoters \ NewVoters ELSE named

Recover ==
    /\ AllowRecovery /\ ~recovered /\ catUp
    \* allows_recovery: no other old voter answers the operator, who reaches
    \* the keepers on the catalog's side; the survivors are stopped.
    /\ \A p \in Procs : (IdOf(p) \in OldVoters \ Survivors) => ~(alive[p] /\ side[p] = side[Cat])
    /\ \A p \in SurvivorProcs \cup ReplacementProcs : alive[p] /\ side[p] = side[Cat]
    /\ \A p \in SurvivorProcs : copy[p] /\ Config(p) = OldVoters
    /\ LET src == CHOOSE s \in SurvivorProcs :
                     \A s2 \in SurvivorProcs : UpToDate(log[s], log[s2])
           tRec == MaxOf({Max(term[s], LastTerm(log[s])) : s \in SurvivorProcs}) + RecoveryGap
           hist == Append(log[src], RecE(tRec, NewVoters, cfgEpoch + 1))
       IN /\ Len(hist) <= MaxLogLen
          /\ log' = [p \in Procs |->
                       IF p \in SurvivorProcs THEN hist
                       ELSE IF p \in ReplacementProcs THEN <<>> ELSE log[p]]
          /\ term' = [p \in Procs |->
                        IF p \in SurvivorProcs THEN tRec
                        ELSE IF p \in ReplacementProcs THEN 0 ELSE term[p]]
          /\ votedFor' = [p \in Procs |->
                            IF p \in SurvivorProcs THEN IdOf(src)
                            ELSE IF p \in ReplacementProcs THEN Nil ELSE votedFor[p]]
          /\ commit' = [p \in Procs |->
                          IF p \in SurvivorProcs THEN commit[src]
                          ELSE IF p \in ReplacementProcs THEN 0 ELSE commit[p]]
          /\ copy' = [p \in Procs |-> IF p \in ReplacementProcs THEN TRUE ELSE copy[p]]
          /\ role' = [p \in Procs |->
                        IF p \in SurvivorProcs \cup ReplacementProcs THEN "Follower" ELSE role[p]]
          /\ votes' = [p \in Procs |->
                         IF p \in SurvivorProcs \cup ReplacementProcs THEN {} ELSE votes[p]]
          \* The survivors were stopped: they come back without a lease.
          /\ lease' = [p \in Procs |-> IF p \in SurvivorProcs THEN NoLease ELSE lease[p]]
          /\ wait' = IF WaitOut THEN RunWait ELSE wait
          /\ \E named \in SUBSET (Ids \ NewVoters), dead \in BOOLEAN :
                /\ catFenced' = [k \in Ids |-> catFenced[k] \/ k \in FenceSet(named)]
                /\ catEpoch' = [k \in Ids |-> IF dead /\ k \in named THEN catEpoch[k] + 1
                                              ELSE catEpoch[k]]
          /\ catMembers' = NewVoters
          /\ cfgEpoch' = cfgEpoch + 1
          /\ recovered' = TRUE
          /\ survHist' = hist
          /\ recTerm' = tRec
          /\ lostIds' = OldVoters \ NewVoters
          /\ reportedHead' = HeadLsn(hist)
    /\ UNCHANGED <<netVars, alive, myEpoch>>
    /\ UNCHANGED <<appendCount, committedOld, committedNew, leaders, newSeen, newObs, mixed>>

-----------------------------------------------------------------------------
(* Specification *)

Next ==
    \/ \E c \in Procs : Campaign(c)
    \/ \E v, c \in Procs : Vote(v, c)
    \/ \E l, f \in Procs : LearnHigherTerm(l, f)
    \/ \E c \in Procs : BecomeLeader(c)
    \/ \E l \in Procs : StepDown(l)
    \/ \E l \in Procs : ClientAppend(l)
    \/ \E l, f \in Procs : Replicate(l, f)
    \/ \E l \in Procs : Commit(l)
    \/ \E p \in Procs : Read(p)
    \/ RealTick
    \/ \E p \in Procs : LocalTick(p)
    \/ WaitTick
    \/ \E p \in Procs : Renew(p)
    \/ Repartition
    \/ CatalogDown
    \/ \E p \in Procs : Stop(p)
    \/ Reincarnate
    \/ Recover

\* The pre-recovery cut: a lost voter leads the old voters at term 2 and
\* committed v1 with the other lost voter while the survivors, at term 1,
\* were cut off.
\* Every keeper holds a fresh lease. The lost voters sit on side 2, away from
\* the survivors, the replacements and the catalog.
FirstLost == IF OldVoters \ Survivors # {} THEN CHOOSE k \in OldVoters \ Survivors : TRUE
             ELSE CHOOSE k \in OldVoters : TRUE

Init ==
    LET v1 == AppE(2, 1, 1)
        oldLog == <<CfgE(0, OldVoters)>>
        lostLog == <<CfgE(0, OldVoters), BlankE(2, FirstLost), v1>>
        isLost(p) == IdOf(p) \in OldVoters \ Survivors
    IN /\ side = [n \in Nodes |-> IF n \in Procs /\ isLost(n) THEN 2 ELSE 1]
       /\ catUp = TRUE
       /\ partChanges = 0
       /\ alive = [p \in Procs |-> p # ReusedProc]
       /\ copy = [p \in Procs |-> IdOf(p) \in OldVoters /\ p # ReusedProc]
       /\ term = [p \in Procs |-> IF isLost(p) THEN 2
                                 ELSE IF IdOf(p) \in OldVoters /\ p # ReusedProc THEN 1 ELSE 0]
       /\ votedFor = [p \in Procs |-> IF IdOf(p) \in OldVoters /\ p # ReusedProc THEN FirstLost ELSE Nil]
       /\ log = [p \in Procs |->
                   IF p = ReusedProc THEN <<>>
                   ELSE IF isLost(p) THEN lostLog
                   ELSE IF IdOf(p) \in OldVoters THEN oldLog ELSE <<>>]
       /\ commit = [p \in Procs |-> IF p = FirstLost THEN 3 ELSE 0]
       /\ role = [p \in Procs |-> IF p = FirstLost THEN "Leader" ELSE "Follower"]
       /\ votes = [p \in Procs |-> {}]
       /\ lease = [p \in Procs |-> IF p = ReusedProc \/ p \notin LeasedProcs THEN NoLease
                                    ELSE [on |-> TRUE, le |-> 0, d |-> 0, epoch |-> 0, fenced |-> FALSE]]
       /\ wait = NoWait
       /\ myEpoch = [p \in Procs |-> 0]
       /\ catEpoch = [k \in Ids |-> 0]
       /\ catFenced = [k \in Ids |-> FALSE]
       /\ catMembers = OldVoters
       /\ cfgEpoch = 0
       /\ recovered = FALSE
       /\ survHist = <<>>
       /\ recTerm = 0
       /\ lostIds = {}
       /\ reportedHead = 0
       /\ appendCount = 1
       /\ committedOld = {[app |-> [lsn |-> 1, val |-> 1, term |-> 2], cterm |-> 2]}
       /\ committedNew = {}
       /\ leaders = {[term |-> 2, id |-> FirstLost, world |-> FALSE]}
       /\ newSeen = FALSE
       /\ newObs = <<>>
       /\ mixed = FALSE

Spec == Init /\ [][Next]_vars

\* The reuse cut: no recovery. Keepers k1 and k3 hold the committed v1, k2
\* lags, and k3's ID is about to be reused on new media.
InitReuse ==
    LET v1 == AppE(1, 1, 1)
        k1 == CHOOSE k \in OldVoters : k # ReusedId
        full == <<CfgE(0, OldVoters), BlankE(1, k1), v1>>
        lagging(p) == p # k1 /\ IdOf(p) # ReusedId
    IN /\ side = [n \in Nodes |-> 1]
       /\ catUp = TRUE
       /\ partChanges = 0
       /\ alive = [p \in Procs |-> p # ReusedProc]
       /\ copy = [p \in Procs |-> p # ReusedProc]
       /\ term = [p \in Procs |-> IF p = ReusedProc THEN 0 ELSE 1]
       /\ votedFor = [p \in Procs |-> IF p = ReusedProc THEN Nil ELSE k1]
       /\ log = [p \in Procs |->
                   IF p = ReusedProc THEN <<>>
                   ELSE IF lagging(p) THEN <<CfgE(0, OldVoters)>> ELSE full]
       /\ commit = [p \in Procs |-> IF p = k1 THEN 3 ELSE 0]
       /\ role = [p \in Procs |-> IF p = k1 THEN "Leader" ELSE "Follower"]
       /\ votes = [p \in Procs |-> {}]
       /\ lease = [p \in Procs |-> IF p = ReusedProc \/ p \notin LeasedProcs THEN NoLease
                                    ELSE [on |-> TRUE, le |-> 0, d |-> 0, epoch |-> 0, fenced |-> FALSE]]
       /\ wait = NoWait
       /\ myEpoch = [p \in Procs |-> 0]
       /\ catEpoch = [k \in Ids |-> 0]
       /\ catFenced = [k \in Ids |-> FALSE]
       /\ catMembers = OldVoters
       /\ cfgEpoch = 0
       /\ recovered = FALSE
       /\ survHist = <<>>
       /\ recTerm = 0
       /\ lostIds = {}
       /\ reportedHead = 0
       /\ appendCount = 1
       /\ committedOld = {[app |-> [lsn |-> 1, val |-> 1, term |-> 1], cterm |-> 1]}
       /\ committedNew = {}
       /\ leaders = {[term |-> 1, id |-> k1, world |-> FALSE]}
       /\ newSeen = FALSE
       /\ newObs = <<>>
       /\ mixed = FALSE

ReuseSpec == InitReuse /\ [][Next]_vars

\* The loss-point cut: the survivor led term 2, committed v1 with both
\* others, then wrote x at LSN 2 that it never committed before it was cut
\* off from the other two.
InitLossCut ==
    LET surv == CHOOSE k \in Survivors : TRUE
        v1 == AppE(2, 1, 1)
        x == AppE(2, 2, 2)
        shared == <<CfgE(0, OldVoters), BlankE(2, surv), v1>>
        isLost(p) == IdOf(p) \in OldVoters \ Survivors
    IN /\ side = [n \in Nodes |-> IF n \in Procs /\ isLost(n) THEN 2 ELSE 1]
       /\ catUp = TRUE
       /\ partChanges = 0
       /\ alive = [p \in Procs |-> TRUE]
       /\ copy = [p \in Procs |-> IdOf(p) \in OldVoters]
       /\ term = [p \in Procs |-> IF IdOf(p) \in OldVoters THEN 2 ELSE 0]
       /\ votedFor = [p \in Procs |-> IF IdOf(p) \in OldVoters THEN surv ELSE Nil]
       /\ log = [p \in Procs |->
                   IF p = surv THEN Append(shared, x)
                   ELSE IF IdOf(p) \in OldVoters THEN shared ELSE <<>>]
       /\ commit = [p \in Procs |-> IF IdOf(p) \in OldVoters THEN 3 ELSE 0]
       /\ role = [p \in Procs |-> "Follower"]
       /\ votes = [p \in Procs |-> {}]
       /\ lease = [p \in Procs |-> NoLease]
       /\ wait = NoWait
       /\ myEpoch = [p \in Procs |-> 0]
       /\ catEpoch = [k \in Ids |-> 0]
       /\ catFenced = [k \in Ids |-> FALSE]
       /\ catMembers = OldVoters
       /\ cfgEpoch = 0
       /\ recovered = FALSE
       /\ survHist = <<>>
       /\ recTerm = 0
       /\ lostIds = {}
       /\ reportedHead = 0
       /\ appendCount = 2
       /\ committedOld = {[app |-> [lsn |-> 1, val |-> 1, term |-> 2], cterm |-> 2]}
       /\ committedNew = {}
       /\ leaders = {[term |-> 2, id |-> surv, world |-> FALSE]}
       /\ newSeen = FALSE
       /\ newObs = <<>>
       /\ mixed = FALSE

LossSpec == InitLossCut /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties *)

\* No read of a history the recovery did not keep after a read of the
\* recovered history, and every recovered read is a prefix of one log.
NoMixedHistory == ~mixed

\* Every gated leader holds every record of its world committed in an
\* earlier term (leader completeness). The recovered world keeps the survivors' history
\* (the records it held, committed or not) and loses the old world's other
\* commits: the acknowledged loss. Lost voters' commits during the wait-out
\* are part of that loss.
CommittedEntriesPreserved ==
    \A l \in Procs :
        (role[l] = "Leader" /\ Gate(l)) =>
            IF NewWorld(log[l])
            THEN /\ \A c \in committedNew : c.cterm < term[l] => c.app \in Apps(log[l])
                 /\ \A c \in committedOld : c.app \in Apps(survHist) => c.app \in Apps(log[l])
            ELSE \A c \in committedOld : c.cterm < term[l] => c.app \in Apps(log[l])

\* At most one leader per term in each world. The two worlds may reuse
\* terms when the recovery gap is small; no record crosses between them.
ElectionSafety ==
    \A x, y \in leaders : (x.term = y.term /\ x.world = y.world) => x.id = y.id

\* Log matching within the recovered world.
NewWorldLogMatching ==
    \A a, b \in Procs :
        (NewWorld(log[a]) /\ NewWorld(log[b])) =>
            \A i \in 1..Min(Len(log[a]), Len(log[b])) :
                log[a][i].term = log[b][i].term => SubSeq(log[a], 1, i) = SubSeq(log[b], 1, i)

\* The reported loss point is exact: every lost commit lies above the head
\* the recovery reported, so a head comparison finds the whole loss.
LossAboveReportedHead ==
    recovered => \A c \in committedOld : c.app \notin Apps(survHist) => c.app.lsn > reportedHead

\* One recovery record: the catalog's configuration epoch moved once, and the
\* survivors' recovery entry is the first entry of that epoch in every log of
\* the recovered world.
OneRecoveryRecord ==
    /\ cfgEpoch = IF recovered THEN 1 ELSE 0
    /\ recovered =>
        /\ survHist[Len(survHist)].kind = "Rec"
        /\ survHist[Len(survHist)].val = cfgEpoch
        /\ \A p \in Procs : NewWorld(log[p]) =>
              \A i \in 1..Len(log[p]) : log[p][i].kind = "Rec" => i = Len(survHist)

Safety == NoMixedHistory /\ CommittedEntriesPreserved /\ ElectionSafety /\ NewWorldLogMatching

TypeOK ==
    /\ \A p \in Procs : lease[p].le \in 0..L /\ lease[p].d \in -D..D
    /\ wait.st \in {"none", "run", "done"} /\ wait.le \in 0..(L + M) /\ wait.d \in -D..D

-----------------------------------------------------------------------------
(* Liveness: a catalog outage makes leadership lapse *)

NoLeader == \A p \in Procs : role[p] # "Leader"

OutageFairness ==
    /\ WF_vars(RealTick)
    /\ \A p \in Procs : WF_vars(LocalTick(p))
    /\ WF_vars(WaitTick)
    /\ \A p \in Procs : WF_vars(StepDown(p) /\ ~Gate(p))

FairSpec == Spec /\ OutageFairness

\* Once the catalog is down for good, eventually no keeper leads, ever again.
LeadershipLapses == (~catUp) ~> []NoLeader

Symmetry == Permutations(OldVoters \ (Survivors \cup {FirstLost})) \cup Permutations(Replacements)

=============================================================================
