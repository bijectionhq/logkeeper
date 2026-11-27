----------------------------- MODULE KeeperSafety -----------------------------
EXTENDS Naturals, FiniteSets

\* Shared by the bounded consensus models and the implementation trace model.
\* The trace uses digit tuples for terms because recovery adds 2^32.
RaftVoteLeq(a, b, nil, Less(_, _)) ==
    \/ Less(a.term, b.term)
    \/ (a.term = b.term /\ a.votedFor = nil)
    \/ (a.term = b.term /\ a.votedFor = b.votedFor /\ (~a.committed \/ b.committed))

Majority(holders, voters) ==
    voters # {} /\ 2 * Cardinality(holders \cap voters) > Cardinality(voters)

RemovedVoters(old, target) == old \ target

MatchingParkCut(localVote, leaderVote, localCut, leaderCut) ==
    localVote = leaderVote /\ localCut = leaderCut

CurrentLease(on, holderEpoch, leaseEpoch, fenced) ==
    on /\ holderEpoch = leaseEpoch /\ ~fenced

=============================================================================
