------------------------------ MODULE Membership ----------------------------
EXTENDS Naturals, FiniteSets, Sequences
CONSTANTS Design, Mutation, MaxLsn
VARIABLE state

Replicas == 1..4
Zones == 1..3
Old == {1, 2, 3}
New == {2, 3, 4}
Zone(replica) == IF replica = 4 THEN 1 ELSE replica

Majority(voters, witnesses) ==
    2 * Cardinality(voters \cap witnesses) > Cardinality(voters)

Init ==
    state = [
        phase |-> "old",
        up |-> Replicas,
        fenced |-> {},
        history |-> <<>>,
        data |-> [replica \in Replicas |-> <<>>],
        metadata_end |-> [replica \in Replicas |-> 0],
        stale_receipt |-> FALSE,
        wrote_joint_after_loss |-> FALSE,
        delayed_receipt |-> FALSE,
        old_end |-> 0
    ]

FullCopy(replica) == state.data[replica] = state.history

CopyPrefix(replica) ==
    /\ replica \in state.up
    /\ ~FullCopy(replica)
    /\ state' = [state EXCEPT !.data[replica] = state.history,
                              !.metadata_end[replica] = Len(state.history)]

CopyMetadata(replica) ==
    /\ replica \in state.up
    /\ state.metadata_end[replica] < Len(state.history)
    /\ state' = [state EXCEPT !.metadata_end[replica] = Len(state.history)]

SubstituteCopy ==
    /\ Mutation = "length_only"
    /\ state.phase # "new"
    /\ 4 \in state.up
    /\ state.data[4] = <<>>
    /\ Len(state.history) > 0
    /\ LET opposite == IF state.history[1] = "A" THEN "B" ELSE "A"
       IN state' = [state EXCEPT !.data[4] = [state.history EXCEPT ![1] = opposite]]

VoteReady(replica) ==
    IF Mutation = "metadata_only"
    THEN state.metadata_end[replica] = Len(state.history)
    ELSE IF Mutation = "length_only"
         THEN Len(state.data[replica]) = Len(state.history)
         ELSE IF Mutation = "reuse_address" /\ replica = 4
              THEN FullCopy(1)
              ELSE FullCopy(replica)

CurrentReady(votes) ==
    /\ votes \subseteq state.up
    /\ \A replica \in votes : FullCopy(replica)

BeginChange(votes) ==
    /\ state.phase = "old"
    /\ votes \subseteq (Old \cap state.up)
    /\ Majority(Old, votes)
    /\ state' = [state EXCEPT !.phase = IF Design = "direct" THEN "new" ELSE Design,
                              !.fenced = IF Design = "direct" THEN {} ELSE votes,
                              !.old_end = Len(state.history)]

AdoptNew(votes) ==
    /\ state.phase \in {"joint", "sealed"}
    /\ votes \subseteq state.up
    /\ Majority(New, votes)
    /\ state.phase = "sealed" \/ Majority(Old, votes)
    /\ \A replica \in (votes \cap New) : VoteReady(replica)
    /\ state' = [state EXCEPT !.phase = "new"]

CommitOld(votes, bytes) ==
    /\ votes \subseteq (Old \cap state.up) \ state.fenced
    /\ Majority(Old, votes)
    /\ IF state.phase # "old"
       THEN /\ ~state.stale_receipt
            /\ state' = [state EXCEPT !.stale_receipt = TRUE]
       ELSE /\ Len(state.history) < MaxLsn
            /\ CurrentReady(votes)
            /\ state' = [state EXCEPT !.history = Append(@, bytes),
                 !.data = [r \in Replicas |-> IF r \in votes THEN Append(@[r], bytes) ELSE @[r]],
                 !.metadata_end = [r \in Replicas |-> IF r \in votes THEN Len(state.history) + 1 ELSE @[r]]]

CommitCurrent(votes, bytes) ==
    /\ state.phase \in {"joint", "new"}
    /\ Len(state.history) < MaxLsn
    /\ CurrentReady(votes)
    /\ Majority(New, votes)
    /\ state.phase = "new" \/ Majority(Old, votes) \/ Mutation = "joint_old_optional"
    /\ state' = [state EXCEPT !.history = Append(@, bytes),
         !.data = [r \in Replicas |-> IF r \in votes THEN Append(@[r], bytes) ELSE @[r]],
         !.metadata_end = [r \in Replicas |-> IF r \in votes THEN Len(state.history) + 1 ELSE @[r]],
         !.wrote_joint_after_loss = @ \/ (state.phase = "joint" /\ state.up # Replicas)]

DeliverOldReceipt ==
    /\ state.phase = "new"
    /\ state.old_end > 0
    /\ ~state.delayed_receipt
    /\ state' = [state EXCEPT !.delayed_receipt = TRUE]

RemoveOldData ==
    /\ state.data[1] # <<>>
    /\ state.phase = "new" \/
        (Mutation = "early_discard" /\ state.phase \in {"joint", "sealed"})
    /\ state' = [state EXCEPT !.data[1] = <<>>]

LoseAz(zone) ==
    /\ state.up = Replicas
    /\ state' = [state EXCEPT !.up = {replica \in Replicas : Zone(replica) # zone}]

Next ==
    \/ \E replica \in Replicas : CopyPrefix(replica) \/ CopyMetadata(replica)
    \/ \E votes \in SUBSET Replicas :
            \/ BeginChange(votes) \/ AdoptNew(votes)
            \/ \E bytes \in {"A", "B"} : CommitOld(votes, bytes) \/ CommitCurrent(votes, bytes)
    \/ \E zone \in Zones : LoseAz(zone)
    \/ RemoveOldData \/ DeliverOldReceipt \/ SubstituteCopy

Spec == Init /\ [][Next]_state

RetainedAt(replica, lsn) ==
    IF lsn <= Len(state.data[replica])
    THEN state.data[replica][lsn] = state.history[lsn]
    ELSE FALSE

ProtectingConfig == IF state.phase = "new" THEN New ELSE Old

QuorumCanRecover ==
    \A lsn \in 1..Len(state.history), votes \in SUBSET (state.up \cap ProtectingConfig) :
        Majority(ProtectingConfig, votes) => \E replica \in votes : RetainedAt(replica, lsn)

SurvivingCopy ==
    \A lsn \in 1..Len(state.history) :
        \E replica \in state.up \cap ProtectingConfig : RetainedAt(replica, lsn)

NoStaleCommit == ~state.stale_receipt

NeverWritesJointAfterLoss ==
    ~(state.phase = "new" /\ state.wrote_joint_after_loss /\ state.delayed_receipt)
=============================================================================
