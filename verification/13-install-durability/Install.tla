-------------------------------- MODULE Install ------------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS Design, Mutation
VARIABLE state

Voters(revision) == IF revision = 1 THEN {1, 2, 3} ELSE {2, 3, 4}
Zone(member) == IF member = 4 THEN 1 ELSE member

Init ==
    state = [revision |-> 1, copied |-> {}, proof |-> 0, active |-> FALSE,
             source |-> TRUE, online |-> 1..4, wrote_with_old_proof |-> FALSE]

HasCopies(revision) == Cardinality(Voters(revision) \cap state.copied \cap state.online) >= 2

Copy(member) ==
    /\ member \in state.online \ state.copied
    /\ state.source \/ (state.active /\ state.copied \cap Voters(state.revision) \cap state.online # {})
    /\ state' = [state EXCEPT !.copied = @ \cup {member}]

RecordProof ==
    /\ ~state.active
    /\ state.proof # state.revision
    /\ HasCopies(state.revision)
    /\ state' = [state EXCEPT !.proof = state.revision]

Replace ==
    /\ state.revision = 1
    /\ ~(state.active \/ (Design = "registered" /\ state.proof # 0)) \/ HasCopies(2)
    /\ state' = [state EXCEPT !.revision = 2]

Activate ==
    /\ ~state.active
    /\ state.proof # 0
    /\ Design = "registered" \/ state.proof = state.revision \/ Mutation = "stale_proof"
    /\ state' = [state EXCEPT !.active = TRUE,
                              !.wrote_with_old_proof = state.proof # state.revision]

Reclaim(member) ==
    /\ member \in state.copied
    /\ member \notin Voters(state.revision) \/ Mutation = "reclaim_without_invalidation"
    /\ state' = [state EXCEPT !.copied = @ \ {member}]

ReleaseSource ==
    /\ state.active \/ (Mutation = "ack_preparation" /\ state.proof # 0)
    /\ state.source
    /\ state' = [state EXCEPT !.source = FALSE]

Lose(zone) ==
    /\ state.online = 1..4
    /\ state' = [state EXCEPT !.online = {member \in 1..4 : Zone(member) # zone}]

Next ==
    \/ \E member \in 1..4 : Copy(member) \/ Reclaim(member)
    \/ \E zone \in 1..3 : Lose(zone)
    \/ RecordProof \/ Replace \/ Activate \/ ReleaseSource

Spec == Init /\ [][Next]_state

AnyTargetQuorumCanRecover ==
    state.active =>
        \A recovery \in SUBSET (Voters(state.revision) \cap state.online) :
           Cardinality(recovery) >= 2 => recovery \cap state.copied # {}

RetainedByServingSide ==
    state.source \/ (state.active /\ state.copied \cap Voters(state.revision) \cap state.online # {})

StillHasPayload ==
    state.source \/ state.copied \cap Voters(state.revision) \cap state.online # {}

NeverRecertifiesAndReleases ==
    ~(state.revision = 2 /\ state.proof = 2 /\ state.active /\ ~state.source)

NeverCarriesAndReleases ==
    ~(state.revision = 2 /\ state.wrote_with_old_proof /\ ~state.source)
=============================================================================
