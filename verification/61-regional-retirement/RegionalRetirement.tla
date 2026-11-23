----------------------------- MODULE RegionalRetirement ----------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Limit, Variant, Scenario

Streams == {1, 2}
Versions == IF Scenario = "survivor_stalls" THEN {1} ELSE {1, 2}
References == {<<1, 1>>, <<2, 1>>} \cup (IF 2 \in Versions THEN {<<1, 2>>} ELSE {})
Original(s) == IF s = 1 THEN Versions \ {1} ELSE {}
InitialRead == Scenario \in {"survivor_stalls", "protected_survivor"}

VARIABLES retired, refs, loans, owed, issued, keys, fenced, present, charged, done, writes, late
vars == <<retired, refs, loans, owed, issued, keys, fenced, present, charged, done, writes, late>>

Init ==
    /\ retired = {} /\ refs = References
    /\ issued = IF InitialRead THEN 1 ELSE 0
    /\ loans = 1..issued /\ owed = loans
    /\ keys = [id \in 1..Limit |-> IF id = 1 /\ issued = 1 THEN <<2, 1>> ELSE <<0, 0>>]
    /\ fenced = {} /\ present = Versions /\ charged = Versions /\ done = {}
    /\ writes = [s \in Streams |-> 0] /\ late = FALSE

Retire(s) ==
    /\ s \notin retired
    /\ retired' = retired \cup {s}
    /\ UNCHANGED <<refs, loans, owed, issued, keys, fenced, present, charged, done, writes, late>>

Borrow(ref) ==
    /\ Scenario # "survivor_stalls" /\ ref \in refs /\ issued < Limit
    /\ ref[1] \notin retired \/ Variant = "use_stale_root"
    /\ issued' = issued + 1
    /\ keys' = [keys EXCEPT ![issued'] = ref]
    /\ loans' = loans \cup {issued'} /\ owed' = owed \cup {issued'}
    /\ late' = (late \/ ref[1] \in retired)
    /\ UNCHANGED <<retired, refs, fenced, present, charged, done, writes>>

Finish(id) ==
    /\ id \in loans /\ Scenario # "survivor_stalls"
    /\ loans' = loans \ {id} /\ owed' = owed \ {id}
    /\ UNCHANGED <<retired, refs, issued, keys, fenced, present, charged, done, writes, late>>

FinishDuplicate(id, other) ==
    /\ Variant = "finish_by_version"
    /\ id \in (1..issued) \ owed /\ other \in loans /\ keys[id][2] = keys[other][2]
    /\ loans' = loans \ {other}
    /\ UNCHANGED <<retired, refs, owed, issued, keys, fenced, present, charged, done, writes, late>>

Detach(ref) ==
    /\ ref \in refs /\ ref[1] \in retired
    /\ refs' = refs \ {ref}
    /\ UNCHANGED <<retired, loans, owed, issued, keys, fenced, present, charged, done, writes, late>>

Fence(v) ==
    /\ v \in present \ fenced
    /\ \A ref \in refs : ref[2] # v
    /\ \A id \in loans : keys[id][2] # v
    /\ fenced' = fenced \cup {v}
    /\ UNCHANGED <<retired, refs, loans, owed, issued, keys, present, charged, done, writes, late>>

Erase(v) ==
    /\ v \in present \cap fenced
    /\ present' = present \ {v}
    /\ UNCHANGED <<retired, refs, loans, owed, issued, keys, fenced, charged, done, writes, late>>

Refund(v) ==
    /\ v \in charged
    /\ v \in fenced \ present \/ (Variant = "refund_after_stream_close" /\ 1 \in retired)
    /\ charged' = charged \ {v}
    /\ UNCHANGED <<retired, refs, loans, owed, issued, keys, fenced, present, done, writes, late>>

Settle(s) ==
    /\ s \in retired \ done
    /\ \A ref \in refs : ref[1] # s
    /\ \A id \in loans : keys[id][1] # s
    /\ Variant # "wait_for_shared_readers" \/ loans = {}
    /\ present \cap Original(s) = {} \/ Variant = "detach_means_erased"
    /\ done' = done \cup {s}
    /\ UNCHANGED <<retired, refs, loans, owed, issued, keys, fenced, present, charged, writes, late>>

Append(s) ==
    /\ Scenario # "survivor_stalls" /\ s \notin retired
    /\ Cardinality(charged) + writes[1] + writes[2] < 2
    /\ writes' = [writes EXCEPT ![s] = @ + 1]
    /\ UNCHANGED <<retired, refs, loans, owed, issued, keys, fenced, present, charged, done, late>>

Next ==
    \/ \E s \in Streams : Retire(s) \/ Settle(s) \/ Append(s)
    \/ \E ref \in References : Borrow(ref) \/ Detach(ref)
    \/ \E id \in 1..Limit : Finish(id)
    \/ \E id, other \in 1..Limit : FinishDuplicate(id, other)
    \/ \E v \in Versions : Fence(v) \/ Erase(v) \/ Refund(v)

Spec == Init /\ [][Next]_vars
FairSettlement ==
    Spec /\ WF_vars(Retire(1)) /\ WF_vars(Detach(<<1, 1>>)) /\ WF_vars(Settle(1))
RetiredDeploymentSettles == <> (1 \in done)

EachBorrowRecorded == owed = loans
NoNewReadsAfterRetirement == ~late
AllPhysicalWorkCharged ==
    /\ present \subseteq charged
    /\ \A id \in owed : keys[id][2] \in present \cap charged
    /\ \A ref \in refs : ref[2] \in present \cap charged
PointwiseBound == Cardinality(charged) + writes[1] + writes[2] <= 2
ExactSettledScope ==
    \A s \in done :
        /\ s \in retired /\ present \cap Original(s) = {}
        /\ \A id \in owed : keys[id][1] # s
        /\ \A ref \in refs : ref[1] # s
NeverSurvivorUsesReturnedCapacity ==
    ~(1 \in done /\ writes[2] > 0 /\ charged = {1} /\ 1 \in owed /\ keys[1] = <<2, 1>>)
=============================================================================
