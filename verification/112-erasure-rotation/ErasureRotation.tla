------------------------------ MODULE ErasureRotation ------------------------------
\* Erasure by journal key-generation rotation at an ordered clean checkpoint (D02).
\* Generation 1 holds the erased history. Generation 2 starts at the rotation cut.
CONSTANT Policy

VARIABLES rotated, slots, suffix, committed, revoked, deadline, recovered, viewRead

vars == <<rotated, slots, suffix, committed, revoked, deadline, recovered, viewRead>>

\* "reference": the grant carries the generation and commit waits for both selectable slots.
\* "commit-at-publication": revoke once the clean root is visible in one slot.
\* "unfenced-generation": the journal admits an old-generation append after the cut.
\* "revoke-holds": erase by revoking the held view immediately at commit.
Init ==
  /\ rotated = FALSE
  /\ slots = <<"old", "old">>
  /\ suffix = {}
  /\ committed = FALSE
  /\ revoked = FALSE
  /\ deadline = FALSE
  /\ recovered = "none"
  /\ viewRead = "none"

\* A new grant with generation 2 orders the rotation cut and the clean root is staged.
Rotate ==
  /\ ~rotated
  /\ rotated' = TRUE
  /\ UNCHANGED <<slots, suffix, committed, revoked, deadline, recovered, viewRead>>

PublishSlot(i) ==
  /\ rotated
  /\ slots[i] = "old"
  /\ slots' = [slots EXCEPT ![i] = "clean"]
  /\ UNCHANGED <<rotated, suffix, committed, revoked, deadline, recovered, viewRead>>

AppendNew ==
  /\ rotated
  /\ 2 \notin suffix
  /\ suffix' = suffix \cup {2}
  /\ UNCHANGED <<rotated, slots, committed, revoked, deadline, recovered, viewRead>>

AppendStale ==
  /\ rotated
  /\ Policy = "unfenced-generation"
  /\ 1 \notin suffix
  /\ suffix' = suffix \cup {1}
  /\ UNCHANGED <<rotated, slots, committed, revoked, deadline, recovered, viewRead>>

CommitErasure ==
  /\ rotated
  /\ ~committed
  /\ IF Policy = "commit-at-publication"
       THEN "clean" \in {slots[1], slots[2]}
       ELSE slots = <<"clean", "clean">>
  /\ committed' = TRUE
  /\ revoked' = (Policy = "revoke-holds")
  /\ UNCHANGED <<rotated, slots, suffix, deadline, recovered, viewRead>>

ExpireDeadline ==
  /\ committed
  /\ ~deadline
  /\ deadline' = TRUE
  /\ revoked' = TRUE
  /\ UNCHANGED <<rotated, slots, suffix, committed, recovered, viewRead>>

\* A view admitted before the erasure reads its held old-generation answer.
ReadHeldView ==
  /\ viewRead = "none"
  /\ viewRead' = IF revoked THEN "erased-under-view" ELSE "answer"
  /\ UNCHANGED <<rotated, slots, suffix, committed, revoked, deadline, recovered>>

\* A crash selects either slot and replays its suffix.
Recover(i) ==
  /\ recovered = "none"
  /\ recovered' =
       IF slots[i] = "old" /\ revoked THEN "unrecoverable"
       ELSE IF slots[i] = "old" /\ committed THEN "resurrected"
       ELSE IF slots[i] = "old" THEN "before-erasure"
       ELSE IF 1 \in suffix /\ revoked THEN "unrecoverable"
       ELSE "clean"
  /\ UNCHANGED <<rotated, slots, suffix, committed, revoked, deadline, viewRead>>

Next == Rotate \/ PublishSlot(1) \/ PublishSlot(2) \/ AppendNew \/ AppendStale \/ CommitErasure
  \/ ExpireDeadline \/ ReadHeldView \/ Recover(1) \/ Recover(2)
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Rotate) /\ WF_vars(PublishSlot(1)) /\ WF_vars(PublishSlot(2))
  /\ WF_vars(CommitErasure) /\ WF_vars(ExpireDeadline)

NoResurrection == recovered # "resurrected"
AlwaysRecoverable == recovered # "unrecoverable"
HeldViewKeptUntilDeadline == viewRead = "erased-under-view" => deadline
EventuallyErased == <>(committed /\ deadline)
CleanRecoveryWitness == ~(committed /\ deadline /\ recovered = "clean")
ErasedViewWitness == viewRead # "erased-under-view"
=====================================================================================
