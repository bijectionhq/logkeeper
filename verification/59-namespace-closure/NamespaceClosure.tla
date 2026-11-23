---------------------------- MODULE NamespaceClosure -------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS MaxScope, Width, Variant, Scenario, FastEmpty

Scopes == 1..MaxScope
Slots == 1..Width
Keys == Scopes \X Slots

VARIABLES issued, owner, phase, booked, sent, delivered, guards, armed, closed,
          bodies, auxiliary, proofs, seen
vars == <<issued, owner, phase, booked, sent, delivered, guards, armed, closed,
          bodies, auxiliary, proofs, seen>>

Stalled == Scenario = "stall_seed"
Init ==
    /\ issued = (IF Stalled THEN 1 ELSE 0) /\ owner = issued
    /\ phase = (IF Stalled THEN "provisioning" ELSE "vacant")
    /\ booked = (IF Stalled THEN {1} ELSE {})
    /\ sent = (IF Stalled THEN {<<1, 1>>} ELSE {})
    /\ delivered = {} /\ guards = {} /\ armed = {} /\ closed = {}
    /\ bodies = {} /\ auxiliary = {} /\ proofs = {} /\ seen = [lateArm |-> FALSE, auxiliarySettled |-> {}]

Reserve ==
    /\ owner = 0 /\ booked = {} /\ issued < MaxScope
    /\ issued' = issued + 1 /\ owner' = issued'
    /\ phase' = "provisioning" /\ booked' = {owner'}
    /\ UNCHANGED <<sent, delivered, guards, armed, closed, bodies, auxiliary, proofs, seen>>

Send(key) ==
    /\ phase = "provisioning" /\ key[1] = owner /\ key \notin sent
    /\ sent' = sent \cup {key}
    /\ UNCHANGED <<issued, owner, phase, booked, delivered, guards, armed, closed,
                   bodies, auxiliary, proofs, seen>>

Seed(key) ==
    /\ key \in sent \ guards /\ ~Stalled
    /\ \/ phase = "provisioning" /\ (key[1] = owner \/ Variant = "route_only")
       \/ Variant = "raw_create"
    /\ guards' = guards \cup {key} /\ delivered' = delivered \cup {key}
    /\ UNCHANGED <<issued, owner, phase, booked, sent, armed, closed, bodies, auxiliary, proofs, seen>>

Open ==
    /\ phase = "provisioning"
    /\ \A slot \in Slots : <<owner, slot>> \in guards
    /\ phase' = "open"
    /\ UNCHANGED <<issued, owner, booked, sent, delivered, guards, armed, closed,
                   bodies, auxiliary, proofs, seen>>

Arm(key) ==
    /\ key[1] = owner /\ key \in guards \ (armed \cup bodies \cup closed)
    /\ phase = "open" \/ (Variant = "arm_after_seal" /\ phase = "sealed")
    /\ armed' = armed \cup {key}
    /\ seen' = [seen EXCEPT !.lateArm = (@ \/ phase = "sealed")]
    /\ UNCHANGED <<issued, owner, phase, booked, sent, delivered, guards, closed, bodies, auxiliary, proofs>>

Put(key) ==
    /\ key \in (armed \cap guards) \ closed
    /\ Variant # "late_child" \/ phase = "sealed"
    /\ bodies' = bodies \cup {key} /\ armed' = armed \ {key}
    /\ UNCHANGED <<issued, owner, phase, booked, sent, delivered, guards, closed,
                   auxiliary, proofs, seen>>

IssueAuxiliary(key) ==
    /\ key[1] = owner /\ phase = "open" /\ key \in guards \ auxiliary
    /\ auxiliary' = auxiliary \cup {key}
    /\ UNCHANGED <<issued, owner, phase, booked, sent, delivered, guards, armed, closed, bodies, proofs, seen>>

OldSendsCompleted == sent \cap ({owner} \X Slots) \subseteq delivered

Seal ==
    /\ owner # 0 /\ phase \in {"open", "provisioning"}
    /\ Variant # "wait_for_receipts" \/ OldSendsCompleted
    /\ phase' = "sealed"
    /\ UNCHANGED <<issued, owner, booked, sent, delivered, guards, armed, closed,
                   bodies, auxiliary, proofs, seen>>

CloseChild(key) ==
    /\ phase = "sealed" /\ key[1] = owner /\ key \in guards \ closed
    /\ closed' = closed \cup {key}
    /\ UNCHANGED <<issued, owner, phase, booked, sent, delivered, guards, armed, bodies,
                   auxiliary, proofs, seen>>

DisposeChild(key) ==
    /\ key[1] = owner /\ key \in guards \cap closed
    /\ guards' = guards \ {key} /\ armed' = armed \ {key}
    /\ bodies' = bodies \ {key}
    /\ UNCHANGED <<issued, owner, phase, booked, sent, delivered, closed, auxiliary, proofs, seen>>

SettleAuxiliary(key) ==
    /\ phase = "sealed" /\ key[1] = owner /\ key \in auxiliary
    /\ auxiliary' = auxiliary \ {key}
    /\ seen' = [seen EXCEPT !.auxiliarySettled = @ \cup {key}]
    /\ UNCHANGED <<issued, owner, phase, booked, sent, delivered, guards, armed, closed, bodies, proofs>>

NoLocalGuards == guards \cap ({owner} \X Slots) = {}
NoAuxiliary == auxiliary \cap ({owner} \X Slots) = {}

Finish ==
    /\ owner # 0
    /\ NoLocalGuards
    /\ NoAuxiliary \/ Variant = "ignore_auxiliary"
    /\ phase = "sealed" \/ (FastEmpty /\ phase = "provisioning")
    /\ Variant # "wait_for_receipts" \/ OldSendsCompleted
    /\ proofs' = proofs \cup {owner}
    /\ owner' = 0 /\ phase' = "vacant"
    /\ UNCHANGED <<issued, booked, sent, delivered, guards, armed, closed, bodies, auxiliary, seen>>

ObserveEmpty ==
    /\ Variant = "observation_only" /\ phase = "provisioning" /\ NoLocalGuards
    /\ proofs' = proofs \cup {owner}
    /\ UNCHANGED <<issued, owner, phase, booked, sent, delivered, guards, armed, closed,
                   bodies, auxiliary, seen>>

Refund(scope) ==
    /\ scope \in booked \cap proofs
    /\ booked' = booked \ {scope}
    /\ UNCHANGED <<issued, owner, phase, sent, delivered, guards, armed, closed, bodies, auxiliary, proofs, seen>>

Next ==
    \/ Reserve \/ Open \/ Seal \/ Finish \/ ObserveEmpty
    \/ \E key \in Keys : Send(key) \/ Seed(key) \/ Arm(key) \/ Put(key) \/ IssueAuxiliary(key) \/
                         CloseChild(key) \/ DisposeChild(key) \/ SettleAuxiliary(key)
    \/ \E scope \in Scopes : Refund(scope)

Spec == Init /\ [][Next]_vars
FairClosure == Spec /\ WF_vars(Seal) /\ WF_vars(Finish) /\ WF_vars(Refund(1))
RetirementCompletes == <> (1 \in proofs /\ 1 \notin booked)

ExactGuards == \A key \in guards : key[1] = owner
OnlyPaidWork ==
    /\ owner = 0 \/ owner \in booked
    /\ \A key \in guards \cup armed \cup bodies \cup auxiliary : key[1] \in booked
TerminalNoWork ==
    /\ owner \notin proofs
    /\ \A key \in guards \cup armed \cup bodies \cup auxiliary : key[1] \notin proofs
NoNewArmsAfterSeal == ~seen.lateArm
AllLiveSlotsSeeded == phase = "open" => \A slot \in Slots : <<owner, slot>> \in guards
NeverReuseAfterDelayedSeed ==
    ~(owner = 2 /\ phase = "open" /\ 1 \in proofs /\ 1 \notin booked /\
      <<1, 1>> \in sent \ delivered)
NeverAbortAfterDrain ==
    ~(owner = 0 /\ 1 \in proofs /\ 1 \notin booked /\ <<1, 1>> \in closed \cap seen.auxiliarySettled)
NeverHonorFundedChildAfterSeal ==
    ~(phase = "sealed" /\ <<1, 1>> \in bodies /\ 1 \in booked)
=============================================================================
