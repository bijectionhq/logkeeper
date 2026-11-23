---------------------------- MODULE RealizedMove ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Variant

Append == 1
Recovery == 2
Receipts == {1, 2, 3, 4, 5}
Pool(receipt) == IF receipt \in {1, 3} THEN 2 ELSE IF receipt = 5 THEN 3 ELSE 1
Serial(receipt) == IF receipt \in {1, 2, 5} THEN 1 ELSE 2
Footprint(receipt) == IF Pool(receipt) = 2 THEN 2 ELSE 1
Scope(receipt) == receipt
Identity(receipt) == <<Pool(receipt), Serial(receipt)>>
Original == <<Append, Recovery>>
Candidates == {Original, <<3, Recovery>>, <<Append, 4>>}

VARIABLES phase, seal, chosen, available, mounted, alias, physical, paid, disposed, settled, recovered
vars == <<phase, seal, chosen, available, mounted, alias, physical, paid, disposed, settled, recovered>>

Init ==
    /\ phase = "pending" /\ seal = <<>> /\ chosen = <<>>
    /\ available = Original /\ mounted = {}
    /\ alias = 9 /\ physical = 0 /\ paid = Receipts
    /\ disposed = {} /\ settled = {} /\ recovered = FALSE

Verify(vector) ==
    Variant = "pool_totals" \/ (Scope(vector[1]) = Append /\ Scope(vector[2]) = Recovery)

Seal(vector) ==
    /\ phase = "pending" /\ Verify(vector)
    /\ Pool(vector[1]) = 2 /\ Pool(vector[2]) = 1
    /\ Footprint(vector[1]) = 2 /\ Footprint(vector[2]) = 1
    /\ phase' = "sealed" /\ seal' = vector /\ chosen' = vector
    /\ UNCHANGED <<available, mounted, alias, physical, paid, disposed, settled, recovered>>

ReplaceRoute ==
    /\ phase = "sealed" /\ available = Original
    /\ available' = <<3, 4>>
    /\ UNCHANGED <<phase, seal, chosen, mounted, alias, physical, paid, disposed, settled, recovered>>

Recover ==
    /\ phase = "sealed" /\ available # Original /\ ~recovered
    /\ recovered' = TRUE
    /\ seal' = IF Variant = "resolve_again" THEN available ELSE seal
    /\ UNCHANGED <<phase, chosen, available, mounted, alias, physical, paid, disposed, settled>>

Install ==
    /\ phase = "sealed"
    /\ IF Variant = "physical_order" THEN alias < Serial(seal[1]) ELSE alias < 10
    /\ phase' = "installed" /\ mounted' = {seal[1], seal[2]}
    /\ alias' = IF Variant = "physical_order" THEN Serial(seal[1]) ELSE 10
    /\ physical' = seal[1]
    /\ UNCHANGED <<seal, chosen, available, paid, disposed, settled, recovered>>

EligibleCleanup(receipt) ==
    receipt = seal[2] \/ (Variant = "role_blind" /\ receipt \in mounted)

Dispose(receipt) ==
    /\ phase = "installed" /\ (receipt \in {Recovery, 4, 5} \/ EligibleCleanup(receipt))
    /\ receipt \notin disposed
    /\ disposed' = disposed \cup {receipt}
    /\ UNCHANGED <<phase, seal, chosen, available, mounted, alias, physical, paid, settled, recovered>>

Settles(expected, actual) ==
    /\ EligibleCleanup(expected)
    /\ IF Variant = "serial_only" THEN Serial(expected) = Serial(actual)
        ELSE Identity(expected) = Identity(actual)

Cleanup(expected, actual) ==
    /\ phase = "installed" /\ expected \in mounted \ settled /\ actual \in disposed
    /\ Settles(expected, actual)
    /\ paid' = paid \ {expected} /\ settled' = settled \cup {expected}
    /\ UNCHANGED <<phase, seal, chosen, available, mounted, alias, physical, disposed, recovered>>

Next ==
    (\E vector \in Candidates : Seal(vector)) \/ ReplaceRoute \/ Recover \/ Install \/
    (\E receipt \in Receipts : Dispose(receipt)) \/ (\E expected, actual \in Receipts : Cleanup(expected, actual))

Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Seal(Original)) /\ WF_vars(Install)

ExactChosenVector == phase # "pending" => chosen = Original
SealSurvives == phase # "pending" => chosen = seal
ExactInstalledWindow == phase = "installed" => physical = chosen[1] /\ alias = 10
ScopedCleanup ==
    phase = "installed" => physical \in paid /\ settled \subseteq {chosen[2]} /\ settled \subseteq disposed
Installs == <> (phase = "installed")
NeverResumeAndSettle == ~(recovered /\ phase = "installed" /\ settled = {Recovery})
=============================================================================
