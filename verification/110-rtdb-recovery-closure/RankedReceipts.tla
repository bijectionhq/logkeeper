------------------------------ MODULE RankedReceipts ------------------------------
CONSTANTS Policy
VARIABLES phase, sourceOnline, availableReceipts, cut, root, restored

vars == <<phase, sourceOnline, availableReceipts, cut, root, restored>>
Init ==
  /\ phase = "preparing"
  /\ sourceOnline = TRUE
  /\ availableReceipts = "none"
  /\ cut = 0
  /\ root = "unset"
  /\ restored = FALSE

Choose ==
  /\ phase = "preparing"
  /\ phase' = "chosen"
  /\ availableReceipts' = "named"
  /\ cut' = 1
  /\ UNCHANGED <<sourceOnline, root, restored>>

InstallLater ==
  /\ phase = "chosen"
  /\ phase' = "later"
  /\ sourceOnline' = FALSE
  /\ availableReceipts' = IF Policy \in {"carry-position-only", "trust-cut-only"} THEN "none" ELSE availableReceipts
  /\ UNCHANGED <<cut, root, restored>>

Crash ==
  /\ phase = "later"
  /\ phase' = "offline"
  /\ root' \in {"older", "newer"}
  /\ UNCHANGED <<sourceOnline, availableReceipts, cut, restored>>

Reopen ==
  /\ phase = "offline"
  /\ IF Policy = "require-old-publisher" THEN sourceOnline ELSE TRUE
  /\ availableReceipts = "named" \/ Policy = "trust-cut-only"
  /\ phase' = "restored"
  /\ restored' = (availableReceipts = "named")
  /\ UNCHANGED <<sourceOnline, availableReceipts, cut, root>>

Next == Choose \/ InstallLater \/ Crash \/ Reopen
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Choose) /\ WF_vars(InstallLater) /\ WF_vars(Crash) /\ WF_vars(Reopen)
ExactRecoverablePublication == phase = "restored" => restored /\ cut = 1
EventuallyRestores == <>(phase = "restored")
NeverRestoresFromOlder == ~(phase = "restored" /\ root = "older")
NeverRestoresFromNewer == ~(phase = "restored" /\ root = "newer")
===================================================================================
