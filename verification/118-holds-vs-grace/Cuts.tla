-------------------------------- MODULE Cuts --------------------------------
EXTENDS Naturals
CONSTANTS Mode, Request, Fault
VARIABLES latest, basis, target, status, oldRoot, oldSuffix, child, attempts, result
vars == <<latest, basis, target, status, oldRoot, oldSuffix, child, attempts, result>>

Exact == Mode \in {"A", "pin"}
Fixed == Request \in {"named", "fork"}
Held == Exact /\ status = "running" /\ basis = 0

Init ==
  /\ latest = 0 /\ basis = 0 /\ target = 0 /\ status = "idle"
  /\ oldRoot = TRUE /\ oldSuffix = TRUE /\ child = FALSE /\ attempts = 0 /\ result = 2

Begin ==
  /\ status = "idle"
  /\ IF Fixed THEN latest = 0 ELSE TRUE
  /\ basis' = latest /\ target' = latest /\ status' = "running"
  /\ attempts' = 1
  /\ UNCHANGED <<latest, oldRoot, oldSuffix, child, result>>

Publish ==
  /\ status # "idle" /\ latest = 0
  /\ latest' = 1 /\ UNCHANGED <<basis, target, status, oldRoot, oldSuffix, child, attempts, result>>

TrimSuffix ==
  /\ latest = 1 /\ oldSuffix /\ (~Held \/ Fault = "omit-suffix") /\ ~child
  /\ oldSuffix' = FALSE
  /\ UNCHANGED <<latest, basis, target, status, oldRoot, child, attempts, result>>

CollectRoot ==
  /\ latest = 1 /\ oldRoot /\ (~Held \/ Fault = "omit-root") /\ (~child \/ Fault = "ignore-child")
  /\ oldRoot' = FALSE
  /\ UNCHANGED <<latest, basis, target, status, oldSuffix, child, attempts, result>>

Available == basis = 1 \/ (oldRoot /\ oldSuffix)

FreshRetry ==
  /\ status = "running" /\ ~Exact /\ ~Available
  /\ IF Fixed THEN
       /\ status' = "refused" /\ UNCHANGED <<basis, target, attempts>>
     ELSE
       /\ attempts' = 2 /\ UNCHANGED status
       /\ basis' = IF Fault = "stale-retry" THEN basis ELSE latest
       /\ target' = IF Fault = "stale-retry" THEN target ELSE latest
  /\ UNCHANGED <<latest, oldRoot, oldSuffix, child, result>>

Finish ==
  /\ status = "running"
  /\ Available \/ Fault = "retarget"
  /\ result' = IF Fault = "retarget" /\ ~Available THEN latest ELSE basis
  /\ status' = "returned" /\ child' = (Request = "fork")
  /\ UNCHANGED <<latest, basis, target, oldRoot, oldSuffix, attempts>>

Next == Begin \/ Publish \/ TrimSuffix \/ CollectRoot \/ FreshRetry \/ Finish
Spec == Init /\ [][Next]_vars

\* Cut identities also stand for distinguishable, verified fold results.
NoWrongData == status = "returned" => result = target /\ (~Fixed \/ result = 0)
RequestedBasisBacked == (status = "running" /\ basis = 0) => oldRoot /\ oldSuffix
RetryRereadsRoot == attempts = 2 => basis = latest /\ target = latest
ExactNamedService == Fixed => status # "refused"

SawOldCutAfterPublish == ~(status = "returned" /\ latest = 1 /\ result = 0)
ForkBacked == child => oldRoot /\ oldSuffix

SawForkTransfer == ~(child /\ latest = 1 /\ oldRoot /\ oldSuffix)
SawFreshRetry == ~(status = "returned" /\ attempts = 2 /\ result = 1
                   /\ ~oldRoot /\ ~oldSuffix)
SawRefusal == ~(status = "refused" /\ result = 2 /\ ~oldRoot /\ ~oldSuffix)
=============================================================================
