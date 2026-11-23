------------------------------ MODULE MaintenanceLane ------------------------------
\* Maintenance reserve between checkpoints under repeated writer replacement.
\* "per-term-claim": RTDB appends a maintenance claim (and confirmation) for every term.
\* "grant-fenced": the Logkeeper grant fences terms; only the boundary and upload are maintenance.
\* "grant-unfenced": like grant-fenced, but the journal admits appends from a superseded grant.
EXTENDS Naturals
CONSTANTS Policy, Reserve, MaxCrashes

VARIABLES used, phase, holder, grant, crashes, checkpoints, blockOwner, uploads, claimed, tail

vars == <<used, phase, holder, grant, crashes, checkpoints, blockOwner, uploads, claimed, tail>>

PerTerm == Policy = "per-term-claim"
Fenced == Policy # "grant-unfenced"

Init ==
  /\ used = 1            \* the retained previous upload
  /\ phase = "idle"
  /\ holder = 1
  /\ grant = 1
  /\ crashes = 0
  /\ checkpoints = 0
  /\ blockOwner = 0
  /\ uploads = 0
  /\ claimed = TRUE
  /\ tail = 0

Room(n) == used + n <= Reserve

\* A crash installs a new grant. The per-term design must then append a claim
\* before the new holder can write anything else.
Regrant ==
  /\ crashes < MaxCrashes
  /\ crashes' = crashes + 1
  /\ grant' = grant + 1
  /\ holder' = grant + 1
  /\ claimed' = ~PerTerm
  /\ UNCHANGED <<used, phase, checkpoints, blockOwner, uploads, tail>>

Claim ==
  /\ ~claimed
  /\ Room(1)
  /\ used' = used + 1
  /\ claimed' = TRUE
  \* A claim after the upload follows the next checkpoint's cut and survives its trim.
  /\ tail' = IF phase = "uploaded" THEN tail + 1 ELSE tail
  /\ UNCHANGED <<phase, holder, grant, crashes, checkpoints, blockOwner, uploads>>

Boundary ==
  /\ claimed
  /\ phase = "idle"
  /\ Room(1)
  /\ used' = used + 1
  /\ phase' = "boundary"
  /\ blockOwner' = holder
  /\ UNCHANGED <<holder, grant, crashes, checkpoints, uploads, claimed, tail>>

\* The current holder uploads the pending block once, after replaying through its grant.
Upload ==
  /\ claimed
  /\ phase = "boundary"
  /\ Room(1)
  /\ used' = used + 1
  /\ phase' = "uploaded"
  /\ uploads' = uploads + 1
  /\ UNCHANGED <<holder, grant, crashes, checkpoints, blockOwner, claimed, tail>>

\* A superseded holder that never learned of its replacement retries its own upload.
StaleUpload ==
  /\ ~Fenced
  /\ phase = "uploaded"
  /\ blockOwner # grant
  /\ uploads = 1
  /\ Room(1)
  /\ used' = used + 1
  /\ uploads' = 2
  /\ tail' = tail + 1
  /\ UNCHANGED <<phase, holder, grant, crashes, checkpoints, blockOwner, claimed>>

\* The custodian publishes the uploaded root and trims through its cut,
\* keeping the upload record that follows the cut.
PublishAndTrim ==
  /\ phase = "uploaded"
  /\ checkpoints < 2
  /\ used' = 1 + tail
  /\ tail' = 0
  /\ phase' = "idle"
  /\ checkpoints' = checkpoints + 1
  /\ uploads' = 0
  /\ UNCHANGED <<holder, grant, crashes, blockOwner, claimed>>

Next == Regrant \/ Claim \/ Boundary \/ Upload \/ StaleUpload \/ PublishAndTrim
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Claim) /\ WF_vars(Boundary) /\ WF_vars(Upload) /\ WF_vars(PublishAndTrim)

WithinReserve == used <= Reserve
\* Some progress action stays enabled whenever no checkpoint is in hand.
ProgressHeadroom ==
  \/ (~claimed /\ phase = "idle" /\ used + 3 <= Reserve)
  \/ (~claimed /\ phase = "boundary" /\ used + 2 <= Reserve)
  \/ (~claimed /\ phase = "uploaded" /\ used + 1 <= Reserve)
  \/ (claimed /\ phase = "uploaded")
  \/ (claimed /\ phase = "idle" /\ used + 2 <= Reserve)
  \/ (claimed /\ phase = "boundary" /\ used + 1 <= Reserve)
OneUploadPerBlock == uploads <= 1
EventuallyCheckpoints == <>(checkpoints >= 2)
=====================================================================================
