----------------------------- MODULE Authority -----------------------------
EXTENDS Naturals, TLC

CONSTANT Policy
VARIABLES phase, incarnation, manifest, archive, readers, physical, operation, before, archiveBefore, row, drained
vars == <<phase, incarnation, manifest, archive, readers, physical, operation, before, archiveBefore, row, drained>>

Init ==
  /\ phase = "absent"
  /\ incarnation = 0
  /\ manifest = "none"
  /\ archive = FALSE
  /\ readers = 0
  /\ physical = TRUE
  /\ operation = "init"
  /\ before = "absent"
  /\ archiveBefore = FALSE
  /\ row = FALSE
  /\ drained = FALSE

Install ==
  /\ phase = "absent"
  /\ phase' = "installed"
  /\ incarnation' = 1
  /\ operation' = "install"
  /\ before' = phase
  /\ archiveBefore' = archive
  /\ UNCHANGED <<manifest, archive, readers, physical, row, drained>>

Archive ==
  /\ phase = "installed"
  /\ ~archive
  /\ archive' = TRUE
  /\ operation' = "archive"
  /\ before' = phase
  /\ archiveBefore' = archive
  /\ UNCHANGED <<phase, incarnation, manifest, readers, physical, row, drained>>

Restore ==
  /\ phase = "installed"
  /\ readers = 0
  /\ archive
  /\ manifest = "none"
  /\ manifest' = "certified"
  /\ operation' = "restore"
  /\ before' = phase
  /\ archiveBefore' = archive
  /\ UNCHANGED <<phase, incarnation, archive, readers, physical, row, drained>>

Retire ==
  /\ phase = "installed"
  /\ phase' = "closed"
  /\ operation' = "retire"
  /\ before' = phase
  /\ archiveBefore' = archive
  /\ UNCHANGED <<incarnation, manifest, archive, readers, physical, row, drained>>

Dispose ==
  /\ phase = "closed"
  /\ (readers = 0 \/ Policy = "undrained-disposal")
  /\ physical
  /\ physical' = FALSE
  /\ operation' = "dispose"
  /\ before' = phase
  /\ archiveBefore' = archive
  /\ UNCHANGED <<phase, incarnation, manifest, archive, readers, row, drained>>

Release ==
  /\ readers = 1
  /\ readers' = 0
  /\ operation' = "release"
  /\ drained' = (phase = "closed")
  /\ before' = phase
  /\ archiveBefore' = archive
  /\ UNCHANGED <<phase, incarnation, manifest, archive, physical, row>>

Data(verb) ==
  /\ (phase = "installed"
       \/ (Policy = "self-install" /\ verb = "transact" /\ phase = "absent")
       \/ (Policy = "late-hold" /\ verb = "hold" /\ phase = "closed"))
  /\ (verb # "hold" \/ readers = 0)
  /\ operation' = verb
  /\ before' = phase
  /\ archiveBefore' = archive
  /\ phase' = IF phase = "absent" THEN "installed"
              ELSE IF Policy = "subject-retire" /\ verb = "forget" THEN "closed"
              ELSE phase
  /\ incarnation' = IF phase = "absent" THEN 1 ELSE incarnation
  /\ manifest' = IF Policy = "replace-with-row" /\ verb = "transact" /\ row
                 THEN "row" ELSE manifest
  /\ archive' = (archive \/ (Policy = "row-archive" /\ verb = "transact"))
  /\ readers' = IF verb = "hold" THEN 1 ELSE readers
  /\ row' = IF verb = "transact" THEN TRUE
            ELSE IF verb = "forget" THEN FALSE ELSE row
  /\ UNCHANGED <<physical, drained>>

Next ==
  \/ Install \/ Archive \/ Restore \/ Retire \/ Dispose \/ Release
  \/ \E verb \in {"transact", "read", "subscribe", "hold", "forget"} : Data(verb)

Spec == Init /\ [][Next]_vars

Typed ==
  /\ phase \in {"absent", "installed", "closed"}
  /\ incarnation \in 0..1
  /\ manifest \in {"none", "certified", "row"}
  /\ archive \in BOOLEAN
  /\ archiveBefore \in BOOLEAN
  /\ readers \in 0..1
  /\ physical \in BOOLEAN
  /\ operation \in {"init", "install", "archive", "restore", "retire", "dispose", "release",
                    "transact", "read", "subscribe", "hold", "forget"}
  /\ before \in {"absent", "installed", "closed"}
  /\ row \in BOOLEAN
  /\ drained \in BOOLEAN

InstallRequiresAuthority == operation # "transact" \/ before = "installed"
ArchiveRequiresAuthority == ~archive \/ archiveBefore \/ operation = "archive"
RestoreRequiresEvidence == manifest \in {"none", "certified"}
RetireRequiresAuthority == phase # "closed" \/ before = "closed" \/ operation = "retire"
RetireClosesAdmission == operation # "hold" \/ phase = "installed"
DisposalDrains == physical \/ (phase = "closed" /\ readers = 0)

TerminalWitness == ~(phase = "closed" /\ manifest = "certified" /\ ~physical /\ row /\ drained)
=============================================================================
