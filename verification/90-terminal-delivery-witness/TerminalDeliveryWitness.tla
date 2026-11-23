----------------------- MODULE TerminalDeliveryWitness -----------------------
EXTENDS Naturals

CONSTANT Variant, Scenario

VARIABLES phase, extent, stopped, observed, durable, provider, source,
          installedRows, rows, replied, recovered, settled

vars == <<phase, extent, stopped, observed, durable, provider, source,
          installedRows, rows, replied, recovered, settled>>

Original == [lineage |-> 1, slot |-> 0, serial |-> 2, pool |-> 8, borrow |-> 3]
OldReceipt == [Original EXCEPT !.serial = 1]
OtherPool == [Original EXCEPT !.pool = 9]
OtherLineage == [Original EXCEPT !.lineage = 2]
NoRows == {}
SealedRows == IF Scenario = "shared-delivery" THEN {0, 1} ELSE {0}

Init ==
  /\ phase = "prepared"
  /\ extent = TRUE
  /\ stopped = FALSE
  /\ observed = "absent"
  /\ durable = "absent"
  /\ provider = TRUE
  /\ source = TRUE
  /\ installedRows = NoRows
  /\ rows = NoRows
  /\ replied = FALSE
  /\ recovered = FALSE
  /\ settled = FALSE

Seal ==
  /\ phase = "prepared"
  /\ phase' = "sealed"
  /\ UNCHANGED <<extent, stopped, observed, durable, provider, source,
                 installedRows, rows, replied, recovered, settled>>

LoseSource ==
  /\ phase = "sealed"
  /\ phase' = "source-offline"
  /\ source' = FALSE
  /\ UNCHANGED <<extent, stopped, observed, durable, provider,
                 installedRows, rows, replied, recovered, settled>>

CustodyChanges ==
  /\ phase = "source-offline"
  /\ phase' = "provider-outcome"
  /\ stopped' = (Scenario # "live")
  /\ extent' = (Scenario \in {"live", "stopped-with-media", "uncovered-old-base", "covered-old-base"})
  /\ UNCHANGED <<observed, durable, provider, source,
                 installedRows, rows, replied, recovered, settled>>

StageReceipt ==
  /\ phase = "provider-outcome"
  /\ phase' = "receipt-staged"
  /\ observed' = CASE Scenario = "stale-slot" -> "old-serial"
                    [] Scenario = "other-pool" -> "other-pool"
                    [] Scenario = "other-lineage" -> "other-lineage"
                    [] Scenario \in {"no-proof", "live"} -> "absent"
                    [] OTHER -> "exact"
  /\ durable' = IF Scenario = "volatile" THEN "absent" ELSE observed'
  /\ UNCHANGED <<extent, stopped, provider, source, installedRows, rows, replied, recovered, settled>>

LoseProvider ==
  /\ phase = "receipt-staged"
  /\ phase' = "provider-offline"
  /\ provider' = FALSE
  /\ UNCHANGED <<extent, stopped, observed, durable, source, installedRows, rows, replied, recovered, settled>>

Identity(receipt) ==
  CASE receipt = "exact" -> Original
    [] receipt = "old-serial" -> OldReceipt
    [] receipt = "other-pool" -> OtherPool
    [] receipt = "other-lineage" -> OtherLineage
    [] OTHER -> [lineage |-> 0, slot |-> 0, serial |-> 0, pool |-> 0, borrow |-> 0]

ExactReceipt ==
  LET receipt == IF Variant = "volatile-is-durable" THEN observed ELSE durable
      identity == Identity(receipt)
  IN /\ receipt # "absent"
     /\ IF Variant = "slot-only" THEN identity.slot = Original.slot ELSE identity = Original

OtherNeed == Scenario \in {"shared-read", "shared-replay", "shared-delivery"}

Supported ==
  extent \/
    (/\ Variant # "require-original-extent"
     /\ ExactReceipt
     /\ (~OtherNeed \/ Variant = "ignore-other-owner")
     /\ (Variant # "recontact-provider" \/ provider))

OlderSelectable == Scenario \in {"uncovered-old-base", "covered-old-base"}
OlderPathHasReceipt == Scenario = "covered-old-base"

DisposeOriginal ==
  /\ phase = "provider-offline"
  /\ OlderSelectable
  /\ extent
  /\ durable = "exact"
  /\ (OlderPathHasReceipt \/ Variant = "visible-only-reclaim")
  /\ extent' = FALSE
  /\ UNCHANGED <<phase, stopped, observed, durable, provider, source,
                 installedRows, rows, replied, recovered, settled>>

Activate ==
  /\ phase = "provider-offline"
  /\ Supported
  /\ phase' = "active"
  /\ installedRows' = IF Variant = "erase-at-mount" /\ ExactReceipt THEN NoRows ELSE SealedRows
  /\ rows' = installedRows'
  /\ UNCHANGED <<extent, stopped, observed, durable, provider, source, replied, recovered, settled>>

TryFinish ==
  /\ phase = "active"
  /\ phase' = "tested-effect"
  /\ replied' = (0 \in rows /\ ((extent /\ ~stopped) \/ (Variant = "receipt-authorizes-use" /\ ExactReceipt)))
  /\ UNCHANGED <<extent, stopped, observed, durable, provider, source, installedRows, rows, recovered, settled>>

CrashAndReopen ==
  /\ phase = "tested-effect"
  /\ phase' = "reopened"
  /\ observed' = "absent"
  /\ recovered' = (extent \/ (durable = "exact" /\ ~OtherNeed))
  /\ UNCHANGED <<extent, stopped, durable, provider, source, installedRows, rows, replied, settled>>

Settle ==
  /\ phase = "reopened"
  /\ recovered
  /\ durable = "exact"
  /\ phase' = "settled"
  /\ rows' = rows \ {0}
  /\ settled' = TRUE
  /\ UNCHANGED <<extent, stopped, observed, durable, provider, source, installedRows, replied, recovered>>

Installed == phase \in {"active", "tested-effect", "reopened", "settled"}
Justified == Installed => extent \/ durable = "exact"
ProtectsOtherOwners == (Installed /\ OtherNeed) => extent
PreservesSealedBook == Installed => installedRows = SealedRows
NoStoppedReply == replied => ~stopped
Reopens == phase \in {"reopened", "settled"} => recovered
KeepsSelectableBasis == OlderSelectable => extent \/ OlderPathHasReceipt
SettlesExactly == settled => rows = (SealedRows \ {0})
FinishesWithoutOldRoutes == <> (settled /\ recovered /\ ~source /\ ~provider /\ ~extent)
RecoversLiveAndReplies == <> (recovered /\ replied)
StopsWithMedia == <> (settled /\ recovered /\ ~replied /\ extent)

Next == Seal \/ LoseSource \/ CustodyChanges \/ StageReceipt \/ LoseProvider \/ DisposeOriginal \/ Activate \/
        TryFinish \/ CrashAndReopen \/ Settle
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Next)

=============================================================================
