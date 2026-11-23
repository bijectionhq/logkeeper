---------------------------- MODULE StorageBoundary ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS MaxScope, Capacity, Variant, IncludeStage, KeepVersions

Scopes == 1..MaxScope
VARIABLES issued, owner, phase, payload, paid, prechecked, fenced, retired,
          pendingStage, staged, priorVersions, late
vars == <<issued, owner, phase, payload, paid, prechecked, fenced, retired,
          pendingStage, staged, priorVersions, late>>

Init ==
    /\ issued = 0 /\ owner = 0 /\ phase = "vacant" /\ payload = 0
    /\ paid = {} /\ prechecked = {} /\ fenced = {} /\ retired = {}
    /\ pendingStage = {} /\ staged = {} /\ priorVersions = {} /\ late = FALSE

Arm ==
    /\ owner = 0 /\ phase = "vacant" /\ payload = 0
    /\ issued < MaxScope /\ Cardinality(paid) < Capacity
    /\ issued' = issued + 1 /\ owner' = issued'
    /\ phase' = "armed" /\ paid' = paid \cup {owner'}
    /\ UNCHANGED <<payload, prechecked, fenced, retired, pendingStage, staged, priorVersions, late>>

Check(scope) ==
    /\ Variant = "checked_then_raw" /\ phase = "armed" /\ scope = owner
    /\ prechecked' = prechecked \cup {scope}
    /\ UNCHANGED <<issued, owner, phase, payload, paid, fenced, retired, pendingStage, staged, priorVersions, late>>

Put(scope) ==
    /\ scope \in 1..issued
    /\ \/ phase = "armed" /\ scope = owner
       \/ Variant = "checked_then_raw" /\ scope \in prechecked
       \/ Variant = "absent_grants_creation" /\ owner = 0 /\ payload = 0
       \/ Variant = "content_tag_alias" /\ phase = "armed"
    /\ phase' = IF owner = 0 THEN phase ELSE "written"
    /\ payload' = scope /\ late' = (late \/ scope \in fenced)
    /\ UNCHANGED <<issued, owner, paid, prechecked, fenced, retired, pendingStage, staged, priorVersions>>

Fence ==
    /\ owner # 0 /\ phase \in {"armed", "written"}
    /\ phase' = "fenced" /\ fenced' = fenced \cup {owner}
    /\ UNCHANGED <<issued, owner, payload, paid, prechecked, retired, pendingStage, staged, priorVersions, late>>

Clear ==
    /\ owner # 0 /\ phase = "fenced"
    /\ phase' = "vacant" /\ payload' = 0 /\ owner' = 0
    /\ retired' = retired \cup {owner}
    /\ priorVersions' = IF KeepVersions /\ payload # 0 THEN priorVersions \cup {payload} ELSE priorVersions
    /\ UNCHANGED <<issued, paid, prechecked, fenced, pendingStage, staged, late>>

Restore ==
    /\ Variant = "forget_fence" /\ owner # 0 /\ phase = "fenced"
    /\ phase' = "armed"
    /\ UNCHANGED <<issued, owner, payload, paid, prechecked, fenced, retired,
                   pendingStage, staged, priorVersions, late>>

IssueStage(scope) ==
    /\ IncludeStage /\ phase = "armed" /\ scope = owner /\ scope \notin pendingStage \cup staged
    /\ pendingStage' = pendingStage \cup {scope}
    /\ UNCHANGED <<issued, owner, phase, payload, paid, prechecked, fenced, retired, staged, priorVersions, late>>

UploadStage(scope) ==
    /\ scope \in pendingStage
    /\ Variant # "stage_after_clear" \/ scope # owner
    /\ pendingStage' = pendingStage \ {scope} /\ staged' = staged \cup {scope}
    /\ UNCHANGED <<issued, owner, phase, payload, paid, prechecked, fenced, retired, priorVersions, late>>

SettleStage(scope) ==
    /\ scope \in pendingStage \cup staged
    /\ scope # owner \/ phase = "fenced"
    /\ pendingStage' = pendingStage \ {scope} /\ staged' = staged \ {scope}
    /\ UNCHANGED <<issued, owner, phase, payload, paid, prechecked, fenced, retired, priorVersions, late>>

PurgeVersion(scope) ==
    /\ scope \in priorVersions
    /\ priorVersions' = priorVersions \ {scope}
    /\ UNCHANGED <<issued, owner, phase, payload, paid, prechecked, fenced, retired, pendingStage, staged, late>>

Refund(scope) ==
    /\ scope \in paid /\ scope # owner
    /\ scope \notin pendingStage \cup staged \/ Variant = "ignore_stage"
    /\ scope \notin priorVersions \/ Variant = "ignore_prior_version"
    /\ paid' = paid \ {scope}
    /\ UNCHANGED <<issued, owner, phase, payload, prechecked, fenced, retired,
                   pendingStage, staged, priorVersions, late>>

Next ==
    \/ Arm \/ Fence \/ Clear \/ Restore
    \/ \E scope \in Scopes :
        Check(scope) \/ Put(scope) \/ IssueStage(scope) \/ UploadStage(scope) \/
        SettleStage(scope) \/ PurgeVersion(scope) \/ Refund(scope)

Spec == Init /\ [][Next]_vars

ExactBody == payload = 0 \/ owner = payload
NoWriteAfterFence == ~late
RetiredHasNoBody == payload \notin retired
AllWorkCharged ==
    /\ owner # 0 => owner \in paid
    /\ pendingStage \cup staged \cup priorVersions \subseteq paid
    /\ payload # 0 => payload \in paid
WithinBudget == Cardinality(paid) <= Capacity
NeverReuseWithOldStaging == ~(owner = 2 /\ payload = 2 /\ 1 \in staged /\ 1 \in paid)
NeverReclaimAndReuse == ~(owner = 2 /\ payload = 2 /\ 1 \in retired /\ 1 \notin paid)
NeverReuseWithOldVersion == ~(owner = 2 /\ payload = 2 /\ 1 \in priorVersions /\ 1 \in paid)
=============================================================================
