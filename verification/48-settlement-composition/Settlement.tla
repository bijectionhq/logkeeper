------------------------------ MODULE Settlement ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Limit, Variant, Scenario
VARIABLE s

Pools == 1..2
Credit(pool) ==
    (IF s.prepared[pool] THEN 1 ELSE 0) + Cardinality({owner \in Pools : s.custody[owner] = pool})
Used(pool) == s.ordinary[pool] + Credit(pool)
MayLand(pool) == s.ticket[pool] = "pending" /\ ~s.providerFence[pool]
NeedsCharge(pool) == s.present[pool] \/ MayLand(pool)
CorrectCustody(pool) == s.custody[pool] = pool
ProviderReachable(pool) == Scenario # "provider_down" \/ pool # 1
EmptyKnown(pool) == pool \in s.verified \/ s.ticket[pool] = "unused"

Init ==
    s = [choice |-> "open", book |-> TRUE, installed |-> FALSE, targetAck |-> FALSE,
         prepared |-> [pool \in Pools |-> FALSE], localFence |-> {},
         providerFence |-> [pool \in Pools |-> FALSE], ticket |-> [pool \in Pools |-> "unused"],
         present |-> [pool \in Pools |-> FALSE], verified |-> {}, custody |-> [pool \in Pools |-> 0],
         receipt |-> {}, acked |-> {}, ordinary |-> [pool \in Pools |-> 0], recovered |-> {},
         landedAfterCompaction |-> {}, queuedAtAbort |-> FALSE, recoveredWithCharge |-> FALSE]

Prepare(pool) ==
    /\ pool \notin s.localFence /\ ~s.prepared[pool] /\ s.custody[pool] = 0
    /\ s.choice = "open" \/ (s.choice = "abort" /\ s.book)
    /\ Used(pool) < Limit
    /\ s' = [s EXCEPT !.prepared[pool] = TRUE]

Issue(pool) ==
    /\ pool \notin s.localFence /\ s.prepared[pool] /\ s.ticket[pool] = "unused"
    /\ s' = [s EXCEPT !.ticket[pool] = "pending"]

Land(pool) ==
    /\ MayLand(pool)
    /\ s' = [s EXCEPT !.ticket[pool] = "done", !.present[pool] = TRUE,
                     !.landedAfterCompaction = IF s.book THEN @ ELSE @ \cup {pool}]

Fill(pool) ==
    /\ Used(pool) < Limit
    /\ s' = [s EXCEPT !.ordinary[pool] = @ + 1]

ChooseAbort ==
    /\ s.choice = "open"
    /\ s' = [s EXCEPT !.choice = "abort",
         !.queuedAtAbort = Scenario = "provider_down" /\ MayLand(1),
         !.prepared = IF Variant = "refund_on_abort" THEN [pool \in Pools |-> FALSE] ELSE @]

ChooseSeal ==
    /\ Scenario # "provider_down" /\ s.choice = "open" /\ \A pool \in Pools : s.prepared[pool]
    /\ s' = [s EXCEPT !.choice = "seal"]

Install ==
    /\ s.choice = "seal" /\ ~s.installed
    /\ s' = [s EXCEPT !.installed = TRUE]

CloseKey(pool) ==
    /\ s.choice = "abort" \/ s.installed
    /\ pool \notin s.localFence
    /\ s' = [s EXCEPT !.localFence = @ \cup {pool}]

FenceWrites(pool) ==
    /\ s.choice = "abort" /\ pool \in s.localFence /\ ProviderReachable(pool) /\ ~s.providerFence[pool]
    /\ s' = [s EXCEPT !.providerFence[pool] = TRUE]

Erase(pool) ==
    /\ s.choice = "abort" /\ pool \in s.localFence /\ ProviderReachable(pool) /\ ~MayLand(pool)
    /\ s.present[pool]
    /\ s' = [s EXCEPT !.present[pool] = FALSE]

VerifyAbsence(pool) ==
    /\ s.choice = "abort" /\ pool \in s.localFence /\ ProviderReachable(pool)
    /\ ~NeedsCharge(pool) /\ pool \notin s.verified
    /\ s' = [s EXCEPT !.verified = @ \cup {pool}]

SettleEmpty(pool) ==
    /\ s.choice = "abort" /\ pool \in s.localFence /\ pool \notin s.receipt
    /\ EmptyKnown(pool) \/ Variant = "fence_only"
    /\ s' = [s EXCEPT !.prepared[pool] = FALSE, !.receipt = @ \cup {pool}]

AdoptDebit(pool, owner) ==
    /\ Variant # "absence_only"
    /\ (s.choice = "abort" /\ ~EmptyKnown(pool)) \/ s.installed
    /\ pool \in s.localFence /\ s.prepared[pool] /\ pool \notin s.receipt
    /\ owner = pool \/ (Variant = "wrong_pool" /\ Used(owner) < Limit)
    /\ s' = [s EXCEPT !.prepared[pool] = FALSE, !.custody[pool] = owner, !.receipt = @ \cup {pool}]

ReleaseCustody(pool) ==
    /\ pool \in s.verified /\ s.custody[pool] # 0
    /\ s' = [s EXCEPT !.custody[pool] = 0]

ApplyReceipt(pool) ==
    /\ pool \in s.receipt /\ pool \notin s.acked
    /\ s' = [s EXCEPT !.acked = @ \cup {pool}]

ApplyTarget ==
    /\ ~s.targetAck /\ (s.choice = "abort" \/ s.installed \/
                           (Variant = "target_before_install" /\ s.choice = "seal"))
    /\ s' = [s EXCEPT !.targetAck = TRUE]

Compact ==
    /\ s.book /\ s.acked = Pools /\ s.targetAck
    /\ s' = [s EXCEPT !.book = FALSE]

Recover(pool) ==
    /\ pool \notin s.recovered
    /\ s' = [s EXCEPT !.recovered = @ \cup {pool},
         !.recoveredWithCharge = @ \/ (Scenario = "provider_down" /\ pool = 1 /\ CorrectCustody(pool) /\
             s.book /\ MayLand(pool)),
         !.custody[pool] = IF Variant = "lose_debit" THEN 0 ELSE @]

Next ==
    \/ ChooseAbort \/ (ChooseSeal \/ Install) \/ ApplyTarget \/ Compact
    \/ \E pool \in Pools :
         Prepare(pool) \/ Issue(pool) \/ Land(pool) \/ Fill(pool) \/ CloseKey(pool) \/ FenceWrites(pool) \/
         Erase(pool) \/ VerifyAbsence(pool) \/ SettleEmpty(pool) \/ ReleaseCustody(pool) \/
         ApplyReceipt(pool) \/ Recover(pool) \/ \E owner \in Pools : AdoptDebit(pool, owner)

Spec == Init /\ [][Next]_s
Fair ==
    /\ Spec /\ WF_s(ApplyTarget) /\ WF_s(Compact)
    /\ \A pool \in Pools :
        WF_s(CloseKey(pool)) /\ WF_s(SettleEmpty(pool)) /\ WF_s(AdoptDebit(pool, pool)) /\
        WF_s(ApplyReceipt(pool))

PoolBounds == \A pool \in Pools : Used(pool) <= Limit
PhysicalWorkIsCharged == \A pool \in Pools : NeedsCharge(pool) => s.prepared[pool] \/ CorrectCustody(pool)
ReceiptSurvivesRecovery == \A pool \in s.receipt :
    pool \in s.localFence /\ ~s.prepared[pool] /\ ((NeedsCharge(pool) \/ s.installed) => CorrectCustody(pool))
TargetEvidenceExact == (s.targetAck /\ s.choice = "seal") => s.installed
ForgetKeepsCharge == ~s.book => \A pool \in Pools : NeedsCharge(pool) => CorrectCustody(pool)
AbortCanSettle == (s.choice = "abort") ~> ~s.book

NeverCompactsWithChargedPendingWrite ==
    ~(~s.book /\ s.queuedAtAbort /\ s.recoveredWithCharge /\ MayLand(1) /\ CorrectCustody(1) /\ Used(1) = Limit)
NeverLateEffectAfterCompaction ==
    ~(1 \in s.landedAfterCompaction /\ s.queuedAtAbort /\ s.recoveredWithCharge /\
      s.present[1] /\ CorrectCustody(1) /\ Used(1) = Limit /\ ~ProviderReachable(1))
NeverCompactsAnInstalledSealAtCapacity ==
    ~(~s.book /\ s.installed /\ \A pool \in Pools : CorrectCustody(pool) /\ Used(pool) = Limit)
=============================================================================
