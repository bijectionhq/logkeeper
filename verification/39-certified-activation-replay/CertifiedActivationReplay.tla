------------------------ MODULE CertifiedActivationReplay ------------------------
EXTENDS Naturals, Sequences

CONSTANTS Limit, Variant, Scenario
VARIABLE s

Operations == {"ack", "clean"}
Proofs == {"none", "exact", "foreign"}

Apply(enabled, cleared, operation) ==
    IF enabled /\ operation \notin cleared THEN cleared \cup {operation} ELSE cleared

IssuedEvidence(operation, proof) ==
    CASE proof # "exact" -> TRUE
      [] operation = "ack" -> s.recorded
      [] OTHER ->
           (s.custodian = "fenced" /\ (s.physical # "unverified" \/ Variant = "fence_as_disposition"))
           \/ (Variant = "absence_as_fence" /\ s.custodian = "empty")

Eligible(proof) == proof = "exact" \/ (Variant = "accept_foreign" /\ proof = "foreign")

Init ==
    s = [phase |-> "serving", learned |-> 0, chosen |-> <<>>, installed |-> <<>>,
         cleared |-> {}, recovered |-> {}, recorded |-> FALSE, custodian |-> "empty", queued |-> TRUE,
         currentSource |-> TRUE, currentProvider |-> TRUE, lateDenied |-> FALSE,
         bytes |-> FALSE, physical |-> "unverified", dispositionAtReplay |-> FALSE]

SourceRecords ==
    /\ ~s.recorded
    /\ s' = [s EXCEPT !.recorded = TRUE]

DelayedCopy ==
    /\ s.queued
    /\ s' = [s EXCEPT !.queued = FALSE,
                     !.lateDenied = s.custodian = "fenced",
                     !.bytes = IF s.custodian = "fenced" THEN @ ELSE TRUE,
                     !.custodian = IF @ = "fenced" THEN @ ELSE "held"]

FenceOriginal ==
    /\ s.custodian # "fenced"
    /\ s' = [s EXCEPT !.custodian = "fenced"]

ConfirmDisposition(kind) ==
    /\ s.custodian = "fenced" /\ s.physical = "unverified"
    /\ kind = "absent" \/ s.bytes
    /\ s' = [s EXCEPT !.physical = kind, !.bytes = kind = "charged"]

Choose(operation, proof) ==
    /\ s.phase = "serving" /\ Len(s.chosen) < Limit
    /\ IssuedEvidence(operation, proof)
    /\ LET next == Apply(Eligible(proof), s.cleared, operation)
           alreadyKnown == IF operation = "ack" THEN s.recorded ELSE s.custodian = "fenced"
       IN s' = [s EXCEPT !.chosen = Append(@, [op |-> operation, evidence |-> proof,
                            applied |-> next # s.cleared, factAtOrder |-> alreadyKnown]),
                          !.cleared = next]

Learn ==
    /\ s.phase = "serving" /\ s.learned < Len(s.chosen)
    /\ s' = [s EXCEPT !.learned = Len(s.chosen)]

Seal ==
    /\ s.phase = "serving" /\ Len(s.chosen) > 0
    /\ s' = [s EXCEPT !.phase = "sealed",
                     !.currentSource = Scenario # "disconnected",
                     !.currentProvider = Scenario # "disconnected"]

ReplayEligibility(entry) ==
    CASE Variant = "reread_external" ->
           IF entry.op = "ack" THEN s.recorded ELSE s.physical # "unverified"
      [] Variant = "unavailable_as_absence" ->
           Eligible(entry.evidence) /\ IF entry.op = "ack" THEN s.currentSource ELSE s.currentProvider
      [] OTHER -> Eligible(entry.evidence)

RECURSIVE Replay(_, _)
Replay(log, cleared) ==
    IF Len(log) = 0 THEN [results |-> <<>>, cleared |-> cleared]
    ELSE LET entry == Head(log)
             next == Apply(ReplayEligibility(entry), cleared, entry.op)
             later == Replay(Tail(log), next)
         IN [results |-> <<next # cleared>> \o later.results, cleared |-> later.cleared]

Recover ==
    /\ s.phase = "sealed"
    /\ Variant # "lookup_required" \/ (s.currentSource /\ s.currentProvider)
    /\ LET cut == IF Variant = "learned_only" THEN SubSeq(s.chosen, 1, s.learned) ELSE s.chosen
           replay == Replay(cut, {})
       IN s' = [s EXCEPT !.phase = "installed", !.installed = replay.results,
                         !.recovered = replay.cleared, !.dispositionAtReplay = s.physical # "unverified"]

Next ==
    \/ SourceRecords \/ DelayedCopy \/ FenceOriginal \/ Learn \/ Seal \/ Recover
    \/ \E kind \in {"absent", "charged"} : ConfirmDisposition(kind)
    \/ \E operation \in Operations, proof \in Proofs : Choose(operation, proof)

Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(Recover)

KeepsChosenOutcomes ==
    s.phase = "installed" =>
      s.installed = [i \in 1..Len(s.chosen) |-> s.chosen[i].applied] /\ s.recovered = s.cleared
ChosenCleanupRequiresOriginalFence == "clean" \in s.cleared => s.custodian = "fenced"
ReleasedPlanCannotRegrow == "clean" \in s.cleared => s.custodian # "held"
PresentBytesRemainCharged == ("clean" \in s.cleared /\ s.bytes) => s.physical = "charged"
ChosenAckRequiresSourceRecord == "ack" \in s.cleared => s.recorded
ChosenSuccessHasExactEvidence ==
    \A i \in 1..Len(s.chosen) : s.chosen[i].applied => s.chosen[i].evidence = "exact"

InstallsAfterSeal == (s.phase = "sealed") ~> (s.phase = "installed")

NeverRecoversHiddenCleanupOffline ==
    ~(s.phase = "installed" /\ ~s.currentProvider /\ s.learned < Len(s.chosen) /\ "clean" \in s.recovered)
NeverKeepsOldRefusalAfterFactsChange ==
    ~(s.phase = "installed" /\ Len(s.chosen) = 1 /\ s.chosen[1].op = "clean" /\
      s.chosen[1].evidence = "none" /\ ~s.chosen[1].factAtOrder /\
      s.dispositionAtReplay /\ s.installed = <<FALSE>>)
NeverRejectsQueuedCopyAfterCertifiedCleanup ==
    ~(s.phase = "installed" /\ "clean" \in s.recovered /\ s.lateDenied)
NeverTransfersPhysicalCharge ==
    ~(s.phase = "installed" /\ "clean" \in s.recovered /\ s.bytes /\ s.physical = "charged")
=============================================================================
