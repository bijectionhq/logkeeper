--------------------------- MODULE InventoryRecovery --------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Limit, Variant, Scenario

Voters == 1..3
Empty == "empty"
Issue == "issue"
Attached == "return-with-proof"
Unattached == "return-without-proof"
Commands == IF Scenario = "issuance" THEN {Issue} ELSE {Issue, Attached, Unattached}
Initial == [issued |-> 1, eligible |-> FALSE]

VARIABLES chosen, candidate, votes, learned, inventory, stable, visible, evidence,
          running, selected, cutoff, crashUsed, resumedFromOlder, lastReceipt, earlyReceipt, observed
vars == <<chosen, candidate, votes, learned, inventory, stable, visible, evidence,
          running, selected, cutoff, crashUsed, resumedFromOlder, lastReceipt, earlyReceipt, observed>>

Apply(value, command) ==
    CASE command = Issue -> [value EXCEPT !.issued = @ + 1]
      [] command = Attached -> [value EXCEPT !.eligible = TRUE]
      [] OTHER -> value

RECURSIVE Replay(_)
Replay(history) ==
    IF Len(history) = 0 THEN Initial ELSE Apply(Replay(SubSeq(history, 1, Len(history) - 1)), history[Len(history)])

Init ==
    /\ chosen = <<>> /\ candidate = Empty /\ votes = {} /\ learned = 0 /\ inventory = Initial
    /\ stable = 0 /\ visible = 0 /\ evidence = FALSE
    /\ running = TRUE /\ selected = 0 /\ cutoff = <<>> /\ crashUsed = FALSE
    /\ resumedFromOlder = FALSE /\ lastReceipt = 0 /\ earlyReceipt = FALSE
    /\ observed = [head |-> <<>>, unlearned |-> FALSE]

EvidenceArrives ==
    /\ ~evidence /\ Scenario # "issuance"
    /\ Scenario # "late_evidence" \/ \E index \in 1..Len(chosen) : chosen[index] = Unattached
    /\ evidence' = TRUE
    /\ UNCHANGED <<chosen, candidate, votes, learned, inventory, stable, visible, running,
                   selected, cutoff, crashUsed, resumedFromOlder, lastReceipt, earlyReceipt, observed>>

Propose(command) ==
    /\ running /\ candidate = Empty /\ Len(chosen) < Limit
    /\ command # Attached \/ evidence
    /\ candidate' = command
    /\ votes' = {}
    /\ UNCHANGED <<chosen, learned, inventory, stable, visible, evidence, running,
                   selected, cutoff, crashUsed, resumedFromOlder, lastReceipt, earlyReceipt, observed>>

DurableVote(voter) ==
    /\ running /\ candidate # Empty /\ voter \notin votes
    /\ IF Cardinality(votes \cup {voter}) >= 2
       THEN /\ chosen' = Append(chosen, candidate)
            /\ candidate' = Empty /\ votes' = {}
       ELSE /\ votes' = votes \cup {voter}
            /\ UNCHANGED <<chosen, candidate>>
    /\ UNCHANGED <<learned, inventory, stable, visible, evidence, running, selected,
                   cutoff, crashUsed, resumedFromOlder, lastReceipt, earlyReceipt, observed>>

Learn ==
    /\ running /\ learned < Len(chosen)
    /\ inventory' = Apply(inventory, chosen[learned + 1])
    /\ learned' = learned + 1
    /\ UNCHANGED <<chosen, candidate, votes, stable, visible, evidence, running,
                   selected, cutoff, crashUsed, resumedFromOlder, lastReceipt, earlyReceipt, observed>>

Reply ==
    /\ running
    /\ \/ learned > 0 /\ learned <= Len(chosen) /\ chosen[learned] = Issue
       \/ Variant = "reply_after_one_vote" /\ candidate = Issue /\ votes # {}
    /\ lastReceipt' = IF Variant = "reply_after_one_vote" /\ candidate = Issue /\ votes # {}
                     THEN inventory.issued + 1 ELSE inventory.issued
    /\ earlyReceipt' = (earlyReceipt \/ lastReceipt' > Replay(chosen).issued)
    /\ UNCHANGED <<chosen, candidate, votes, learned, inventory, stable, visible, evidence,
                   running, selected, cutoff, crashUsed, resumedFromOlder, observed>>

Publish ==
    /\ running /\ learned > visible /\ stable = visible
    /\ visible' = learned
    /\ UNCHANGED <<chosen, candidate, votes, learned, inventory, stable, evidence,
                   running, selected, cutoff, crashUsed, resumedFromOlder, lastReceipt, earlyReceipt, observed>>

Sync ==
    /\ running /\ stable # visible
    /\ stable' = visible
    /\ UNCHANGED <<chosen, candidate, votes, learned, inventory, visible, evidence,
                   running, selected, cutoff, crashUsed, resumedFromOlder, lastReceipt, earlyReceipt, observed>>

Crash(which) ==
    /\ running /\ ~crashUsed /\ which \in {stable, visible}
    /\ running' = FALSE /\ crashUsed' = TRUE /\ selected' = which /\ learned' = which
    /\ inventory' = Replay(SubSeq(chosen, 1, which))
    /\ observed' = [head |-> chosen, unlearned |-> learned < Len(chosen)]
    /\ cutoff' = CASE Variant = "learned_head" -> SubSeq(chosen, 1, learned)
                   [] Variant = "accepted_is_chosen" /\ candidate # Empty /\ votes # {} ->
                       Append(chosen, candidate)
                   [] OTHER -> chosen
    /\ UNCHANGED <<chosen, candidate, votes, stable, visible, evidence, resumedFromOlder,
                   lastReceipt, earlyReceipt>>

ReplayNext ==
    /\ ~running /\ learned < Len(cutoff)
    /\ LET command == cutoff[learned + 1]
       IN inventory' = Apply(inventory, IF Variant = "refresh_evidence" /\ command = Unattached /\ evidence
                                      THEN Attached ELSE command)
    /\ learned' = learned + 1
    /\ UNCHANGED <<chosen, candidate, votes, stable, visible, evidence, running, selected,
                   cutoff, crashUsed, resumedFromOlder, lastReceipt, earlyReceipt, observed>>

Resume ==
    /\ ~running /\ learned = Len(cutoff)
    /\ running' = TRUE
    /\ resumedFromOlder' = (resumedFromOlder \/ (selected = stable /\ stable # visible /\ selected < learned))
    /\ candidate' = Empty /\ votes' = {}
    /\ UNCHANGED <<chosen, learned, inventory, stable, visible, evidence, selected,
                   cutoff, crashUsed, lastReceipt, earlyReceipt, observed>>

Next ==
    \/ EvidenceArrives \/ \E command \in Commands : Propose(command)
    \/ \E voter \in Voters : DurableVote(voter)
    \/ Learn \/ Reply \/ Publish \/ Sync
    \/ \E which \in {stable, visible} : Crash(which)
    \/ ReplayNext \/ Resume

Spec == Init /\ [][Next]_vars

ExactApplied == learned <= Len(chosen) => inventory = Replay(SubSeq(chosen, 1, learned))
NoUnchosenApplication == learned <= Len(chosen)
NoEarlyReceipt == ~earlyReceipt
ResumeAtChosen ==
    running /\ crashUsed => cutoff = observed.head /\ learned >= Len(observed.head)
NeverOldSelectorWithChosenIssue ==
    ~(resumedFromOlder /\ Len(chosen) = 2 /\ learned = 2 /\ inventory.issued = 3)
NeverRecoveredUnlearned ==
    ~(running /\ crashUsed /\ observed.unlearned /\ selected = 0 /\ learned = 1
      /\ inventory.issued = 2 /\ lastReceipt = 2)
NeverAcceptedAgainOnLateEvidence ==
    ~(running /\ crashUsed /\ Len(chosen) = 1 /\ chosen[1] = Unattached /\ learned = 1
      /\ evidence /\ ~inventory.eligible)
=============================================================================
