------------------------------ MODULE DurableRoot ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Limit, Variant

Scopes == {1, 2}
None == <<0, 0>>
Retire == 1
Create == 2
Register == 3
Requests == {Retire, Create, Register} \X Scopes
Initial == [issued |-> 1, open |-> TRUE, guard |-> FALSE]

VARIABLES visible, stable, memory, durable, staged, bytesStable, nameStable,
          applied, root, serving, crashed, chosenSelector, receipts, refusedOld, observedAtCrash
vars == <<visible, stable, memory, durable, staged, bytesStable, nameStable,
          applied, root, serving, crashed, chosenSelector, receipts, refusedOld, observedAtCrash>>

Allowed(state, command) ==
    CASE command[1] = Retire -> state.open /\ command[2] = state.issued /\ ~state.guard
      [] command[1] = Create -> state.open /\ command[2] = state.issued /\ ~state.guard
      [] OTHER -> ~state.open /\ command[2] = state.issued + 1

Apply(state, command) ==
    IF ~Allowed(state, command) THEN state ELSE
      CASE command[1] = Retire -> [state EXCEPT !.open = FALSE]
        [] command[1] = Create -> [state EXCEPT !.guard = TRUE]
        [] OTHER -> [issued |-> command[2], open |-> TRUE, guard |-> FALSE]

RECURSIVE Replay(_)
Replay(commands) ==
    IF Len(commands) = 0 THEN Initial
    ELSE Apply(Replay(SubSeq(commands, 1, Len(commands) - 1)), commands[Len(commands)])

Before(history, position) == Replay(SubSeq(history, 1, position - 1))
After(history, position) == Replay(SubSeq(history, 1, position))

Init ==
    /\ visible = 0 /\ stable = 0 /\ memory = <<>> /\ durable = <<>>
    /\ staged = None /\ bytesStable = FALSE /\ nameStable = FALSE
    /\ applied = 0 /\ root = Initial /\ serving = TRUE /\ crashed = FALSE /\ chosenSelector = 0
    /\ receipts = {} /\ refusedOld = FALSE /\ observedAtCrash = [dual |-> FALSE, receipt |-> FALSE, retirementPending |-> FALSE]

Stage(command) ==
    /\ serving /\ memory = durable /\ Len(memory) < Limit /\ staged = None
    /\ staged' = command /\ bytesStable' = FALSE /\ nameStable' = FALSE
    /\ UNCHANGED <<visible, stable, memory, durable, applied, root, serving, crashed,
                   chosenSelector, receipts, refusedOld, observedAtCrash>>

SyncBytes ==
    /\ serving /\ staged # None /\ ~bytesStable
    /\ bytesStable' = TRUE
    /\ UNCHANGED <<visible, stable, memory, durable, staged, nameStable, applied, root, serving,
                   crashed, chosenSelector, receipts, refusedOld, observedAtCrash>>

SyncName ==
    /\ serving /\ staged # None /\ ~nameStable
    /\ nameStable' = TRUE
    /\ UNCHANGED <<visible, stable, memory, durable, staged, bytesStable, applied, root, serving,
                   crashed, chosenSelector, receipts, refusedOld, observedAtCrash>>

Commit ==
    /\ serving /\ staged # None
    /\ bytesStable \/ Variant = "omit_data_barrier"
    /\ nameStable \/ Variant = "omit_name_barrier"
    /\ memory' = Append(memory, staged)
    /\ durable' = IF bytesStable /\ nameStable THEN memory' ELSE durable
    /\ staged' = None /\ bytesStable' = FALSE /\ nameStable' = FALSE
    /\ UNCHANGED <<visible, stable, applied, root, serving, crashed, chosenSelector, receipts,
                   refusedOld, observedAtCrash>>

ApplyNext ==
    /\ serving /\ applied < Len(memory)
    /\ root' = Apply(root, memory[applied + 1]) /\ applied' = applied + 1
    /\ refusedOld' = (refusedOld \/ (crashed /\ memory[applied'] = <<Create, 1>> /\
          ~Allowed(root, memory[applied'])))
    /\ UNCHANGED <<visible, stable, memory, durable, staged, bytesStable, nameStable, serving,
                   crashed, chosenSelector, receipts, observedAtCrash>>

Certify(position) ==
    /\ serving /\ position \in 1..applied
    /\ memory[position][1] = Retire /\ Allowed(Before(memory, position), memory[position])
    /\ receipts' = receipts \cup {memory[position][2]}
    /\ UNCHANGED <<visible, stable, memory, durable, staged, bytesStable, nameStable, applied,
                   root, serving, crashed, chosenSelector, refusedOld, observedAtCrash>>

Publish ==
    /\ serving /\ stable = visible /\ applied > visible /\ applied <= Len(durable)
    /\ visible' = applied
    /\ UNCHANGED <<stable, memory, durable, staged, bytesStable, nameStable, applied, root, serving,
                   crashed, chosenSelector, receipts, refusedOld, observedAtCrash>>

SyncSelector ==
    /\ serving /\ stable # visible
    /\ stable' = visible
    /\ UNCHANGED <<visible, memory, durable, staged, bytesStable, nameStable, applied, root, serving,
                   crashed, chosenSelector, receipts, refusedOld, observedAtCrash>>

PowerLoss(which) ==
    /\ serving /\ ~crashed /\ which \in {stable, visible}
    /\ memory' = IF Variant = "intact_is_chosen" /\ staged # None THEN Append(durable, staged) ELSE durable
    /\ staged' = None /\ bytesStable' = FALSE /\ nameStable' = FALSE
    /\ applied' = which /\ root' = After(durable, which) /\ serving' = FALSE
    /\ crashed' = TRUE /\ chosenSelector' = which
    /\ stable' = which /\ visible' = which
    /\ observedAtCrash' = [dual |-> stable # visible, receipt |-> 1 \in receipts,
                           retirementPending |-> \E position \in (applied + 1)..Len(durable) :
                               durable[position] = <<Retire, 1>> /\
                                 Allowed(Before(durable, position), durable[position])]
    /\ UNCHANGED <<durable, receipts, refusedOld>>

RecoverNext ==
    /\ ~serving /\ applied < Len(memory)
    /\ applied' = applied + 1 /\ root' = Apply(root, memory[applied'])
    /\ UNCHANGED <<visible, stable, memory, durable, staged, bytesStable, nameStable, serving,
                   crashed, chosenSelector, receipts, refusedOld, observedAtCrash>>

Resume ==
    /\ ~serving /\ (applied = Len(memory) \/ Variant = "open_at_base")
    /\ serving' = TRUE
    /\ UNCHANGED <<visible, stable, memory, durable, staged, bytesStable, nameStable, applied, root,
                   crashed, chosenSelector, receipts, refusedOld, observedAtCrash>>

Next ==
    \/ \E command \in Requests : Stage(command)
    \/ SyncBytes \/ SyncName \/ Commit \/ ApplyNext \/ RecoverNext \/ Resume
    \/ \E position \in 1..Len(memory) : Certify(position)
    \/ Publish \/ SyncSelector
    \/ \E which \in {stable, visible} : PowerLoss(which)

Spec == Init /\ [][Next]_vars

NoRetiredScopeReopens ==
    serving => \A scope \in receipts : scope <= root.issued /\ (~root.open \/ root.issued # scope)

ExactApplication == root = After(memory, applied)
RecoveryOnlyAppliesChosen == ~serving => applied <= Len(durable)

HasDurableRetirement ==
    \A scope \in receipts : \E position \in 1..Len(durable) :
        durable[position] = <<Retire, scope>> /\ Allowed(Before(durable, position), durable[position])

NeverRejectsDelayedCreateAfterRecovery ==
    ~(serving /\ crashed /\ observedAtCrash.dual /\ observedAtCrash.receipt /\ chosenSelector = 0 /\ refusedOld
      /\ root.issued = 2 /\ root.open)

NeverRecoversUnlearnedRetirement ==
    ~(serving /\ crashed /\ observedAtCrash.dual /\ observedAtCrash.retirementPending /\ ~observedAtCrash.receipt
      /\ chosenSelector = 0 /\ 1 \in receipts /\ ~root.open)
=============================================================================
