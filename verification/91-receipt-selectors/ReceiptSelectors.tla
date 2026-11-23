-------------------------- MODULE ReceiptSelectors ---------------------------
EXTENDS Naturals

CONSTANT Variant, Scenario

VARIABLES stable, visible, newBytes, newName, oldProof, tail, pin, running, picked, resumed

vars == <<stable, visible, newBytes, newName, oldProof, tail, pin, running, picked, resumed>>
Selectors == {stable, visible}
NeedOld(root) == root = "old" /\ Scenario # "inline"
NeedNew(root) == root = "replacement" /\ Scenario = "pending"
NeedTail(root) == root = "old" /\ Scenario # "pending"

Init ==
  /\ stable = "old"
  /\ visible = "old"
  /\ newBytes = "absent"
  /\ newName = FALSE
  /\ oldProof = TRUE
  /\ tail = TRUE
  /\ pin = (Scenario = "borrowed")
  /\ running = TRUE
  /\ picked = "none"
  /\ resumed = FALSE

Complete(root) ==
  /\ NeedOld(root) => oldProof
  /\ NeedNew(root) => newBytes = "exact" /\ newName
  /\ NeedTail(root) => tail

StageBytes ==
  /\ running
  /\ Scenario = "pending"
  /\ newBytes = "absent"
  /\ newBytes' = IF Variant = "foreign-bytes" THEN "foreign" ELSE "exact"
  /\ UNCHANGED <<stable, visible, newName, oldProof, tail, pin, running, picked, resumed>>

StageName ==
  /\ running
  /\ newBytes # "absent"
  /\ ~newName
  /\ newName' = TRUE
  /\ UNCHANGED <<stable, visible, newBytes, oldProof, tail, pin, running, picked, resumed>>

Publish ==
  /\ running
  /\ picked = "none"
  /\ stable = "old"
  /\ visible = "old"
  /\ (Scenario # "pending" \/
        (newBytes # "absent" /\ (newBytes = "exact" \/ Variant = "foreign-bytes") /\
          (newName \/ Variant = "bytes-only")))
  /\ visible' = "replacement"
  /\ UNCHANGED <<stable, newBytes, newName, oldProof, tail, pin, running, picked, resumed>>

SyncSelector ==
  /\ running
  /\ stable # visible
  /\ stable' = visible
  /\ UNCHANGED <<visible, newBytes, newName, oldProof, tail, pin, running, picked, resumed>>

DisposeOld ==
  /\ running
  /\ oldProof
  /\ Variant # "keep-every-receipt"
  /\ ~pin \/ Variant = "ignore-borrower"
  /\ IF Variant = "clear-is-reclaim"
        THEN Scenario # "pending"
        ELSE \A root \in (IF Variant = "visible-only" THEN {visible} ELSE Selectors) : ~NeedOld(root)
  /\ oldProof' = FALSE
  /\ UNCHANGED <<stable, visible, newBytes, newName, tail, pin, running, picked, resumed>>

DisposeTail ==
  /\ running
  /\ Scenario # "pending"
  /\ tail
  /\ \A root \in (IF Variant = "visible-tail" THEN {visible} ELSE Selectors) : ~NeedTail(root)
  /\ tail' = FALSE
  /\ UNCHANGED <<stable, visible, newBytes, newName, oldProof, pin, running, picked, resumed>>

FinishBorrow ==
  /\ running
  /\ pin
  /\ pin' = FALSE
  /\ UNCHANGED <<stable, visible, newBytes, newName, oldProof, tail, running, picked, resumed>>

Crash ==
  /\ running
  /\ picked = "none"
  /\ visible = "replacement"
  /\ \E root \in Selectors :
        /\ picked' = root
        /\ stable' = root
        /\ visible' = root
  /\ running' = FALSE
  /\ UNCHANGED <<newBytes, newName, oldProof, tail, pin, resumed>>

Reopen ==
  /\ ~running
  /\ Complete(picked)
  /\ running' = TRUE
  /\ resumed' = TRUE
  /\ UNCHANGED <<stable, visible, newBytes, newName, oldProof, tail, pin, picked>>

ReadySelectors == \A root \in Selectors : Complete(root)
SafelyBorrowed == pin => oldProof
HasSelectedReceipt == \A root \in Selectors : NeedNew(root) => newBytes = "exact" /\ newName
ReadyToReopen == ~running => Complete(picked)
Continues == <> resumed
Reclaims == <> (~oldProof /\ ~tail)

Next == StageBytes \/ StageName \/ Publish \/ SyncSelector \/ DisposeOld \/ DisposeTail \/ FinishBorrow \/ Crash \/ Reopen
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Next)
FairWithoutCrash == Init /\ [][Next /\ picked' = "none"]_vars /\ WF_vars(Next /\ picked' = "none")

=============================================================================
