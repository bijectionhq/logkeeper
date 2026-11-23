------------------------ MODULE SettlementWorkspace ------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS JobCount, ScratchUnits, Scenario, Variant

Jobs == 1..JobCount
ReadyInitially == IF Scenario = "all-ready" THEN Jobs ELSE Jobs \ {1}
Dedicated == Variant = "per-obligation"
Reserved == IF Dedicated THEN JobCount ELSE IF Variant = "no-reserve" THEN 0 ELSE ScratchUnits
HardLimit == JobCount + ScratchUnits
OrdinaryLimit == HardLimit - Reserved
CanArrive == IF Scenario = "evidence-arrives" THEN {1} ELSE {}

VARIABLES ready, workspace, published, refunded, ordinary, crashed
vars == <<ready, workspace, published, refunded, ordinary, crashed>>
OrdinaryUse == ordinary + Cardinality(Jobs \ refunded)
UnreservedScratch == IF Reserved = 0 THEN Cardinality(workspace) ELSE 0

Init ==
  /\ ready = ReadyInitially
  /\ workspace = {}
  /\ published = {}
  /\ refunded = {}
  /\ ordinary = OrdinaryLimit - JobCount
  /\ crashed = FALSE

Receive(j) ==
  /\ j \in CanArrive \ ready
  /\ ready' = ready \cup {j}
  /\ UNCHANGED <<workspace, published, refunded, ordinary, crashed>>

HasRoom ==
  IF Reserved > 0 THEN Cardinality(workspace) < Reserved
  ELSE OrdinaryUse + UnreservedScratch < OrdinaryLimit

Stage(j) ==
  /\ j \notin (published \cup workspace)
  /\ HasRoom
  /\ \/ j \in ready
     \/ Variant = "hold-while-waiting"
     \/ Variant = "foreign-evidence" /\ ready # {}
  /\ workspace' = workspace \cup {j}
  /\ UNCHANGED <<ready, published, refunded, ordinary, crashed>>

Publish(j) ==
  /\ j \in workspace
  /\ j \in ready \/ (Variant = "foreign-evidence" /\ ready # {})
  /\ Variant # "require-ordinary-room" \/ OrdinaryUse < OrdinaryLimit
  /\ workspace' = workspace \ {j}
  /\ published' = published \cup {j}
  /\ refunded' = refunded \cup {j}
  /\ UNCHANGED <<ready, ordinary, crashed>>

EarlyRefund(j) ==
  /\ Variant = "early-refund"
  /\ j \in workspace \ refunded
  /\ refunded' = refunded \cup {j}
  /\ UNCHANGED <<ready, workspace, published, ordinary, crashed>>

Refill ==
  /\ OrdinaryUse + UnreservedScratch < OrdinaryLimit
  /\ ordinary' = ordinary + 1
  /\ UNCHANGED <<ready, workspace, published, refunded, crashed>>

Restart ==
  /\ ~crashed
  /\ workspace # {}
  /\ workspace' = {}
  /\ crashed' = TRUE
  /\ UNCHANGED <<ready, published, refunded, ordinary>>

Next ==
  \/ \E j \in Jobs : Receive(j) \/ Stage(j) \/ Publish(j) \/ EarlyRefund(j)
  \/ Refill
  \/ Restart

Spec == Init /\ [][Next]_vars

Fair ==
  /\ Spec
  /\ \A j \in Jobs : WF_vars(Receive(j)) /\ WF_vars(Stage(j)) /\ WF_vars(Publish(j))

Fits == OrdinaryUse + UnreservedScratch + Reserved <= HardLimit
ChargedUntilPublished == refunded = published
ExactPublication == published \subseteq ready
OnlyReadyHoldsWorkspace == workspace \subseteq ready
ScratchBound == Reserved = 0 \/ Cardinality(workspace) <= Reserved
ReadyFinishes == \A j \in Jobs : (j \in ready) ~> (j \in refunded)
DelayedEvidenceSettles == <>(CanArrive \subseteq refunded)
NoRestartRefundAndRefill ==
  ~(crashed /\ 2 \in refunded /\ ordinary > 0 /\ 1 \notin refunded)

=============================================================================
