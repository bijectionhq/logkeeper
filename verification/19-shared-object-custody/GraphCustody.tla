----------------------------- MODULE GraphCustody ----------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS RootCount, Variant
VARIABLE state

Roots == 1..RootCount
Versions == {1, 2}
Needs(root) == CASE root = 1 -> {1}
                 [] root = 2 -> {1, 2}
                 [] OTHER -> {2}
Pair(root, version) == <<root, version>>
References == UNION {{Pair(r,v) : v \in Needs(r)} : r \in Roots}

Init ==
    state = [root |-> [r \in Roots |-> IF r = 1 THEN "live" ELSE "fresh"],
        gate |-> [v \in Versions |-> "open"], bytes |-> Versions,
        pinned |-> {Pair(1,1)}, released |-> {}, messages |-> {}, borrow |-> 0,
        scan |-> {}, link |-> TRUE, rejected |-> FALSE, prior_borrow |-> FALSE,
        served_fork_after_parent |-> FALSE, child_at_parent_withdrawal |-> FALSE,
        replacement_at_withdrawal |-> FALSE]

Begin(root) ==
    /\ state.root[root] = "fresh"
    /\ state' = [state EXCEPT !.root[root] = "preparing"]

Send(ref) ==
    /\ state.root[ref[1]] = "preparing"
    /\ ref \notin (state.messages \cup state.pinned \cup state.released)
    /\ state' = [state EXCEPT !.messages = @ \cup {ref}]

Accepts(ref) ==
    /\ state.gate[ref[2]] = "open" \/ Variant = "accept_during_disposal"
    /\ ref \notin state.released \/ Variant = "unfenced_release"

Deliver(ref) ==
    /\ ref \in state.messages
    /\ IF Accepts(ref) THEN
          state' = [state EXCEPT !.messages = @ \ {ref}, !.pinned = @ \cup {ref}]
       ELSE
          state' = [state EXCEPT !.messages = @ \ {ref},
            !.rejected = @ \/ ref \in state.released]

Publish(root) ==
    /\ state.root[root] = "preparing"
    /\ \A v \in Needs(root) :
         Pair(root,v) \in state.pinned \/ (root = 2 /\ v = 2 /\ Variant = "skip_dependency")
    /\ state' = [state EXCEPT !.root[root] = "live"]

Close(root) ==
    /\ state.root[root] \in {"preparing", "live"}
    /\ state' = [state EXCEPT !.root[root] = "closed",
        !.child_at_parent_withdrawal = @ \/ (root = 1 /\ state.root[2] = "live"),
        !.replacement_at_withdrawal = @ \/
          (IF RootCount = 3 /\ root = 2 THEN state.root[3] = "live" ELSE FALSE)]

Release(ref) ==
    /\ state.root[ref[1]] = "closed" \/ Variant = "release_live_root"
    /\ ref \notin state.released
    /\ state' = [state EXCEPT !.released = @ \cup {ref}, !.pinned = @ \ {ref}]

Borrow(ref) ==
    /\ state.root[ref[1]] = "live"
    /\ ref \in state.pinned
    /\ state.borrow = 0
    /\ state' = [state EXCEPT !.borrow = ref[2],
        !.served_fork_after_parent = @ \/ (ref = Pair(2,1) /\ state.child_at_parent_withdrawal /\
              Pair(1,1) \in state.released)]

FinishBorrow ==
    /\ state.borrow # 0
    /\ state' = [state EXCEPT !.prior_borrow = TRUE, !.borrow = 0]

Unreferenced(version) ==
    \A ref \in state.pinned : ref[2] # version

Scan(version) ==
    /\ state.gate[version] = "open"
    /\ Unreferenced(version)
    /\ state.borrow # version
    /\ version \notin state.scan
    /\ state' = [state EXCEPT !.scan = @ \cup {version}]

FenceDisposal(version) ==
    /\ state.gate[version] = "open"
    /\ version \in state.scan
    /\ Unreferenced(version) \/ Variant = "stale_scan"
    /\ state.borrow # version \/ Variant = "ignore_borrow"
    /\ state' = [state EXCEPT !.gate[version] = "deleting"]

Erase(version) ==
    /\ state.gate[version] = "deleting"
    /\ state.link
    /\ state' = [state EXCEPT !.gate[version] = "gone",
        !.bytes = IF Variant = "delete_by_key" THEN {} ELSE @ \ {version}]

ToggleLink ==
    /\ state.link \/ Variant # "permanent_loss"
    /\ state' = [state EXCEPT !.link = ~@]

Next ==
    \/ FinishBorrow \/ ToggleLink
    \/ \E root \in Roots : Begin(root) \/ Publish(root) \/ Close(root)
    \/ \E ref \in References : Send(ref) \/ Deliver(ref) \/ Release(ref) \/ Borrow(ref)
    \/ \E version \in Versions : Scan(version) \/ FenceDisposal(version) \/ Erase(version)

Spec == Init /\ [][Next]_state
FairSpec == Spec /\ \A version \in Versions : WF_state(Erase(version))

EveryLiveRootComplete ==
    \A root \in Roots :
      state.root[root] = "live" => \A v \in Needs(root) : Pair(root,v) \in state.pinned

EveryPinFencesDisposal ==
    \A ref \in state.pinned : state.gate[ref[2]] = "open"

PhysicalVersionsRemain ==
    \A v \in Versions : state.gate[v] # "gone" => v \in state.bytes

EveryBorrowFencesDisposal ==
    state.borrow # 0 => state.gate[state.borrow] = "open"

ReleaseIsTerminal ==
    state.pinned \cap state.released = {}

SettlesWithAccess ==
    (<>[]state.link) => (\A v \in Versions : (state.gate[v] = "deleting") ~> (state.gate[v] = "gone"))

SettlesWithoutAccess ==
    \A v \in Versions : (state.gate[v] = "deleting") ~> (state.gate[v] = "gone")

NeverServesForkAfterParentWithdrawal ==
    ~state.served_fork_after_parent

NeverRejectsAfterEarlyRelease ==
    ~state.rejected

NeverCollectsAfterRehome ==
    ~(RootCount = 3 /\ state.served_fork_after_parent /\ state.prior_borrow /\
      state.replacement_at_withdrawal /\ state.root[3] = "live" /\ state.gate[1] = "gone")
=============================================================================
