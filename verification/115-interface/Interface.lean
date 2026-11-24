import Std

namespace Interface

abbrev Cut := Nat
abbrev Time := Nat
abbrev Subject := Nat
abbrev Owner := Nat

structure Key where
  relation : Nat
  subject : Subject
  deriving DecidableEq, Repr

structure Write where
  key : Key
  validFrom : Time
  validTo : Time
  value : Option Nat
  deriving DecidableEq, Repr

structure Range where
  relation : Nat
  first : Subject
  endBefore : Subject
  deriving DecidableEq, Repr

inductive Check where
  | point (key : Key) (valid : Time) (expected : Option Nat)
  | count (range : Range) (valid expected : Nat)
  deriving DecidableEq, Repr

structure Request where
  owner : Owner
  id : Nat
  basis : Cut
  checks : List Check
  writes : List Write
  deriving DecidableEq, Repr

structure Receipt where
  cut : Cut
  accepted : Bool
  deriving DecidableEq, Repr

inductive Event where
  | decision (request : Request) (receipt : Receipt)
  | erasure (subject : Subject) (deadline : Time)
  deriving DecidableEq, Repr

structure Lease where
  owner : Owner
  cut : Cut
  expiresAt : Time
  deriving DecidableEq, Repr

structure Store where
  history : List Event := []
  floor : Cut := 0
  leases : List (Nat × Lease) := []
  nextLease : Nat := 0
  now : Time := 0
  deriving Repr

inductive ReadError where
  | unavailable | erased | noLease
  deriving DecidableEq, Repr

inductive TransactionError where
  | changedRequest | unavailable | forgottenSubject
  deriving DecidableEq, Repr

inductive Watch where
  | reset (basis : Cut)
  | batch (through : Cut) (events : List (Cut × List Write))
  | unavailable
  deriving DecidableEq, Repr

def head (store : Store) : Cut := store.history.length

abbrev View := List Event

def snapshot (store : Store) (cut : Cut) : View := store.history.take cut

def eventSubject : Event → Option Subject
  | .erasure subject _ => some subject
  | .decision _ _ => none

def forgotten (view : View) (subject : Subject) : Bool :=
  view.any (fun event => eventSubject event == some subject)

def writes : Event → List Write
  | .decision request receipt => if receipt.accepted then request.writes else []
  | .erasure _ _ => []

def point (view : View) (key : Key) (valid : Time) : Option Nat :=
  if forgotten view key.subject then none
  else
    let selected := (view.flatMap writes).reverse.find?
      (fun write => write.key == key && write.validFrom ≤ valid && valid < write.validTo)
    selected.bind Write.value

def range (view : View) (query : Range) (valid : Time) : List (Subject × Nat) :=
  (List.range' query.first (query.endBefore - query.first)).filterMap fun subject =>
    (point view ⟨query.relation, subject⟩ valid).map (fun value => (subject, value))

-- Query code sees resolved observations, with no access to the event log or receipt payload.
structure ReadView where
  point : Key → Time → Option Nat
  range : Range → Time → List (Subject × Nat)

def queryView (view : View) : ReadView := ⟨point view, range view⟩

def satisfies (view : View) : Check → Bool
  | .point key valid expected => point view key valid == expected
  | .count selector valid expected => (range view selector valid).length == expected

def revoked (store : Store) (cut : Cut) : Bool :=
  (store.history.drop cut).any fun event =>
    match event with
    | .erasure _ deadline => decide (deadline ≤ store.now)
    | .decision _ _ => false

def available (store : Store) (cut : Cut) : Bool :=
  decide (store.floor ≤ cut ∧ cut ≤ head store)

def permit (store : Store) (cut : Cut) : Except ReadError Unit :=
  if !available store cut then .error .unavailable
  else if revoked store cut then .error .erased
  else .ok ()

inductive Basis where
  | latest | exact (cut : Cut)

def resolve (store : Store) : Basis → Cut
  | .latest => head store
  | .exact cut => cut

def read (store : Store) (basis : Basis) (query : ReadView → α) :
    Except ReadError (Cut × α) := do
  let cut := resolve store basis
  permit store cut
  return (cut, query (queryView (snapshot store cut)))

def prior (store : Store) (request : Request) : Option (Request × Receipt) :=
  store.history.findSome? fun event =>
    match event with
    | .decision original receipt =>
      if original.owner == request.owner && original.id == request.id then
        some (original, receipt)
      else none
    | .erasure _ _ => none

def transact (store : Store) (request : Request) :
    Store × Except TransactionError Receipt :=
  match prior store request with
  | some (original, receipt) =>
    (store, if original == request then .ok receipt else .error .changedRequest)
  | none =>
    match permit store request.basis with
    | .error _ => (store, .error .unavailable)
    | .ok _ =>
      if request.writes.any (fun write => forgotten store.history write.key.subject) then
        (store, .error .forgottenSubject)
      else
        let accepted := request.checks.all (satisfies (snapshot store request.basis)) &&
          request.checks.all (satisfies store.history)
        let receipt := ⟨head store + 1, accepted⟩
        ({ store with history := store.history ++ [.decision request receipt] }, .ok receipt)

def watchEvents (suffix : View) : List (Cut × List Write) :=
  suffix.filterMap fun event =>
    match event with
    | .decision request receipt =>
      if receipt.accepted then some (receipt.cut, request.writes) else none
    | .erasure _ _ => none

def subscribe (store : Store) (cursor : Cut) : Watch :=
  if head store < cursor then .unavailable
  else
    let suffix := store.history.drop cursor
    if cursor < store.floor || suffix.any (fun event => (eventSubject event).isSome) then
      .reset (head store)
    else .batch (head store) (watchEvents suffix)

inductive HoldRequest where
  | acquire (owner : Owner) (basis : Basis) (expiresAt : Time)
  | release (owner : Owner) (handle : Nat)

def hold (store : Store) : HoldRequest → Store × Except ReadError (Option Nat)
  | .acquire owner basis expiresAt =>
    let cut := resolve store basis
    if expiresAt ≤ store.now then (store, .error .noLease)
    else
      match permit store cut with
      | .error reason => (store, .error reason)
      | .ok _ =>
        let handle := store.nextLease
        ({ store with leases := (handle, ⟨owner, cut, expiresAt⟩) :: store.leases,
                      nextLease := handle + 1 }, .ok (some handle))
  | .release owner handle =>
    let remaining := store.leases.filter (fun (id, lease) => !(id == handle && lease.owner == owner))
    ({ store with leases := remaining }, .ok none)

def heldRead (store : Store) (owner : Owner) (handle : Nat) (query : ReadView → α) :
    Except ReadError (Cut × α) :=
  match store.leases.lookup handle with
  | none => .error .noLease
  | some lease =>
    if lease.owner == owner && store.now < lease.expiresAt then
      read store (.exact lease.cut) query
    else .error .noLease

def forget (store : Store) (subject : Subject) (delay : Nat) : Store :=
  if forgotten store.history subject then store
  else { store with history := store.history ++ [.erasure subject (store.now + delay)] }

-- Internal transitions, outside the five verbs.
def advanceTime (store : Store) (now : Time) : Store :=
  { store with now := max now store.now }

def armFloor (store : Store) (floor : Cut) : Store :=
  if store.floor ≤ floor ∧ floor ≤ head store ∧
      ∀ pair ∈ store.leases, pair.2.expiresAt ≤ store.now ∨ floor ≤ pair.2.cut then
    { store with floor := floor }
  else store

-- The check is executable because its quantifier is over a finite list.
theorem trimRespectsLiveHold {store : Store} {floor id : Nat} {lease : Lease}
    (old : store.floor ≤ lease.cut) (bound : (id, lease) ∈ store.leases)
    (live : store.now < lease.expiresAt) :
    (armFloor store floor).floor ≤ lease.cut := by
  unfold armFloor
  split
  · rename_i allowed
    exact (allowed.2.2 (id, lease) bound).resolve_left (Nat.not_le_of_gt live)
  · exact old

theorem exactCut (store : Store) (cut : Cut) (query : ReadView → α)
    (ok : permit store cut = .ok ()) :
    read store (.exact cut) query = .ok (cut, query (queryView (store.history.take cut))) := by
  simp [read, resolve, snapshot, ok]
  rfl

theorem projectionAtOneCut (store : Store) (cut : Cut) (query : ReadView → α)
    (project : α → β) (ok : permit store cut = .ok ()) :
    read store (.exact cut) (fun view => project (query view)) =
      (read store (.exact cut) query).map (fun (basis, result) => (basis, project result)) := by
  rw [exactCut store cut _ ok, exactCut store cut _ ok]
  rfl

theorem prefixStable (history suffix : View) (cut : Cut) (bound : cut ≤ history.length) :
    (history ++ suffix).take cut = history.take cut :=
  List.take_append_of_le_length bound

theorem originalRetry {store : Store} {request : Request} {receipt : Receipt}
    (recorded : prior store request = some (request, receipt)) :
    transact store request = (store, .ok receipt) := by
  simp [transact, recorded]

theorem changedRetry {store : Store} {request original : Request} {receipt : Receipt}
    (recorded : prior store request = some (original, receipt)) (different : original ≠ request) :
    transact store request = (store, .error .changedRequest) := by
  simp [transact, recorded, different]

theorem conflictingGuardRefuses {store : Store} {request : Request}
    (fresh : prior store request = none) (basis : permit store request.basis = .ok ())
    (writable : request.writes.any (fun write => forgotten store.history write.key.subject) = false)
    (conflict : request.checks.all (satisfies store.history) = false) :
    (transact store request).2 = .ok ⟨head store + 1, false⟩ := by
  simp [transact, fresh, basis, writable, conflict]

theorem rejectedWatchInvisible (request : Request) (cut : Cut) :
    watchEvents [.decision request ⟨cut, false⟩] = [] := rfl

theorem rejectedWritesInvisible (request : Request) (cut : Cut) :
    writes (.decision request ⟨cut, false⟩) = [] := rfl

theorem resetBelowFloor {store : Store} {cursor : Cut}
    (old : cursor < store.floor) (past : cursor ≤ head store) :
    subscribe store cursor = .reset (head store) := by
  simp [subscribe, Nat.not_lt_of_ge past, old]

theorem orderedBatch {store : Store} {cursor : Cut}
    (retained : store.floor ≤ cursor) (past : cursor ≤ head store)
    (clean : (store.history.drop cursor).any (fun event => (eventSubject event).isSome) = false) :
    subscribe store cursor = .batch (head store) (watchEvents (store.history.drop cursor)) := by
  simp [subscribe, Nat.not_lt_of_ge past, Nat.not_lt_of_ge retained, clean]

theorem forgottenPoint {view : View} {key : Key} (valid : Time)
    (erased : forgotten view key.subject = true) : point view key valid = none := by
  simp [point, erased]

theorem forgetKeepsHolds (store : Store) (subject : Subject) (delay : Nat) :
    (forget store subject delay).leases = store.leases := by
  unfold forget
  split <;> rfl

theorem revokedRead {store : Store} {cut : Cut} (query : ReadView → α)
    (valid : available store cut = true) (expired : revoked store cut = true) :
    read store (.exact cut) query = .error .erased := by
  simp [read, resolve, permit, valid, expired]
  rfl

-- Effective overlay reads choose the last override, including a tombstone.
def overlayPoint (parent : Option Nat) (overlay : List (Option Nat)) : Option Nat :=
  overlay.getLast?.getD parent

theorem untouchedOverlay (parent : Option Nat) : overlayPoint parent [] = parent := rfl

theorem overlayWins (parent : Option Nat) (earlier : List (Option Nat)) (last : Option Nat) :
    overlayPoint parent (earlier ++ [last]) = last := by
  simp [overlayPoint]

inductive Step where
  | transaction (request : Request)
  | retention (floor : Cut)
  | holdCut (request : HoldRequest)
  | erase (subject : Subject) (delay : Nat)
  | time (now : Time)

def apply (store : Store) : Step → Store
  | .transaction request => (transact store request).1
  | .retention floor => armFloor store floor
  | .holdCut request => (hold store request).1
  | .erase subject delay => forget store subject delay
  | .time now => advanceTime store now

inductive Reachable : Store → Prop where
  | empty : Reachable {}
  | step {store : Store} (prior : Reachable store) (step : Step) :
      Reachable (apply store step)

theorem traceReachable (steps : List Step) (store : Store) (reachable : Reachable store) :
    Reachable (steps.foldl apply store) := by
  induction steps generalizing store with
  | nil => exact reachable
  | cons step tail inductionHypothesis =>
    exact inductionHypothesis _ (.step reachable step)

end Interface
