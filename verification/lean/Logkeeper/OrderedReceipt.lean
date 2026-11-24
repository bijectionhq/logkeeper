import Logkeeper.Protocol

set_option warningAsError true

namespace Logkeeper.Protocol.Ordered

/-- The applied image retains the request identity and exact original receipt.
The outcome is the original applied result, including an original refusal. -/
structure RetainedReceipt (Fingerprint Receipt : Type) where
  fingerprint : Fingerprint
  original : Receipt

def abstract_book {Key Fingerprint Receipt : Type}
    (book : Key → Option (RetainedReceipt Fingerprint Receipt)) :
    Key → Option (Fingerprint × Receipt) :=
  fun key => (book key).map fun retained => (retained.fingerprint, retained.original)

def retains_receipt (position expiresAt : Nat) (ownsLiveHold : Bool) : Bool :=
  decide (position < expiresAt) || ownsLiveHold

def replay_mutation {Fingerprint Receipt : Type} [DecidableEq Fingerprint]
    (stored presented : Fingerprint) (original : Receipt) : Option Receipt :=
  if stored = presented then some original else none

def replay {Fingerprint Receipt : Type} [DecidableEq Fingerprint]
    (barrier : Bool) (stored presented : Fingerprint) (original : Receipt) : Option Receipt :=
  if barrier then none else replay_mutation stored presented original

def record_after_apply {Outcome Refusal : Type} (barrier : Bool)
    (applied : Except Refusal Outcome) : Bool :=
  !barrier || match applied with
    | .ok _ => true
    | .error _ => false

def retain_applied {Outcome Refusal : Type} (barrier : Bool)
    (applied : Except Refusal Outcome) : Option (Except Refusal Outcome) :=
  if record_after_apply barrier applied then some applied else none

def original_placement_matches {Placement : Type} (original installed : Placement) : Prop :=
  original = installed

theorem foreign_original_cannot_reconcile {Placement : Type} {original installed : Placement}
    (different : original ≠ installed) : ¬ original_placement_matches original installed :=
  different

def fresh_request_expired (position expiresAt : Nat) : Prop := expiresAt ≤ position

theorem expired_request_cannot_admit_fresh_work {position expiresAt : Nat}
    (expired : fresh_request_expired position expiresAt) : ¬ position < expiresAt :=
  Nat.not_lt_of_ge expired

theorem barriers_never_replay {Fingerprint Receipt : Type} [DecidableEq Fingerprint]
    (stored presented : Fingerprint) (original : Receipt) :
    replay true stored presented original = none := by
  simp [replay]

theorem mutation_retry_exact {Fingerprint Receipt : Type} [DecidableEq Fingerprint]
    (stored presented : Fingerprint) (original : Receipt) :
    replay false stored presented original =
      if stored = presented then some original else none := by
  rfl

theorem mutation_receipt_within_horizon {Fingerprint Receipt : Type} [DecidableEq Fingerprint]
    (fingerprint : Fingerprint) (original : Receipt) {position expiresAt : Nat}
    (inHorizon : position < expiresAt) (ownsLiveHold : Bool) :
    retains_receipt position expiresAt ownsLiveHold = true ∧
      replay false fingerprint fingerprint original = some original := by
  simp [retains_receipt, inHorizon, replay, replay_mutation]

theorem expired_receipt_without_hold {position expiresAt : Nat} (expired : expiresAt ≤ position) :
    retains_receipt position expiresAt false = false := by
  simp [retains_receipt, Nat.not_lt_of_ge expired]

theorem positive_receipt_is_applied {Outcome Refusal : Type} {barrier : Bool}
    {applied : Except Refusal Outcome} {positive : Outcome}
    (retained : retain_applied barrier applied = some (.ok positive)) : applied = .ok positive := by
  unfold retain_applied at retained
  split at retained <;> simp_all

theorem refused_barrier_leaves_no_receipt {Outcome Refusal : Type} (refusal : Refusal) :
    retain_applied (Outcome := Outcome) true (.error refusal) = none := by
  rfl

theorem reissued_append_identifies_chosen_append
    {ledger : PrefixAgreement.Ledger Voter Decision} {position presented : Nat}
    {left right : Append} {receipt : AppendReceipt}
    (evidence : Evidence ledger) (first later : Seal ledger)
    (atFirst : first.decisions[position]? = some (.append left))
    (atLater : later.decisions[position]? = some (.append right))
    (reissued : replay false left.receipt.requestDigest presented left.receipt = some receipt) :
    receipt = right.receipt ∧ presented = right.receipt.requestDigest := by
  have same := same_chosen_append evidence first later atFirst atLater
  subst right
  simp only [replay, Bool.false_eq_true, ite_false, replay_mutation] at reissued
  split at reissued <;> simp_all

/-- A successful application can record a mutation and an exact retry can reissue it. -/
example : ∃ receipt : Except Nat Nat, retain_applied false (.ok 3) = some receipt ∧
    retains_receipt 1 2 false = true ∧ replay false 7 7 receipt = some receipt := by
  exact ⟨.ok 3, rfl, rfl, rfl⟩

-- Keep the exact request match while omitting the original placement check.
example : replay false 7 7 3 = some 3 ∧ ¬ original_placement_matches 1 2 := by
  simp [replay, replay_mutation, original_placement_matches]

-- A previous success is available, but recording it for the refused attempt
-- would break positive_receipt_is_applied.
example : retain_applied false (.ok 3 : Except Nat Nat) = some (.ok 3) ∧
    retain_applied false (.error 2 : Except Nat Nat) ≠ some (.ok 3) := by
  simp [retain_applied, record_after_apply]

-- The weakened strict expiry predicate would let this identity submit anew.
example : ¬ (7 : Nat) < 7 ∧ fresh_request_expired 7 7 := by
  simp [fresh_request_expired]

#print axioms barriers_never_replay
#print axioms mutation_retry_exact
#print axioms mutation_receipt_within_horizon
#print axioms expired_receipt_without_hold
#print axioms positive_receipt_is_applied
#print axioms refused_barrier_leaves_no_receipt
#print axioms reissued_append_identifies_chosen_append
#print axioms foreign_original_cannot_reconcile
#print axioms expired_request_cannot_admit_fresh_work

end Logkeeper.Protocol.Ordered
