import Logkeeper.DurableAcceptor

set_option warningAsError true

namespace Logkeeper.Protocol

/-- The logical placement remains fixed while physical voters change. -/
structure Placement where
  installation : Nat
  incarnation : Nat
  deriving DecidableEq

structure DataCut where
  placement : Placement
  next : Nat
  digest : Nat
  deriving DecidableEq

structure DecisionCut where
  placement : Placement
  next : Nat
  digest : Nat
  deriving DecidableEq

structure Attempt where
  placement : Placement
  issuer : Nat
  nonce : Nat
  deriving DecidableEq

inductive ChargeClass where
  | ordinary
  | maintenance
  deriving DecidableEq

structure Debit where
  class : ChargeClass
  bytes : Nat
  deriving DecidableEq

structure Credit where
  ordinary : Nat
  maintenance : Nat
  deriving DecidableEq

def Credit.addDebit (credit : Credit) (debit : Debit) : Credit :=
  match debit.class with
  | .ordinary => { credit with ordinary := credit.ordinary + debit.bytes }
  | .maintenance => { credit with maintenance := credit.maintenance + debit.bytes }

structure AppendReceipt where
  attempt : Attempt
  requestDigest : Nat
  outcomeDigest : Nat
  cut : DataCut
  -- Selected command positions determine the retry lifetime.
  expiresAt : DecisionCut
  deriving DecidableEq

structure Append where
  receipt : AppendReceipt
  debit : Debit
  deriving DecidableEq

inductive Decision where
  | append (record : Append)
  | control (digest : Nat)
  deriving DecidableEq

def application (decisions : List Decision) : List Append :=
  decisions.filterMap fun decision =>
    match decision with
    | .append record => some record
    | .control _ => none

def trimCredit (decisions : List Decision) (oldFloor newFloor : Nat) : Credit :=
  (((application decisions).drop oldFloor).take (newFloor - oldFloor)).foldl
    (fun credit record => credit.addDebit record.debit) ⟨0, 0⟩

/-- The certificate selects this exact decoded decision list, independently
of the encoding of its compact physical image. -/
structure Seal (ledger : PrefixAgreement.Ledger Voter Decision) where
  ballot : Nat
  decisions : List Decision
  chosen : PrefixAgreement.Chosen ledger ballot decisions

/-- Concrete replies and accepted values belong to the same ledger. -/
structure Evidence (ledger : PrefixAgreement.Ledger Voter Decision) where
  ballots : PrefixAgreement.BallotRules ledger
  replicas : Voter → DurableAcceptor.State Decision
  reached : ∀ voter ∈ ledger.members, DurableAcceptor.Reachable (replicas voter)
  accepts : ∀ voter ∈ ledger.members, ∀ vote,
    ledger.voted voter vote → (replicas voter).votes vote
  reported : ∀ voter ∈ ledger.members, ∀ ballot, ledger.prepared ballot voter = true →
    (replicas voter).replies ballot = some (ledger.report ballot voter)

theorem compatible {ledger : PrefixAgreement.Ledger Voter Decision}
    (evidence : Evidence ledger) (first later : Seal ledger) :
    first.decisions <+: later.decisions ∨ later.decisions <+: first.decisions :=
  DurableAcceptor.durable_replica_histories_agree evidence.ballots evidence.replicas
    evidence.reached evidence.accepts evidence.reported first.chosen later.chosen

theorem same_chosen_decision {ledger : PrefixAgreement.Ledger Voter Decision}
    (evidence : Evidence ledger) (first later : Seal ledger)
    (atFirst : first.decisions[position]? = some left)
    (atLater : later.decisions[position]? = some right) : left = right := by
  have agrees : ∀ {xs ys : List Decision} {x y : Decision},
      xs <+: ys → xs[position]? = some x → ys[position]? = some y → x = y := by
    intro xs ys x y prefix xAt yAt
    obtain ⟨suffix, rfl⟩ := prefix
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp xAt).1, xAt] at yAt
    exact Option.some.inj yAt
  rcases compatible evidence first later with shorter | longer
  · exact agrees shorter atFirst atLater
  · exact (agrees longer atLater atFirst).symm

theorem same_chosen_append {ledger : PrefixAgreement.Ledger Voter Decision}
    (evidence : Evidence ledger) (first later : Seal ledger)
    (atFirst : first.decisions[position]? = some (.append left))
    (atLater : later.decisions[position]? = some (.append right)) : left = right :=
  Decision.append.inj (same_chosen_decision evidence first later atFirst atLater)

theorem empty_trim_returns_zero (history : List Decision) (floor : Nat) :
    trimCredit history floor floor = ⟨0, 0⟩ := by
  simp [trimCredit]

end Logkeeper.Protocol
