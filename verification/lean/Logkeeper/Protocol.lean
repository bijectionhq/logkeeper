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
  chargeClass : ChargeClass
  bytes : Nat
  deriving DecidableEq

structure Credit where
  ordinary : Nat
  maintenance : Nat
  deriving DecidableEq

def Credit.addDebit (credit : Credit) (debit : Debit) : Credit :=
  match debit.chargeClass with
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

private theorem agrees_at_position {xs ys : List Decision} {position : Nat} {left right : Decision}
    (extendsHistory : xs <+: ys)
    (atFirst : xs[position]? = some left) (atLater : ys[position]? = some right) :
    left = right := by
  obtain ⟨suffix, rfl⟩ := extendsHistory
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp atFirst).1, atFirst] at atLater
  exact Option.some.inj atLater

theorem same_chosen_decision {ledger : PrefixAgreement.Ledger Voter Decision}
    {position : Nat} {left right : Decision}
    (evidence : Evidence ledger) (first later : Seal ledger)
    (atFirst : first.decisions[position]? = some left)
    (atLater : later.decisions[position]? = some right) : left = right := by
  rcases compatible evidence first later with shorter | longer
  · exact agrees_at_position shorter atFirst atLater
  · exact (agrees_at_position longer atLater atFirst).symm

/-- The signed repair package carries the final predecessor selection to
the successor's installed base. Full decision history is a logical projection
of the selected state and the compacted prefix that preceded it. -/
structure Transfer (source : PrefixAgreement.Ledger SourceVoter Decision)
    (destination : PrefixAgreement.Ledger DestinationVoter Decision) where
  finalSource : Seal source
  installedBase : Seal destination
  exactImage : installedBase.decisions = finalSource.decisions

theorem transfer_extends_chosen_history
    {source : PrefixAgreement.Ledger SourceVoter Decision}
    {destination : PrefixAgreement.Ledger DestinationVoter Decision}
    (oldVoters : Evidence source) (newVoters : Evidence destination)
    (transfer : Transfer source destination) (first : Seal source) (later : Seal destination)
    (beforeSeal : first.decisions.length ≤ transfer.finalSource.decisions.length)
    (afterInstall : transfer.installedBase.decisions.length ≤ later.decisions.length) :
    first.decisions <+: later.decisions := by
  have oldPrefix : first.decisions <+: transfer.finalSource.decisions := by
    rcases compatible oldVoters first transfer.finalSource with prior | terminal
    · exact prior
    · exact List.prefix_of_prefix_length_le List.prefix_rfl terminal beforeSeal
  have newPrefix : transfer.installedBase.decisions <+: later.decisions := by
    rcases compatible newVoters transfer.installedBase later with installed | shorter
    · exact installed
    · exact List.prefix_of_prefix_length_le List.prefix_rfl shorter afterInstall
  rw [transfer.exactImage] at newPrefix
  exact oldPrefix.trans newPrefix

theorem same_append_after_transfer
    {position : Nat} {left right : Append}
    {source : PrefixAgreement.Ledger SourceVoter Decision}
    {destination : PrefixAgreement.Ledger DestinationVoter Decision}
    (oldVoters : Evidence source) (newVoters : Evidence destination)
    (transfer : Transfer source destination) (first : Seal source) (later : Seal destination)
    (beforeSeal : first.decisions.length ≤ transfer.finalSource.decisions.length)
    (afterInstall : transfer.installedBase.decisions.length ≤ later.decisions.length)
    (atFirst : first.decisions[position]? = some (.append left))
    (atLater : later.decisions[position]? = some (.append right)) : left = right :=
  Decision.append.inj (agrees_at_position
    (transfer_extends_chosen_history oldVoters newVoters transfer first later beforeSeal afterInstall)
    atFirst atLater)

theorem same_chosen_append {ledger : PrefixAgreement.Ledger Voter Decision}
    {position : Nat} {left right : Append}
    (evidence : Evidence ledger) (first later : Seal ledger)
    (atFirst : first.decisions[position]? = some (.append left))
    (atLater : later.decisions[position]? = some (.append right)) : left = right :=
  Decision.append.inj (same_chosen_decision evidence first later atFirst atLater)

theorem empty_trim_returns_zero (history : List Decision) (floor : Nat) :
    trimCredit history floor floor = ⟨0, 0⟩ := by
  simp [trimCredit]

#print axioms same_chosen_append
#print axioms same_append_after_transfer

end Logkeeper.Protocol
