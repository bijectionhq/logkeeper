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

/-- A hold's replay interval and the removed prefix are both half-open.
A nonempty live interval starts at or after the old floor. -/
def pinsSuffix (start finish newFloor : Nat) : Prop :=
  start < finish ∧ start < newFloor

def trimPrefixSafe (oldFloor newFloor checkpoint : Nat) (live : List (Nat × Nat)) : Prop :=
  ∀ lsn, oldFloor ≤ lsn → lsn < newFloor →
    lsn < checkpoint ∧ ∀ hold ∈ live, ¬ (hold.1 ≤ lsn ∧ lsn < hold.2)

theorem trim_preserves_replay {oldFloor newFloor checkpoint : Nat} {live : List (Nat × Nat)}
    (atCheckpoint : newFloor ≤ checkpoint)
    (noPin : ∀ hold ∈ live, ¬ pinsSuffix hold.1 hold.2 newFloor) :
    trimPrefixSafe oldFloor newFloor checkpoint live := by
  intro lsn _ beforeTrim
  refine ⟨by omega, fun hold member covers => ?_⟩
  exact noPin hold member ⟨by omega, by omega⟩

def creditFor (lane : ChargeClass) (records : List Append) : Nat :=
  (records.map fun record => if record.debit.chargeClass = lane then record.debit.bytes else 0).sum

private theorem credit_fold (records : List Append) (initial : Credit) :
    records.foldl (fun acc record => acc.addDebit record.debit) initial =
      ⟨initial.ordinary + creditFor .ordinary records,
       initial.maintenance + creditFor .maintenance records⟩ := by
  induction records generalizing initial with
  | nil => simp [creditFor]
  | cons record tail ih =>
    rw [List.foldl_cons, ih]
    cases h : record.debit.chargeClass <;>
      simp [Credit.addDebit, creditFor, h, Nat.add_assoc]

theorem trim_credit_matches_removed_records (history : List Decision) (oldFloor newFloor : Nat) :
    let removed := ((application history).drop oldFloor).take (newFloor - oldFloor)
    trimCredit history oldFloor newFloor = ⟨creditFor .ordinary removed, creditFor .maintenance removed⟩ := by
  dsimp [trimCredit]
  rw [credit_fold]
  simp

theorem reachable_trim_prefix :
    trimPrefixSafe 2 5 5 [(5, 9), (2, 2)] := by
  apply trim_preserves_replay (by decide)
  intro hold member
  simp at member
  rcases member with rfl | rfl <;> simp [pinsSuffix]

theorem omitted_pin_removes_needed_record : ¬ trimPrefixSafe 2 5 5 [(4, 9)] := by
  intro safe
  exact (safe 4 (by decide) (by decide)).2 (4, 9) (by simp) (by decide)

theorem trim_beyond_checkpoint_removes_needed_record : ¬ trimPrefixSafe 2 5 4 [] := by
  intro safe
  exact (by decide : ¬ 4 < 4) (safe 4 (by decide) (by decide)).1

theorem wrong_class_changes_credit (receipt : AppendReceipt) :
    trimCredit [.append ⟨receipt, .mk .ordinary 7⟩] 0 1 ≠
      trimCredit [.append ⟨receipt, .mk .maintenance 7⟩] 0 1 := by
  simp [trimCredit, application, Credit.addDebit]

#print axioms trim_preserves_replay
#print axioms trim_credit_matches_removed_records
#print axioms reachable_trim_prefix
#print axioms omitted_pin_removes_needed_record
#print axioms trim_beyond_checkpoint_removes_needed_record
#print axioms wrong_class_changes_credit

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

private theorem agrees_at_position {Value : Type} {xs ys : List Value} {position : Nat}
    {left right : Value}
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

/-- Control entries do not change the application indices of a chosen prefix. -/
theorem application_preserves_prefix {first later : List Decision}
    (chosen : first <+: later) : application first <+: application later := by
  obtain ⟨suffix, rfl⟩ := chosen
  exact ⟨application suffix, by simp [application]⟩

/-- An index in a held suffix cannot be removed by an admitted trim. It still
names the original append after the successor installs the exact sealed base
and confirms a later decision prefix. The live hold comes from the selected
retention state. -/
theorem held_record_survives_trim_and_transfer
    {source : PrefixAgreement.Ledger SourceVoter Decision}
    {destination : PrefixAgreement.Ledger DestinationVoter Decision}
    (oldVoters : Evidence source) (newVoters : Evidence destination)
    (transfer : Transfer source destination) (first : Seal source) (later : Seal destination)
    (beforeSeal : first.decisions.length ≤ transfer.finalSource.decisions.length)
    (afterInstall : transfer.installedBase.decisions.length ≤ later.decisions.length)
    {oldFloor newFloor checkpoint start through lsn : Nat}
    {live : List (Nat × Nat)} {record : Append}
    (safe : trimPrefixSafe oldFloor newFloor checkpoint live)
    (held : (start, through) ∈ live) (atFloor : oldFloor ≤ start)
    (inHold : start ≤ lsn ∧ lsn < through)
    (original : (application first.decisions)[lsn]? = some record) :
    newFloor ≤ lsn ∧ (application later.decisions)[lsn]? = some record := by
  constructor
  · by_cases retained : newFloor ≤ lsn
    · exact retained
    · exact False.elim ((safe lsn (Nat.le_trans atFloor inHold.1) (by omega)).2
        (start, through) held inHold)
  · have preserved := application_preserves_prefix
      (transfer_extends_chosen_history oldVoters newVoters transfer first later beforeSeal afterInstall)
    obtain ⟨suffix, eq⟩ := preserved
    rw [← eq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp original).1, original]

theorem empty_trim_returns_zero (history : List Decision) (floor : Nat) :
    trimCredit history floor floor = ⟨0, 0⟩ := by
  simp [trimCredit]

#print axioms same_chosen_append
#print axioms same_append_after_transfer
#print axioms application_preserves_prefix
#print axioms held_record_survives_trim_and_transfer

end Logkeeper.Protocol
