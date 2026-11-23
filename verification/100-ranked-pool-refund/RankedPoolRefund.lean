import ConfigurationClosure
import SettlementRedo

set_option warningAsError true

namespace RankedPoolRefund

open SettlementRedo (Command Refund replay)
open ConfigurationClosure (Generation Handoff Changes InstalledOnQuorum)

variable {Ticket Voter : Type}

def MountMatches (localHistory installedHistory : List Command) : Prop :=
  localHistory = installedHistory

theorem matching_a_ranked_cut_requires_exact_commands (localHistory installedHistory : List Command)
    (verified : MountMatches localHistory installedHistory) : localHistory = installedHistory := by
  exact verified

structure Mount (rules : PoolState.Rules Ticket) (origin : PoolState.Image Ticket)
    (installed : List Command) where
  state : SettlementRedo.State Ticket
  history : SettlementRedo.Trace rules ⟨JournalRotation.initial, origin⟩ state
  matchesCut : MountMatches state.journal.history installed
  selector : JournalRotation.View
  selectable : state.journal.namespaceChoices selector

theorem the_ranked_mount_uses_its_full_exact_installed_cut
    [DecidableEq Ticket] (rules : PoolState.Rules Ticket) (origin : PoolState.Image Ticket)
    (installed : List Command) (mount : Mount rules origin installed) (safe : PoolState.Sound rules origin) :
    replay rules origin installed = some mount.state.pool ∧ PoolState.Sound rules mount.state.pool ∧
      ∃ base suffix atCut,
        mount.state.journal.media (.base mount.selector.generation) = some base ∧
        (∀ offset command, suffix[offset]? = some command →
          mount.state.journal.media (.tail (mount.selector.cut + offset)) = some [command]) ∧
        replay rules origin base = some atCut ∧ replay rules atCut suffix = some mount.state.pool := by
  let sound := SettlementRedo.arbitrary_ordered_refund_and_reuse_traces_remain_recoverable
    rules origin mount.state mount.history
  have exactCut := matching_a_ranked_cut_requires_exact_commands _ _ mount.matchesCut
  obtain ⟨base, suffix, atCut, stored, frames, opened, complete, poolSound⟩ :=
    SettlementRedo.every_crash_choice_of_the_composed_machine_recovers_the_current_budget
      rules origin mount.state mount.history safe mount.selector mount.selectable
  exact ⟨(congrArg (replay rules origin) exactCut).symm.trans sound.applied,
    poolSound, base, suffix, atCut, stored, frames, opened, complete⟩

theorem any_later_recovery_majority_reads_the_chosen_refund_and_spend_order
    [DecidableEq Ticket] (rules : PoolState.Rules Ticket) (origin : PoolState.Image Ticket)
    (safe : PoolState.Sound rules origin)
    {before next current : Generation Voter Command}
    (transfer : Handoff before next) (later : Changes next current) (installed : InstalledOnQuorum current)
    (available : Voter → Bool) (quorum : JournalRefinement.Majority current.ledger.members available)
    {ballot : Nat} {earlier : List Command} (chosen : PrefixAgreement.Chosen before.ledger ballot earlier)
    (mount : ∀ voter ∈ current.ledger.members, available voter = true →
      current.installed voter current.basis → Mount rules origin current.basis) :
    ∃ voter ∈ current.ledger.members, available voter = true ∧
      current.installed voter current.basis ∧
      ∃ suffix, current.basis = earlier ++ suffix ∧
        ∃ image, replay rules origin current.basis = some image ∧ PoolState.Sound rules image := by
  obtain ⟨voter, member, online, copy, extension⟩ :=
    ConfigurationClosure.earlier_choice_reaches_any_later_recovery_majority
      transfer later installed available quorum chosen
  obtain ⟨suffix, whole⟩ := extension
  let opened := mount voter member online copy
  have exactImage := the_ranked_mount_uses_its_full_exact_installed_cut rules origin _ opened safe
  exact ⟨voter, member, online, copy, suffix, whole.symm, opened.state.pool, exactImage.1, exactImage.2.1⟩

def additionalDebit (image : PoolState.Image Ticket) (bytes : Nat) : Command :=
  .occupy (image.ordinary + bytes)

theorem new_work_cannot_spend_a_saturated_recovered_budget
    (rules : PoolState.Rules Ticket) (image : PoolState.Image Ticket)
    (full : PoolState.used rules image = rules.limit) (bytes : Nat) (positive : 0 < bytes) :
    SettlementRedo.decide rules image (additionalDebit image bytes) = none := by
  have refuses : ¬ image.ordinary + bytes + PoolState.charges rules image.rows ≤ rules.limit := by
    simp only [PoolState.used] at full
    omega
  simp [additionalDebit, SettlementRedo.decide, refuses]

structure RefundReceipt where
  position : Nat
  original : Refund

noncomputable def refundReceipt (rules : PoolState.Rules Ticket) (origin : PoolState.Image Ticket)
    (history : List Command) (position : Nat) (original : Refund) : Option RefundReceipt := by
  classical
  exact if history[position]? = some (.refund original) then
    (replay rules origin (history.take (position + 1))).map (fun _ => ⟨position, original⟩)
  else none

theorem a_historical_receipt_reports_the_exact_applied_refund
    (rules : PoolState.Rules Ticket) (origin : PoolState.Image Ticket) (history : List Command)
    (position : Nat) (original : Refund) (receipt : RefundReceipt)
    (reported : refundReceipt rules origin history position original = some receipt) :
    history[position]? = some (.refund original) ∧ receipt = ⟨position, original⟩ ∧
      ∃ applied, replay rules origin (history.take (position + 1)) = some applied := by
  unfold refundReceipt at reported
  split at reported
  · next selected =>
    cases ordered : replay rules origin (history.take (position + 1)) with
    | none => simp [ordered] at reported
    | some applied =>
      simp [ordered] at reported
      exact ⟨selected, reported.symm, applied, rfl⟩
  · cases reported

theorem the_exact_refund_can_be_reported_after_its_credit_was_consumed
    (rules : PoolState.Rules Ticket) (origin : PoolState.Image Ticket) (row : PoolState.Row Ticket)
    (original : Refund) (rows : origin.rows = [row]) (ready : SettlementRedo.Ready origin original row)
    (full : PoolState.used rules origin = rules.limit) :
    let history := [.refund original, .occupy (origin.ordinary + rules.cost row.binding)]
    ∃ current, replay rules origin history = some current ∧
      refundReceipt rules origin history 0 original = some ⟨0, original⟩ ∧
      ∀ bytes, 0 < bytes → SettlementRedo.decide rules current (additionalDebit current bytes) = none := by
  intro history
  obtain ⟨current, executed, _, fullAgain⟩ :=
    (SettlementRedo.at_capacity_the_original_refund_must_precede_a_dependent_debit
      rules origin row original rows ready full).2
  change replay rules origin history = some current at executed
  refine ⟨current, executed, ?_, fun bytes positive =>
    new_work_cannot_spend_a_saturated_recovered_budget rules current fullAgain bytes positive⟩
  have complete : replay rules origin ([.refund original] ++ [.occupy (origin.ordinary + rules.cost row.binding)]) =
      some current := executed
  rw [SettlementRedo.a_checkpoint_and_its_suffix_replay_in_order] at complete
  cases first : replay rules origin [.refund original] with
  | none => simp [first] at complete
  | some earlier => simp [refundReceipt, history, first]

#print axioms matching_a_ranked_cut_requires_exact_commands
#print axioms the_ranked_mount_uses_its_full_exact_installed_cut
#print axioms any_later_recovery_majority_reads_the_chosen_refund_and_spend_order
#print axioms new_work_cannot_spend_a_saturated_recovered_budget
#print axioms a_historical_receipt_reports_the_exact_applied_refund
#print axioms the_exact_refund_can_be_reported_after_its_credit_was_consumed

end RankedPoolRefund
