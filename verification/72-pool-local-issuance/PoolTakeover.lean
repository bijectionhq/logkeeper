import ConfigurationClosure
import PoolState

set_option warningAsError true

namespace PoolTakeover

open ConfigurationClosure (Generation Handoff Changes InstalledOnQuorum)
open PoolState (Rules Image Identity Sound Step Trace Holds Disposed)
open ChannelLifecycle (Key)
open RegistrationRecovery (Binding)

variable {Ticket Voter : Type} [DecidableEq Ticket]

inductive Replay (rules : Rules Ticket) : Image Ticket → List (Image Ticket) → Image Ticket → Prop
  | nil (state : Image Ticket) : Replay rules state [] state
  | cons {before next last rest} :
      Step rules before next → Replay rules next rest last → Replay rules before (next :: rest) last

theorem replay_of_one_exact_pool_history_has_one_joint_image
    {rules : Rules Ticket} {initial left right : Image Ticket} {commands : List (Image Ticket)}
    (one : Replay rules initial commands left) (other : Replay rules initial commands right) :
    left = right := by
  induction one generalizing right with
  | nil => cases other; rfl
  | cons _ _ prior =>
      cases other with
      | cons _ sameTail => exact prior sameTail

private theorem replay_split {rules : Rules Ticket} {initial final : Image Ticket}
    (earlier suffix : List (Image Ticket))
    (whole : Replay rules initial (earlier ++ suffix) final) :
    ∃ middle, Replay rules initial earlier middle ∧ Replay rules middle suffix final := by
  induction earlier generalizing initial with
  | nil => exact ⟨initial, .nil _, whole⟩
  | cons first rest prior =>
      cases whole with
      | cons step tail =>
          obtain ⟨middle, chosen, remaining⟩ := prior tail
          exact ⟨middle, .cons step chosen, remaining⟩

private theorem replay_is_a_local_trace {rules : Rules Ticket} {initial final : Image Ticket}
    {steps : List (Image Ticket)} (verified : Replay rules initial steps final) : Trace rules initial final := by
  have addFirst {before next last : Image Ticket} (step : Step rules before next)
      (later : Trace rules next last) : Trace rules before last := by
    induction later with
    | same => exact .next (.same _) step
    | next _ event prior => exact .next prior event
  induction verified with
  | nil => exact .same _
  | cons step _ prior => exact addFirst step prior

theorem any_later_recovery_majority_reads_the_joint_pool_history
    (rules : Rules Ticket) (initial chosenImage recovered : Image Ticket)
    {before middle current : Generation Voter (Image Ticket)}
    (change : Handoff before middle) (later : Changes middle current) (installed : InstalledOnQuorum current)
    (available : Voter → Bool) (quorum : JournalRefinement.Majority current.ledger.members available)
    {ballot : Nat} {chosenHistory : List (Image Ticket)}
    (chosen : PrefixAgreement.Chosen before.ledger ballot chosenHistory)
    (oldCut : Replay rules initial chosenHistory chosenImage)
    (newCut : Replay rules initial current.basis recovered) :
    ∃ voter ∈ current.ledger.members, available voter = true ∧
      current.installed voter current.basis ∧ Trace rules chosenImage recovered := by
  obtain ⟨voter, member, online, exactCopy, included⟩ :=
    ConfigurationClosure.earlier_choice_reaches_any_later_recovery_majority
      change later installed available quorum chosen
  obtain ⟨remaining, exactHistory⟩ := included
  have full : Replay rules initial (chosenHistory ++ remaining) recovered := exactHistory ▸ newCut
  obtain ⟨cut, validated, replayed⟩ := replay_split chosenHistory remaining full
  have exactCut : cut = chosenImage := replay_of_one_exact_pool_history_has_one_joint_image validated oldCut
  exact ⟨voter, member, online, exactCopy, exactCut ▸ replay_is_a_local_trace replayed⟩

theorem ranked_takeover_cannot_separate_the_fence_debit_and_allocator
    (rules : Rules Ticket) (initial chosenImage recovered : Image Ticket)
    {before middle current : Generation Voter (Image Ticket)}
    (change : Handoff before middle) (later : Changes middle current) (installed : InstalledOnQuorum current)
    (available : Voter → Bool) (quorum : JournalRefinement.Majority current.ledger.members available)
    {ballot : Nat} {chosenHistory : List (Image Ticket)} {identity : Identity} {key : Key} {binding : Binding}
    (chosen : PrefixAgreement.Chosen before.ledger ballot chosenHistory)
    (oldCut : Replay rules initial chosenHistory chosenImage)
    (newCut : Replay rules initial current.basis recovered)
    (safe : Sound rules chosenImage) (closed : CopyFence.Closed chosenImage.gate key)
    (charged : Holds chosenImage identity key binding) :
    ∃ voter ∈ current.ledger.members, available voter = true ∧ current.installed voter current.basis ∧
      Sound rules recovered ∧ chosenImage.issued ≤ recovered.issued ∧
      ChannelLifecycle.decideAcquire recovered.gate key binding = .refuse ∧
      (Holds recovered identity key binding ∨
        ∃ disposed, Trace rules chosenImage disposed ∧ Disposed disposed identity key binding) := by
  obtain ⟨voter, member, online, exactCopy, history⟩ := any_later_recovery_majority_reads_the_joint_pool_history
    rules initial chosenImage recovered change later installed available quorum chosen oldCut newCut
  have valid := PoolState.all_local_histories_keep_the_exact_allocator_and_capacity safe history
  have stillClosed := PoolState.after_any_local_history_a_closed_scope_stays_refused closed history
  exact ⟨voter, member, online, exactCopy, valid.1, valid.2,
    CopyFence.closed_copy_refuses_every_binding stillClosed binding,
    PoolState.a_paid_extent_stays_charged_until_its_own_stable_absence safe history charged⟩

#print axioms replay_of_one_exact_pool_history_has_one_joint_image
#print axioms any_later_recovery_majority_reads_the_joint_pool_history
#print axioms ranked_takeover_cannot_separate_the_fence_debit_and_allocator

end PoolTakeover
