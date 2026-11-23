import AuthorityRefinement
import ChannelLifecycle
import CheckpointReconstruction

set_option warningAsError true

namespace CustodyAuthorityHandoff

open ChannelLifecycle (Key Store)
open RegistrationRecovery (Binding Decision)

inductive Status where
  | unused
  | prepared (binding : Binding)
  | closing (binding : Binding)
  | settled

inductive Change where
  | prepare (binding : Binding)
  | cancel (binding : Binding)
  | settle (binding : Binding)

structure Command where
  key : Key
  change : Change

abbrev Book := Key → Status

def advance (prior : Status) (change : Change) : Status :=
  match prior, change with
  | .unused, .prepare binding => .prepared binding
  | .prepared old, .cancel expected => if old = expected then .closing old else prior
  | .closing old, .settle expected => if old = expected then .settled else prior
  | _, _ => prior

def applyCommand (book : Book) (command : Command) : Book :=
  fun key => if key = command.key then advance (book key) command.change else book key

def permitsCommand (fenced : Key → Binding → Prop) (command : Command) : Prop :=
  match command.change with
  | .settle binding => fenced command.key binding
  | _ => True

def Carries (book : Book) (key : Key) (binding : Binding) : Prop :=
  book key = .prepared binding ∨ book key = .closing binding

def Terminal (book : Book) (key : Key) (binding : Binding) : Prop :=
  book key = .closing binding ∨ book key = .settled

theorem cancel_requires_exact_binding {book : Book} {key : Key} {expected binding : Binding}
    (prepared : book key = .prepared binding) (different : binding ≠ expected) :
    applyCommand book ⟨key, .cancel expected⟩ key = .prepared binding := by
  simp [applyCommand, prepared, advance, different]

theorem a_different_custodian_command_leaves_the_old_plan_unchanged
    (book : Book) (command : Command) (key : Key)
    (distinct : key.handle.custodian ≠ command.key.handle.custodian) :
    applyCommand book command key = book key := by
  have separate : key ≠ command.key :=
    fun same => distinct (congrArg (fun value : Key => value.handle.custodian) same)
  simp [applyCommand, separate]

theorem no_exact_plan_is_lost_without_its_provider_fence
    {fenced : Key → Binding → Prop} {book : Book} {command : Command}
    {key : Key} {binding : Binding} (valid : permitsCommand fenced command)
    (known : Carries book key binding) :
    Carries (applyCommand book command) key binding ∨ fenced key binding := by
  rcases command with ⟨address, change⟩
  by_cases sameAddress : key = address
  · subst address
    rcases known with prepared | closing
    · cases change with
      | prepare _ => exact .inl (.inl (by simp [applyCommand, prepared, advance]))
      | cancel expected =>
          by_cases same : binding = expected
          · exact .inl (.inr (by simp [applyCommand, prepared, advance, same]))
          · exact .inl (.inl (by simp [applyCommand, prepared, advance, same]))
      | settle _ => exact .inl (.inl (by simp [applyCommand, prepared, advance]))
    · cases change with
      | prepare _ => exact .inl (.inr (by simp [applyCommand, closing, advance]))
      | cancel _ => exact .inl (.inr (by simp [applyCommand, closing, advance]))
      | settle expected =>
          by_cases same : binding = expected
          · subst expected
            have exactFence : fenced key binding := valid
            exact .inr exactFence
          · exact .inl (.inr (by simp [applyCommand, closing, advance, same]))
  · exact .inl (by simpa [Carries, applyCommand, sameAddress] using known)

theorem a_possible_grant_keeps_its_intent_across_any_valid_suffix
    {fenced : Key → Binding → Prop} {book : Book}
    {key : Key} {binding : Binding} (known : Carries book key binding)
    (commands : List Command) (valid : ∀ command, command ∈ commands → permitsCommand fenced command) :
    Carries (commands.foldl applyCommand book) key binding ∨ fenced key binding := by
  induction commands generalizing book with
  | nil => exact .inl known
  | cons head tail prior =>
      rcases no_exact_plan_is_lost_without_its_provider_fence (valid head List.mem_cons_self) known with retained | closed
      · exact prior retained (fun command member => valid command (List.mem_cons_of_mem _ member))
      · exact .inr closed

theorem late_commands_never_reopen_terminal_plan {book : Book} {key : Key} {binding : Binding}
    (terminal : Terminal book key binding) (command : Command) :
    Terminal (applyCommand book command) key binding := by
  rcases command with ⟨address, change⟩
  by_cases exactKey : key = address
  · subst address
    rcases terminal with closing | settled
    · cases change with
      | prepare _ => exact .inl (by simp [applyCommand, closing, advance])
      | cancel _ => exact .inl (by simp [applyCommand, closing, advance])
      | settle expected =>
          by_cases same : binding = expected
          · exact .inr (by simp [applyCommand, closing, advance, same])
          · exact .inl (by simp [applyCommand, closing, advance, same])
    · cases change <;> exact .inr (by simp [applyCommand, settled, advance])
  · simpa [Terminal, applyCommand, exactKey] using terminal

theorem terminal_plan_stays_closed_across_arbitrary_suffixes
    {book : Book} {key : Key} {binding : Binding} (terminal : Terminal book key binding)
    (commands : List Command) :
    Terminal (commands.foldl applyCommand book) key binding := by
  induction commands generalizing book with
  | nil => exact terminal
  | cons head _ prior => exact prior (late_commands_never_reopen_terminal_plan terminal head)

def fromJournal (stream : Kernel.State Command) : Book :=
  (stream.history.map Kernel.Entry.bytes).foldl applyCommand (fun _ => .unused)

def bookEngine (scope : CheckpointReconstruction.StreamKey) (format : Nat)
    (openRoot : Root → Option Book) (durableClosure : Root → Prop) :
    CheckpointReconstruction.Engine Book Command Root :=
  ⟨scope, format, fun _ => .unused, fun book entry => applyCommand book entry.bytes, openRoot, durableClosure⟩

theorem certified_checkpoint_and_retained_tail_recover_issuer_book
    {scope : CheckpointReconstruction.StreamKey} {format : Nat}
    {openRoot : Root → Option Book} {durableClosure : Root → Prop}
    {stream : Kernel.State Command} {image : CheckpointReconstruction.Image Book Command Root}
    {target : CheckpointReconstruction.Cut} {records : List (Kernel.Entry Command)}
    (certified : CheckpointReconstruction.Certified (bookEngine scope format openRoot durableClosure) stream image)
    (admitted : CheckpointReconstruction.Admitted (bookEngine scope format openRoot durableClosure)
      stream image target records) :
    CheckpointReconstruction.replay (bookEngine scope format openRoot durableClosure) image.root records =
      some (fromJournal {stream with history := stream.history.take target.next}) := by
  simpa only [CheckpointReconstruction.stateAt, fromJournal, List.foldl_map, bookEngine] using
    CheckpointReconstruction.admitted_replay_recovers_exact_cut certified admitted

theorem committed_terminal_decision_survives_any_ordered_authority_trace
    {limits : Kernel.Limits} {before after : Kernel.State Command} {key : Key} {binding : Binding}
    (trace : Kernel.Trace limits before after) (terminal : Terminal (fromJournal before) key binding) :
    Terminal (fromJournal after) key binding := by
  obtain ⟨later, stable⟩ := Kernel.trace_extends_history trace
  simpa only [fromJournal, stable, List.map_append, List.foldl_append] using
    terminal_plan_stays_closed_across_arbitrary_suffixes terminal (later.map Kernel.Entry.bytes)

theorem unsettled_intent_survives_arbitrary_authority_continuations
    {limits : Kernel.Limits} {before after : Kernel.State Command} {key : Key} {binding : Binding}
    {fenced : Key → Binding → Prop}
    (trace : Kernel.Trace limits before after)
    (known : Carries (fromJournal before) key binding)
    (valid : ∀ command, command ∈ after.history.map Kernel.Entry.bytes → permitsCommand fenced command) :
    Carries (fromJournal after) key binding ∨ fenced key binding := by
  obtain ⟨later, stable⟩ := Kernel.trace_extends_history trace
  have validSuffix : ∀ command, command ∈ later.map Kernel.Entry.bytes → permitsCommand fenced command := by
    intro command member
    apply valid command
    rw [stable, List.map_append]
    exact List.mem_append.mpr (.inr member)
  simpa only [fromJournal, stable, List.map_append, List.foldl_append] using
    a_possible_grant_keeps_its_intent_across_any_valid_suffix known (later.map Kernel.Entry.bytes) validSuffix

theorem exact_sealed_install_preserves_the_whole_book (certificate : AuthorityRefinement.Seal Command) :
    fromJournal (AuthorityRefinement.installed certificate) = fromJournal certificate.cut :=
  rfl

theorem issuing_source_cannot_append_through_its_sealed_row (world : AuthorityRefinement.World Command)
    (certificate : AuthorityRefinement.Seal Command) :
    (AuthorityRefinement.sealAt world certificate).rows certificate.source.placement.group = none := by
  simp [AuthorityRefinement.sealAt, AuthorityRefinement.replace]

theorem custody_book_moves_under_the_existing_handoff_gate
    {limits : Kernel.Limits} {world : AuthorityRefinement.World Command}
    (certificate : AuthorityRefinement.Seal Command)
    (source : world.rows certificate.source.placement.group = some certificate.cut)
    (active : certificate.cut.authority = .active certificate.source)
    (advances : certificate.source.placement.generation < certificate.target.generation)
    (different : certificate.source.placement.group ≠ certificate.target.group)
    (reserved : (world.slots certificate.target.group).live = some certificate.nonce) :
    ∃ after installed, AuthorityRefinement.Trace limits world after ∧
      after.rows certificate.target.group = some installed ∧ fromJournal installed = fromJournal certificate.cut := by
  obtain ⟨after, trace, row⟩ :=
    AuthorityRefinement.prepared_move_is_executable (limits := limits) certificate source active advances different reserved
  exact ⟨after, AuthorityRefinement.installed certificate, trace, row, exact_sealed_install_preserves_the_whole_book certificate⟩

def originalDecision (custodians : Nat → Store) (key : Key) (binding : Binding) : Decision :=
  ChannelLifecycle.decideAcquire (custodians key.handle.custodian) key binding

theorem a_committed_inherited_plan_reconciles_at_its_original_custodian
    (certificate : AuthorityRefinement.Seal Command) (custodians : Nat → Store) (key : Key) (binding : Binding)
    (prepared : fromJournal certificate.cut key = .prepared binding)
    (held : (custodians key.handle.custodian).grants key = some binding) :
    fromJournal (AuthorityRefinement.installed certificate) key = .prepared binding ∧
      originalDecision custodians key binding = .replay := by
  exact ⟨prepared,
    (ChannelLifecycle.existing_grant_retries_without_channel_metadata (other := binding) held).1⟩

def settleAtOrigin (custodians : Nat → Store) (key : Key) : Nat → Store :=
  fun location =>
    if location = key.handle.custodian then ChannelLifecycle.releaseGrant (custodians location) key
    else custodians location

theorem moved_issuer_can_release_original_grant_without_rebinding
    (certificate : AuthorityRefinement.Seal Command) (custodians : Nat → Store) (key : Key) (binding : Binding)
    (policy : ChannelLifecycle.Authority)
    (terminal : fromJournal certificate.cut key = .closing binding)
    (held : (custodians key.handle.custodian).grants key = some binding)
    (authorized : fromJournal (AuthorityRefinement.installed certificate) key = .closing binding →
      policy.mayRelease key binding) :
    ChannelLifecycle.Step policy (custodians key.handle.custodian)
      (settleAtOrigin custodians key key.handle.custodian) ∧
      (settleAtOrigin custodians key key.handle.custodian).grants key = none ∧
      ∀ other, other ≠ key.handle.custodian → settleAtOrigin custodians key other = custodians other := by
  have live := authorized terminal
  have original : settleAtOrigin custodians key key.handle.custodian =
      ChannelLifecycle.releaseGrant (custodians key.handle.custodian) key := by simp [settleAtOrigin]
  rw [original]
  exact ⟨.release key binding (.inr held) live,
    (ChannelLifecycle.release_clears_only_the_exact_key (custodians key.handle.custodian) key).1,
    by intro other different; simp [settleAtOrigin, different]⟩

theorem retired_origin_absence_stays_safe_to_settle
    {policy : ChannelLifecycle.Authority} {first last : Store}
    (trace : ChannelLifecycle.Trace policy first last) {key : Key}
    (retired : ChannelLifecycle.Retired first key.handle) (absent : first.grants key = none) (binding : Binding) :
    last.grants key = none ∧ ChannelLifecycle.decideAcquire last key binding = .refuse :=
  ChannelLifecycle.old_delayed_acquire_stays_refused_after_reclaim trace retired absent binding

#print axioms cancel_requires_exact_binding
#print axioms a_different_custodian_command_leaves_the_old_plan_unchanged
#print axioms no_exact_plan_is_lost_without_its_provider_fence
#print axioms a_possible_grant_keeps_its_intent_across_any_valid_suffix
#print axioms late_commands_never_reopen_terminal_plan
#print axioms terminal_plan_stays_closed_across_arbitrary_suffixes
#print axioms certified_checkpoint_and_retained_tail_recover_issuer_book
#print axioms committed_terminal_decision_survives_any_ordered_authority_trace
#print axioms unsettled_intent_survives_arbitrary_authority_continuations
#print axioms exact_sealed_install_preserves_the_whole_book
#print axioms issuing_source_cannot_append_through_its_sealed_row
#print axioms custody_book_moves_under_the_existing_handoff_gate
#print axioms a_committed_inherited_plan_reconciles_at_its_original_custodian
#print axioms moved_issuer_can_release_original_grant_without_rebinding
#print axioms retired_origin_absence_stays_safe_to_settle

end CustodyAuthorityHandoff
