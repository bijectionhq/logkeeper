import RetainedDelivery
import InvocationFloorProof
import SelectiveReadWindow

set_option warningAsError true

namespace SelectiveOrderedRecovery

open ChosenReplay (Lineage)
open RTDBFailover (Invocation Barrier)
open RecoverableRead (Permit)
open RetainedDelivery (Rules Command Frame Reply)
open SelectiveReadWindow (Window)
open ReadInvocationFloor (grant Advances CanCarry)

variable {bytes horizon slots capacity limit : Nat} {Payload Ticket Voter : Type}

structure Image (horizon slots capacity limit : Nat) (Payload : Type) where
  body : RetainedDelivery.Image slots capacity limit Payload
  window : Window horizon

abbrev Result (horizon slots capacity limit : Nat) (Payload : Type) :=
  Image horizon slots capacity limit Payload × Reply Payload capacity

def authority (before : Image horizon slots capacity limit Payload) : Kernel.Authority :=
  OrderedReadReplay.authority before.body.ordered

def attach (body : RetainedDelivery.Image slots capacity limit Payload) (window : Window horizon) :
    Image horizon slots capacity limit Payload :=
  ⟨{body with ordered := {body.ordered with readThrough := window.floor}}, window⟩

def Spent (before : Image horizon slots capacity limit Payload) (writer : Kernel.Writer) (nonce : Nat) : Prop :=
  (grant (authority before) = some writer ∧ SelectiveReadWindow.Spent before.window nonce) ∨
    Advances (some writer) (grant (authority before))

def IsActive (current : Kernel.Authority) (writer : Kernel.Writer) : Prop :=
  current = .active writer

theorem selecting_a_window_nonce_requires_the_exact_active_writer
    (current : Kernel.Authority) (writer : Kernel.Writer) (active : IsActive current writer) :
    current = .active writer := by
  exact active

noncomputable def select (bytes : Nat) (before : Image horizon slots capacity limit Payload) (call : Invocation) :
    Option (Window horizon) := by
  classical
  exact if IsActive (authority before) call.writer then
    SelectiveReadWindow.choose (EnvelopeCodec.wordLimit bytes - 1) before.window call.nonce
  else none

theorem a_selected_nonce_is_fresh_in_its_exact_scope
    (bytes : Nat) (before : Image horizon slots capacity limit Payload) (call : Invocation)
    (after : Window horizon) (selected : select bytes before call = some after) :
    authority before = .active call.writer ∧
      ¬ SelectiveReadWindow.Spent before.window call.nonce ∧
      (∀ nonce, SelectiveReadWindow.Spent after nonce ↔
        SelectiveReadWindow.Spent before.window nonce ∨ nonce = call.nonce) := by
  unfold select at selected
  split at selected
  · next active =>
    have marks := (SelectiveReadWindow.a_normalized_decision_records_one_nonce_and_keeps_the_next_gap _ _ _ _ selected).1
    unfold SelectiveReadWindow.choose at selected
    cases consumed : SelectiveReadWindow.consume (EnvelopeCodec.wordLimit bytes - 1) before.window call.nonce with
    | none => simp [consumed] at selected
    | some next =>
      exact ⟨selecting_a_window_nonce_requires_the_exact_active_writer _ _ active,
        (SelectiveReadWindow.a_successful_consume_is_in_range_unspent_and_exact _ _ next _ consumed).1, marks⟩
  · cases selected

noncomputable def carry (before after : Kernel.Authority) (window : Window horizon) : Window horizon := by
  classical
  exact if grant before = grant after then window else SelectiveReadWindow.initial horizon

-- The legacy reducer is used only to verify and apply the existing capture or abandonment effect.
def adaptFor (before : Image horizon slots capacity limit Payload) (call : Invocation) :
    RetainedDelivery.Image slots capacity limit Payload :=
  {before.body with ordered := {before.body.ordered with readThrough := call.nonce - 1}}

def advance (before : Image horizon slots capacity limit Payload) : Image horizon slots capacity limit Payload :=
  attach (RetainedDelivery.advance before.body) before.window

noncomputable def decideAdmit (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image horizon slots capacity limit Payload) (call : Invocation) (slot : Fin capacity)
    (evidence : Ticket) : Result horizon slots capacity limit Payload :=
  match select bytes before call with
  | none => (advance before, .source .refused)
  | some window =>
      match RetainedDelivery.decide rules lineage (adaptFor before call) (.source (.admit call slot evidence)) with
      | (body, .source (.admitted permit reply)) => (attach body window, .source (.admitted permit reply))
      | _ => (advance before, .source .refused)

noncomputable def decideAbandon (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image horizon slots capacity limit Payload) (call : Invocation) (evidence : Ticket) :
    Result horizon slots capacity limit Payload :=
  match select bytes before call with
  | none => (advance before, .source .refused)
  | some window =>
      match RetainedDelivery.decide rules lineage (adaptFor before call) (.source (.abandon call evidence)) with
      | (body, .source .abandoned) => (attach body window, .source .abandoned)
      | _ => (advance before, .source .refused)

noncomputable def decide (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image horizon slots capacity limit Payload) (command : Command slots capacity limit Payload Ticket) :
    Result horizon slots capacity limit Payload :=
  match command with
  | .source (.admit call slot evidence) => decideAdmit rules lineage before call slot evidence
  | .source (.abandon call evidence) => decideAbandon rules lineage before call evidence
  | other =>
      let result := RetainedDelivery.decide rules lineage before.body other
      (attach result.1 (carry (authority before) (OrderedReadReplay.authority result.1.ordered) before.window), result.2)

def Preserves (before after : Image horizon slots capacity limit Payload) : Prop :=
  (grant (authority before) = grant (authority after) ∧
    ∀ nonce, SelectiveReadWindow.Spent before.window nonce → SelectiveReadWindow.Spent after.window nonce) ∨
  Advances (grant (authority before)) (grant (authority after))

private theorem after_advance_preserves (before : Image horizon slots capacity limit Payload) :
    Preserves before (advance before) :=
  .inl ⟨rfl, fun _ marked => marked⟩

theorem spent_survives_the_bitmap_or_a_newer_authority
    {before after : Image horizon slots capacity limit Payload} {writer : Kernel.Writer} {nonce : Nat}
    (spent : Spent before writer nonce) (preserved : Preserves before after) : Spent after writer nonce := by
  rcases preserved with ⟨same, remembers⟩ | newer
  · rcases spent with ⟨scope, bit⟩ | alreadyOlder
    · exact .inl ⟨same.symm.trans scope, remembers nonce bit⟩
    · exact .inr (same ▸ alreadyOlder)
  · rcases spent with ⟨scope, _⟩ | alreadyOlder
    · exact .inr (scope ▸ newer)
    · exact .inr (ReadInvocationFloor.advances_trans alreadyOlder newer)

theorem selecting_a_spent_invocation_refuses
    (bytes : Nat) (before : Image horizon slots capacity limit Payload) (call : Invocation)
    (spent : Spent before call.writer call.nonce) : select bytes before call = none := by
  cases selected : select bytes before call with
  | none => rfl
  | some window =>
    obtain ⟨active, fresh, _⟩ := a_selected_nonce_is_fresh_in_its_exact_scope bytes before call window selected
    rcases spent with ⟨_, bit⟩ | ended
    · exact False.elim (fresh bit)
    · simp [active, ReadInvocationFloor.grant, ReadInvocationFloor.Advances, ReadInvocationFloor.Newer] at ended

theorem a_spent_invocation_refuses_before_any_new_hold
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image horizon slots capacity limit Payload) (call : Invocation) (slot : Fin capacity)
    (evidence : Ticket) (spent : Spent before call.writer call.nonce) :
    decide rules lineage before (.source (.admit call slot evidence)) = (advance before, .source .refused) := by
  simp [decide, decideAdmit, selecting_a_spent_invocation_refuses bytes before call spent]

private theorem retained_decisions_can_carry
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : RetainedDelivery.Image slots capacity limit Payload) (command : Command slots capacity limit Payload Ticket) :
    CanCarry (OrderedReadReplay.authority before.ordered)
      (OrderedReadReplay.authority (RetainedDelivery.decide rules lineage before command).1.ordered) := by
  have unchanged : CanCarry (OrderedReadReplay.authority before.ordered)
      (OrderedReadReplay.authority before.ordered) := .inl rfl
  cases command with
  | source command =>
    have keeps := InvocationFloorProof.every_ordered_decision_uses_the_same_or_a_newer_grant
      rules.ordered lineage before.ordered command
    cases command
    case deliver => exact unchanged
    all_goals exact keeps
  | grant key request borrow evidence =>
    simp only [RetainedDelivery.decide, RetainedDelivery.grant]
    cases outcome : OrderedReadReplay.decideDelivery rules.ordered lineage before.ordered request evidence <;> dsimp only
    case delivery => split <;> exact unchanged
    all_goals exact unchanged
  | settle key borrow evidence =>
    simp only [RetainedDelivery.decide]
    cases found : DeliveryBook.atKey before.deliveries key <;> dsimp only
    case some => split <;> exact unchanged
    all_goals exact unchanged

private theorem attach_preserves_after_selection
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image horizon slots capacity limit Payload) (call : Invocation) (window : Window horizon)
    (selected : select bytes before call = some window) (command : Command slots capacity limit Payload Ticket) :
    Preserves before (attach (RetainedDelivery.decide rules lineage (adaptFor before call) command).1 window) := by
  have retained := retained_decisions_can_carry rules lineage (adaptFor before call) command
  rcases retained with same | newer
  · have marks := (a_selected_nonce_is_fresh_in_its_exact_scope bytes before call window selected).2.2
    exact .inl ⟨same, fun nonce spent => (marks nonce).mpr (.inl spent)⟩
  · exact .inr newer

private theorem ordinary_carry_preserves
    (before : Image horizon slots capacity limit Payload) (body : RetainedDelivery.Image slots capacity limit Payload)
    (keeps : CanCarry (authority before) (OrderedReadReplay.authority body.ordered)) :
    Preserves before (attach body (carry (authority before) (OrderedReadReplay.authority body.ordered) before.window)) := by
  classical
  rcases keeps with same | newer
  · exact .inl ⟨same, by simp [carry, same, attach]⟩
  · exact .inr newer

theorem every_applied_command_preserves_spent_invocations
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image horizon slots capacity limit Payload) (command : Command slots capacity limit Payload Ticket) :
    Preserves before (decide rules lineage before command).1 := by
  have ordinary (other : Command slots capacity limit Payload Ticket) :=
    ordinary_carry_preserves before (RetainedDelivery.decide rules lineage before.body other).1
      (retained_decisions_can_carry rules lineage before.body other)
  cases command with
  | grant key request borrow evidence => exact ordinary (.grant key request borrow evidence)
  | settle key borrow evidence => exact ordinary (.settle key borrow evidence)
  | source command =>
    cases command with
    | journal effect => exact ordinary (.source (.journal effect))
    | close permit evidence => exact ordinary (.source (.close permit evidence))
    | deliver delivery evidence => exact ordinary (.source (.deliver delivery evidence))
    | admit call slot evidence =>
      simp only [decide, decideAdmit]
      cases selected : select bytes before call with
      | none => exact after_advance_preserves before
      | some window =>
        have records := attach_preserves_after_selection rules lineage before call window selected (.source (.admit call slot evidence))
        cases result : RetainedDelivery.decide rules lineage (adaptFor before call) (.source (.admit call slot evidence)) with
        | mk body outcome =>
          cases outcome
          case source inner =>
            cases inner
            case admitted => simpa only [result] using records
            all_goals exact after_advance_preserves before
          all_goals exact after_advance_preserves before
    | abandon call evidence =>
      simp only [decide, decideAbandon]
      cases selected : select bytes before call with
      | none => exact after_advance_preserves before
      | some window =>
        have records := attach_preserves_after_selection rules lineage before call window selected (.source (.abandon call evidence))
        cases result : RetainedDelivery.decide rules lineage (adaptFor before call) (.source (.abandon call evidence)) with
        | mk body outcome =>
          cases outcome
          case source inner =>
            cases inner
            case abandoned => simpa only [result] using records
            all_goals exact after_advance_preserves before
          all_goals exact after_advance_preserves before

theorem accepting_a_read_records_its_window_bit_and_the_original_protected_effect
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before after : Image horizon slots capacity limit Payload) (call : Invocation) (slot : Fin capacity)
    (evidence : Ticket) (permit : Permit capacity) (reply : Barrier)
    (accepted : decide rules lineage before (.source (.admit call slot evidence)) =
      (after, .source (.admitted permit reply))) :
    Spent after call.writer call.nonce ∧
      (after.body.ordered.reads, permit) = RecoverableRead.captured before.body.ordered.reads slot reply ∧
      after.body.deliveries = before.body.deliveries := by
  simp only [decide, decideAdmit] at accepted
  cases selected : select bytes before call with
  | none => simp [selected] at accepted
  | some window =>
    cases legacy : OrderedReadReplay.decide rules.ordered lineage (adaptFor before call).ordered
        (.admit call slot evidence) with
    | mk ordered outcome =>
      cases outcome <;> simp [selected, RetainedDelivery.decide, legacy] at accepted
      case admitted actualPermit actualReply =>
        rcases accepted with ⟨rfl, rfl, rfl⟩
        have holds := (OrderedReadReplay.every_admitted_reply_is_the_exact_marker_and_attested_basis
          rules.ordered lineage (adaptFor before call).ordered ordered call slot evidence _ _ legacy).2.2.2.2
        obtain ⟨active, _, marked⟩ := a_selected_nonce_is_fresh_in_its_exact_scope bytes before call window selected
        have keeps := InvocationFloorProof.every_ordered_decision_uses_the_same_or_a_newer_grant
          rules.ordered lineage (adaptFor before call).ordered (.admit call slot evidence)
        rw [legacy] at keeps
        refine ⟨?_, holds, rfl⟩
        have activeGrant : grant (authority before) = some call.writer := by rw [active]; rfl
        rcases keeps with same | newer
        · change grant (authority before) = grant (OrderedReadReplay.authority ordered) at same
          exact .inl ⟨same.symm.trans activeGrant, (marked call.nonce).mpr (.inr rfl)⟩
        · change Advances (grant (authority before)) (grant (OrderedReadReplay.authority ordered)) at newer
          rw [activeGrant] at newer
          exact .inr newer

theorem closing_a_read_does_not_clear_its_admission_window_or_delivery_book
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image horizon slots capacity limit Payload) (permit : Permit capacity) (evidence : Ticket) :
    let after := (decide rules lineage before (.source (.close permit evidence))).1
    after.window = before.window ∧ after.body.deliveries = before.body.deliveries := by
  classical
  have same : carry (authority before) (authority before) before.window = before.window := by simp [carry]
  simp only [decide, RetainedDelivery.decide, OrderedReadReplay.decide]
  split
  · cases JointReadRecovery.orderClose (OrderedReadReplay.authority before.body.ordered)
      rules.ordered.snapshot before.body.ordered.reads permit <;> exact ⟨same, rfl⟩
  · exact ⟨same, rfl⟩

noncomputable def step (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image horizon slots capacity limit Payload) (frame : Frame slots capacity limit Payload Ticket) :
    Option (Image horizon slots capacity limit Payload) := by
  classical
  exact if frame.lineage = lineage ∧ frame.position = RetainedDelivery.position before.body + 1 then
    some (decide rules lineage before frame.command).1 else none

noncomputable def replay (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin : Image horizon slots capacity limit Payload) (frames : List (Frame slots capacity limit Payload Ticket)) :
    Option (Image horizon slots capacity limit Payload) :=
  frames.foldlM (step rules lineage) origin

theorem every_replayed_scope_change_preserves_past_admissions
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before after : Image horizon slots capacity limit Payload) (frames : List (Frame slots capacity limit Payload Ticket))
    (writer : Kernel.Writer) (nonce : Nat) (spent : Spent before writer nonce)
    (restored : replay rules lineage before frames = some after) : Spent after writer nonce := by
  induction frames generalizing before with
  | nil =>
    have same : before = after := by simpa [replay] using restored
    exact same ▸ spent
  | cons frame tail later =>
    cases applied : step rules lineage before frame with
    | none => simp [replay, applied] at restored
    | some next =>
      have held : Spent next writer nonce := by
        unfold step at applied
        split at applied
        · cases applied
          exact spent_survives_the_bitmap_or_a_newer_authority spent
            (every_applied_command_preserves_spent_invocations rules lineage before frame.command)
        · cases applied
      exact later next held (by simpa [replay, applied] using restored)

structure Base (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin : Image horizon slots capacity limit Payload) (frames : List (Frame slots capacity limit Payload Ticket)) where
  cut : Nat
  image : Image horizon slots capacity limit Payload
  within : cut ≤ frames.length
  certified : replay rules lineage origin (frames.take cut) = some image

noncomputable def reopen (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    {origin : Image horizon slots capacity limit Payload} {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket)}
    {ballot : Nat} {frames : List (Frame slots capacity limit Payload Ticket)}
    (_cut : PrefixAgreement.Chosen ledger ballot frames) (base : Base rules lineage origin frames)
    (media : List (Frame slots capacity limit Payload Ticket)) : Option (Image horizon slots capacity limit Payload) := by
  classical
  exact if frames.drop base.cut <+: media then replay rules lineage base.image (frames.drop base.cut) else none

private theorem after_certified_base (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin : Image horizon slots capacity limit Payload) (frames : List (Frame slots capacity limit Payload Ticket))
    (base : Base rules lineage origin frames) :
    replay rules lineage base.image (frames.drop base.cut) = replay rules lineage origin frames := by
  have certified := base.certified
  conv => rhs; rw [← List.take_append_drop base.cut frames]
  simp only [replay] at certified ⊢
  rw [List.foldlM_append, certified]
  rfl

private theorem opened_is_exact (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    {origin : Image horizon slots capacity limit Payload} {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket)}
    {ballot : Nat} {frames : List (Frame slots capacity limit Payload Ticket)}
    (cut : PrefixAgreement.Chosen ledger ballot frames) (base : Base rules lineage origin frames)
    (media : List (Frame slots capacity limit Payload Ticket)) (after : Image horizon slots capacity limit Payload)
    (opened : reopen rules lineage cut base media = some after) :
    replay rules lineage origin frames = some after := by
  unfold reopen at opened
  split at opened
  · exact (after_certified_base rules lineage origin frames base).symm.trans opened
  · cases opened

theorem both_selectable_bases_restore_one_window_and_its_original_reads
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    {origin : Image horizon slots capacity limit Payload} {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket)}
    {ballot : Nat} {frames : List (Frame slots capacity limit Payload Ticket)}
    (cut : PrefixAgreement.Chosen ledger ballot frames) (old new : Base rules lineage origin frames)
    (oldMedia newMedia : List (Frame slots capacity limit Payload Ticket)) (left right : Image horizon slots capacity limit Payload)
    (openedOld : reopen rules lineage cut old oldMedia = some left)
    (openedNew : reopen rules lineage cut new newMedia = some right) : left = right :=
  Option.some.inj ((opened_is_exact rules lineage cut old oldMedia left openedOld).symm.trans
    (opened_is_exact rules lineage cut new newMedia right openedNew))

theorem any_recovery_preserves_a_spent_invocation_from_a_certified_prefix
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    {origin : Image horizon slots capacity limit Payload} {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket)}
    {ballot : Nat} {frames : List (Frame slots capacity limit Payload Ticket)}
    (cut : PrefixAgreement.Chosen ledger ballot frames) (earlier selected : Base rules lineage origin frames)
    (media : List (Frame slots capacity limit Payload Ticket)) (after : Image horizon slots capacity limit Payload)
    (opened : reopen rules lineage cut selected media = some after)
    (writer : Kernel.Writer) (nonce : Nat) (spent : Spent earlier.image writer nonce) : Spent after writer nonce := by
  have restored := (after_certified_base rules lineage origin frames earlier).trans
    (opened_is_exact rules lineage cut selected media after opened)
  exact every_replayed_scope_change_preserves_past_admissions rules lineage earlier.image after _ writer nonce spent restored

theorem an_installed_ranked_successor_preserves_the_exact_prior_invocation
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    {before next current : ConfigurationClosure.Generation Voter (Frame slots capacity limit Payload Ticket)}
    (changed : ConfigurationClosure.Handoff before next) (later : ConfigurationClosure.Changes next current)
    {ballot : Nat} {prior : List (Frame slots capacity limit Payload Ticket)}
    (chosen : PrefixAgreement.Chosen before.ledger ballot prior)
    (origin earlier after : Image horizon slots capacity limit Payload)
    (previous : replay rules lineage origin prior = some earlier)
    (restored : replay rules lineage origin current.basis = some after)
    (writer : Kernel.Writer) (nonce : Nat) (spent : Spent earlier writer nonce) :
    Spent after writer nonce := by
  obtain ⟨suffix, exactHistory⟩ :=
    (ConfigurationClosure.handoff_inherits_every_prior_choice changed chosen).trans
      (ConfigurationClosure.arbitrarily_many_changes_keep_installed_prefix later)
  have tail : replay rules lineage earlier suffix = some after := by
    rw [← exactHistory] at restored
    simp only [replay] at previous restored ⊢
    rw [List.foldlM_append, previous] at restored
    exact restored
  exact every_replayed_scope_change_preserves_past_admissions rules lineage earlier after suffix writer nonce spent tail

#print axioms selecting_a_window_nonce_requires_the_exact_active_writer
#print axioms a_selected_nonce_is_fresh_in_its_exact_scope
#print axioms spent_survives_the_bitmap_or_a_newer_authority
#print axioms a_spent_invocation_refuses_before_any_new_hold
#print axioms every_applied_command_preserves_spent_invocations
#print axioms accepting_a_read_records_its_window_bit_and_the_original_protected_effect
#print axioms closing_a_read_does_not_clear_its_admission_window_or_delivery_book
#print axioms every_replayed_scope_change_preserves_past_admissions
#print axioms both_selectable_bases_restore_one_window_and_its_original_reads
#print axioms any_recovery_preserves_a_spent_invocation_from_a_certified_prefix
#print axioms an_installed_ranked_successor_preserves_the_exact_prior_invocation

end SelectiveOrderedRecovery
