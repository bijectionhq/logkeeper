import JointReadRecovery
import ReadInvocationFloor

set_option warningAsError true

namespace OrderedReadReplay

open ChosenReplay (Lineage)
open RTDBFailover (Invocation Barrier barrierAt)
open RecoverableRead (Permit Row SoundFor)
open SnapshotAdmission (Environment View)

variable {width slots capacity : Nat} {Payload Ticket Voter : Type}

structure Image (slots capacity : Nat) (Payload : Type) where
  journal : JointSource.Image slots Payload
  reads : RecoverableRead.State capacity
  readThrough : Nat

structure Delivery (capacity : Nat) where
  call : Invocation
  permit : Permit capacity
  basis : SnapshotAdmission.Basis

inductive Command (slots capacity : Nat) (Payload Ticket : Type) where
  | journal (effect : JointSource.Command slots Payload Ticket)
  | admit (call : Invocation) (slot : Fin capacity) (evidence : Ticket)
  | close (permit : Permit capacity) (evidence : Ticket)
  | abandon (call : Invocation) (evidence : Ticket)
  | deliver (delivery : Delivery capacity) (evidence : Ticket)

structure Frame (slots capacity : Nat) (Payload Ticket : Type) where
  lineage : Lineage
  position : Nat
  command : Command slots capacity Payload Ticket

inductive Reply (Payload : Type) (capacity : Nat) where
  | journal (reply : UnifiedSource.Reply Payload)
  | admitted (permit : Permit capacity) (reply : Barrier)
  | closed
  | abandoned
  | delivery (reply : Barrier)
  | refused

def position (image : Image slots capacity Payload) : Nat :=
  image.journal.source.source.position

def journalAuthority (journal : JointSource.Image slots Payload) : Kernel.Authority :=
  journal.source.source.core.stream.authority

def authority (image : Image slots capacity Payload) : Kernel.Authority :=
  journalAuthority image.journal

def Aligned (view : View) (journal : JointSource.Image slots Payload) : Prop :=
  view.head = journal.source.source.core.stream.history.length ∧
    view.floor = journal.source.source.core.stream.firstRetained ∧
    view.restart = journal.source.source.core.stream.checkpointEnd

structure Rules (width slots capacity : Nat) (Payload Ticket : Type) where
  journal : JointSource.Rules width slots Payload Ticket
  snapshot : Environment
  reservation : Lineage → Nat → Invocation → Fin capacity → SnapshotAdmission.Basis → Ticket → Prop
  abandon : Invocation → Ticket → Prop
  stop : Lineage → Permit capacity → Ticket → Prop
  delivery : Lineage → Invocation → Permit capacity → SnapshotAdmission.Basis → Ticket → Prop
  nextView : Lineage → Image slots capacity Payload → JointSource.Image slots Payload →
    JointSource.Command slots Payload Ticket → Option View

def advance (before : Image slots capacity Payload) : Image slots capacity Payload :=
  {before with journal := {before.journal with source := ChosenReplay.advancePosition before.journal.source}}

def Delegated : JointSource.Command slots Payload Ticket → Prop
  | .stream (.read _ _) => False
  | _ => True

def ViewChange (env : Environment) (before after : View) : Prop :=
  (after = before ∨ SnapshotAdmission.Step env before after) ∧
    after.snapshots = before.snapshots ∧ after.issued = before.issued

def deliveryOpen : Kernel.Authority → Bool
  | .sealed _ _ => false
  | _ => true

def EligibleDelivery (lineage : Lineage) (before : Image slots capacity Payload) (delivery : Delivery capacity) : Prop :=
  delivery.call.lineage = lineage ∧ deliveryOpen (authority before) = true

def MatchesDelivery (reads : RecoverableRead.State capacity) (delivery : Delivery capacity) (row : Row) : Prop :=
  row.serial = delivery.permit.serial ∧ row.reply.invocation = delivery.call ∧
    reads.view.snapshots delivery.permit.serial = some delivery.basis ∧ delivery.basis.stop = row.reply.cut

theorem delivery_checks_the_exact_permit_serial (reads : RecoverableRead.State capacity) (delivery : Delivery capacity)
    (row : Row) (bound : MatchesDelivery reads delivery row) : row.serial = delivery.permit.serial := by
  exact bound.1

def PaidDelivery (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (delivery : Delivery capacity) (evidence : Ticket) : Prop :=
  rules.delivery lineage delivery.call delivery.permit delivery.basis evidence

noncomputable def decideDelivery (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity Payload) (delivery : Delivery capacity) (evidence : Ticket) : Reply Payload capacity := by
  classical
  exact match before.reads.rows delivery.permit.slot with
  | none => .refused
  | some row =>
      if EligibleDelivery lineage before delivery ∧ MatchesDelivery before.reads delivery row ∧
          PaidDelivery rules lineage delivery evidence then .delivery row.reply
      else .refused

noncomputable def decide (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity Payload) (command : Command slots capacity Payload Ticket) :
    Image slots capacity Payload × Reply Payload capacity := by
  classical
  exact match command with
  | .journal effect =>
      if Delegated effect then
        let applied := JointSource.decide rules.journal lineage before.journal effect
        match rules.nextView lineage before applied.1 effect with
        | some view =>
            if ViewChange rules.snapshot before.reads.view view ∧ Aligned view applied.1 ∧
                ReadInvocationFloor.CanCarry (authority before) (journalAuthority applied.1) then
              let floor := ReadInvocationFloor.carry (authority before) (journalAuthority applied.1) before.readThrough
              (⟨applied.1, {before.reads with view := view}, floor⟩, .journal applied.2)
            else (advance before, .refused)
        | none => (advance before, .refused)
      else (advance before, .refused)
  | .admit call slot evidence =>
      let reply := barrierAt call before.journal
      let applied := JointSource.decide rules.journal lineage before.journal
        (AppliedBarrierReceipt.readCommand call)
      if call.lineage = lineage ∧ applied.2 = .stream (.readCut call.nonce reply.cut) ∧
          RecoverableRead.Reservable width rules.snapshot before.reads slot reply ∧
          rules.reservation lineage (position before + 1) call slot
            (SnapshotAdmission.currentBasis before.reads.view) evidence ∧
          ReadInvocationFloor.Fresh width (authority before) before.readThrough call.writer call.nonce then
        let held := RecoverableRead.captured before.reads slot reply
        (⟨applied.1, held.1, call.nonce⟩, .admitted held.2 reply)
      else (advance before, .refused)
  | .close permit evidence =>
      if rules.stop lineage permit evidence then
        match JointReadRecovery.orderClose (authority before) rules.snapshot before.reads permit with
        | some reads => ({advance before with reads := reads}, .closed)
        | none => (advance before, .refused)
      else (advance before, .refused)
  | .abandon call evidence =>
      if call.lineage = lineage ∧ rules.abandon call evidence ∧
          ReadInvocationFloor.Fresh width (authority before) before.readThrough call.writer call.nonce then
        ({advance before with readThrough := call.nonce}, .abandoned)
      else (advance before, .refused)
  | .deliver delivery evidence =>
      (advance before, decideDelivery rules lineage before delivery evidence)

def Eligible (lineage : Lineage) (before : Image slots capacity Payload)
    (frame : Frame slots capacity Payload Ticket) : Prop :=
  frame.lineage = lineage ∧ frame.position = position before + 1

def deliveryFrame (lineage : Lineage) (before : Image slots capacity Payload)
    (request : Delivery capacity) (evidence : Ticket) : Frame slots capacity Payload Ticket :=
  ⟨lineage, position before + 1, .deliver request evidence⟩

noncomputable def step (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity Payload) (frame : Frame slots capacity Payload Ticket) :
    Option (Image slots capacity Payload) := by
  classical
  exact if Eligible lineage before frame then some (decide rules lineage before frame.command).1 else none

noncomputable def replay (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (origin : Image slots capacity Payload) (frames : List (Frame slots capacity Payload Ticket)) :
    Option (Image slots capacity Payload) :=
  frames.foldlM (step rules lineage) origin

theorem replay_after_a_certified_combined_base
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    {origin base : Image slots capacity Payload} (prefixFrames suffix : List (Frame slots capacity Payload Ticket))
    (certified : replay rules lineage origin prefixFrames = some base) :
    replay rules lineage origin (prefixFrames ++ suffix) = replay rules lineage base suffix := by
  simp only [replay] at certified ⊢
  rw [List.foldlM_append, certified]
  rfl

structure Cut (ledger : PrefixAgreement.Ledger Voter (Frame slots capacity Payload Ticket)) where
  ballot : Nat
  frames : List (Frame slots capacity Payload Ticket)
  chosen : PrefixAgreement.Chosen ledger ballot frames

structure Base (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (origin : Image slots capacity Payload) (frames : List (Frame slots capacity Payload Ticket)) where
  cut : Nat
  within : cut ≤ frames.length
  image : Image slots capacity Payload
  certified : replay rules lineage origin (frames.take cut) = some image

noncomputable def reopen {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity Payload Ticket)}
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    {origin : Image slots capacity Payload} (cut : Cut ledger) (base : Base rules lineage origin cut.frames)
    (physical : List (Frame slots capacity Payload Ticket)) : Option (Image slots capacity Payload) := by
  classical
  exact if cut.frames.drop base.cut <+: physical then
    replay rules lineage base.image (cut.frames.drop base.cut)
  else none

theorem a_rival_or_missing_read_operation_cannot_reopen
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity Payload Ticket)}
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    {origin : Image slots capacity Payload} (cut : Cut ledger) (base : Base rules lineage origin cut.frames)
    (physical : List (Frame slots capacity Payload Ticket))
    (inexact : ¬ cut.frames.drop base.cut <+: physical) :
    reopen rules lineage cut base physical = none := by
  simp [reopen, inexact]

theorem reopening_with_exact_coverage_uses_the_whole_chosen_history
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity Payload Ticket)}
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    {origin : Image slots capacity Payload} (cut : Cut ledger) (base : Base rules lineage origin cut.frames)
    (physical : List (Frame slots capacity Payload Ticket))
    (covered : cut.frames.drop base.cut <+: physical) :
    reopen rules lineage cut base physical = replay rules lineage origin cut.frames := by
  rw [reopen, ite_eq_left covered,
    ← replay_after_a_certified_combined_base rules lineage _ _ base.certified, List.take_append_drop]

theorem any_successful_reopen_is_exact
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity Payload Ticket)}
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    {origin : Image slots capacity Payload} (cut : Cut ledger) (base : Base rules lineage origin cut.frames)
    (physical : List (Frame slots capacity Payload Ticket)) {after : Image slots capacity Payload}
    (reopened : reopen rules lineage cut base physical = some after) :
    replay rules lineage origin cut.frames = some after := by
  classical
  by_cases covered : cut.frames.drop base.cut <+: physical
  · exact (reopening_with_exact_coverage_uses_the_whole_chosen_history rules lineage cut base physical covered).symm.trans reopened
  · simp [reopen, covered] at reopened

theorem both_selectable_bases_recover_one_journal_and_read_book
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity Payload Ticket)}
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    {origin : Image slots capacity Payload} (cut : Cut ledger) (old new : Base rules lineage origin cut.frames)
    (oldMedia newMedia : List (Frame slots capacity Payload Ticket)) {left right : Image slots capacity Payload}
    (first : reopen rules lineage cut old oldMedia = some left)
    (second : reopen rules lineage cut new newMedia = some right) :
    left = right :=
  Option.some.inj ((any_successful_reopen_is_exact rules lineage cut old oldMedia first).symm.trans
    (any_successful_reopen_is_exact rules lineage cut new newMedia second))

theorem a_bare_journal_marker_cannot_admit_a_read
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity Payload) (writer : Kernel.Writer) (nonce : Nat) :
    decide rules lineage before (.journal (.stream (.read writer nonce))) = (advance before, .refused) := by
  simp [decide, Delegated]

theorem every_admitted_reply_is_the_exact_marker_and_attested_basis
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before after : Image slots capacity Payload) (call : Invocation) (slot : Fin capacity) (proof : Ticket)
    (permit : Permit capacity) (reply : Barrier)
    (accepted : decide rules lineage before (.admit call slot proof) = (after, .admitted permit reply)) :
    reply = barrierAt call before.journal ∧ call.lineage = lineage ∧
      (JointSource.decide rules.journal lineage before.journal (AppliedBarrierReceipt.readCommand call)).2 =
        .stream (.readCut call.nonce reply.cut) ∧
      rules.reservation lineage (position before + 1) call slot
        (SnapshotAdmission.currentBasis before.reads.view) proof ∧
      (after.reads, permit) = RecoverableRead.captured before.reads slot reply := by
  simp only [decide] at accepted
  split at accepted
  · next checks =>
      cases accepted
      exact ⟨rfl, checks.1, checks.2.1, checks.2.2.2.1, rfl⟩
  · simp at accepted

theorem a_stale_close_cannot_release_a_reused_slot
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity Payload) (permit : Permit capacity) (row : Row) (proof : Ticket)
    (live : before.reads.rows permit.slot = some row) (stale : row.serial ≠ permit.serial) :
    decide rules lineage before (.close permit proof) = (advance before, .refused) := by
  cases current : authority before <;>
    simp [decide, JointReadRecovery.orderClose, current, RecoverableRead.close, live, stale]

theorem a_sealed_source_cannot_choose_a_logical_release
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity Payload) (permit : Permit capacity) (proof : Ticket)
    (target : Kernel.Placement) (prior : Kernel.Writer) (sealed : authority before = .sealed target prior) :
    decide rules lineage before (.close permit proof) = (advance before, .refused) := by
  simp [decide, JointReadRecovery.orderClose, sealed]

theorem an_applied_close_clears_its_result_and_hold_at_one_ordered_position
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before after : Image slots capacity Payload) (permit : Permit capacity) (proof : Ticket)
    (past : Barrier → Prop) (sound : SoundFor width rules.snapshot past before.reads)
    (accepted : decide rules lineage before (.close permit proof) = (after, .closed)) :
    rules.stop lineage permit proof ∧ position after = position before + 1 ∧
      after.journal.source.source.core.stream = before.journal.source.source.core.stream ∧
      after.reads.rows permit.slot = none ∧ after.reads.view.snapshots permit.serial = none := by
  simp only [decide] at accepted
  split at accepted
  · next terminal =>
      cases released : JointReadRecovery.orderClose (authority before) rules.snapshot before.reads permit with
      | none => simp [released] at accepted
      | some reads =>
          simp [released] at accepted
          subst after
          have stopped : RecoverableRead.close rules.snapshot before.reads permit = some reads := by
            cases current : authority before <;> simp [JointReadRecovery.orderClose, current] at released
            all_goals exact released
          have exactClose := RecoverableRead.terminal_release_clears_the_exact_hold_and_preserves_other_reads sound stopped
          exact ⟨terminal, rfl, rfl, exactClose.2.1, exactClose.2.2⟩
  · simp at accepted

private theorem read_book_invariant_preserved
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity Payload) (command : Command slots capacity Payload Ticket)
    (past : Barrier → Prop) (sound : SoundFor width rules.snapshot past before.reads)
    (onAdmission : ∀ permit reply, (decide rules lineage before command).2 = .admitted permit reply → past reply) :
    SoundFor width rules.snapshot past (decide rules lineage before command).1.reads := by
  cases command with
  | journal effect =>
      simp only [decide]
      split
      · cases proposed : rules.nextView lineage before (JointSource.decide rules.journal lineage before.journal effect).1 effect with
        | none => simpa [proposed, advance] using sound
        | some view =>
            dsimp only
            split
            · next checked =>
                rcases checked.1.1 with unchanged | step
                · simpa [unchanged] using sound
                · exact RecoverableRead.ordinary_snapshot_changes_preserve_live_results_and_protection sound step checked.1.2.1
            · exact sound
      · exact sound
  | admit call slot evidence =>
      simp only [decide]
      split
      · next checked =>
          have historical : past (barrierAt call before.journal) := onAdmission
            (RecoverableRead.captured before.reads slot (barrierAt call before.journal)).2 _ (by
            simp [decide, checked])
          exact (RecoverableRead.preserve_on_capture sound checked.2.2.1 historical).1
      · exact sound
  | close permit evidence =>
      simp only [decide]
      split
      · cases released : JointReadRecovery.orderClose (authority before) rules.snapshot before.reads permit with
        | none =>
            simpa [released, advance] using sound
        | some reads =>
            have exactRelease : RecoverableRead.close rules.snapshot before.reads permit = some reads := by
              cases current : authority before <;> simp [JointReadRecovery.orderClose, current] at released
              all_goals exact released
            exact (RecoverableRead.terminal_release_clears_the_exact_hold_and_preserves_other_reads sound exactRelease).1
      · exact sound
  | abandon _ _ =>
      simp only [decide]
      split <;> exact sound
  | deliver _ _ => exact sound

def ChosenAdmission (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (origin : Image slots capacity Payload) (frames : List (Frame slots capacity Payload Ticket))
    (reply : Barrier) : Prop :=
  ∃ before prefixFrames frame suffix permit, frames = prefixFrames ++ frame :: suffix ∧
    replay rules lineage origin prefixFrames = some before ∧ Eligible lineage before frame ∧
    (decide rules lineage before frame.command).2 = .admitted permit reply

private theorem replay_preserves_provenance
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (origin : Image slots capacity Payload) (chosen suffix : List (Frame slots capacity Payload Ticket))
    (prefixFrames : List (Frame slots capacity Payload Ticket)) (before last : Image slots capacity Payload)
    (whole : chosen = prefixFrames ++ suffix)
    (reached : replay rules lineage origin prefixFrames = some before)
    (sound : SoundFor width rules.snapshot (ChosenAdmission rules lineage origin chosen) before.reads)
    (replayed : replay rules lineage before suffix = some last) :
    SoundFor width rules.snapshot (ChosenAdmission rules lineage origin chosen) last.reads := by
  induction suffix generalizing prefixFrames before with
  | nil =>
      have same : before = last := by simpa [replay] using replayed
      exact same ▸ sound
  | cons frame suffix next =>
      by_cases eligible : Eligible lineage before frame
      · let after := (decide rules lineage before frame.command).1
        have advanced : step rules lineage before frame = some after := by simp [step, eligible, after]
        have proceeded : replay rules lineage before [frame] = some after := by simp [replay, advanced]
        have reachedAfter : replay rules lineage origin (prefixFrames ++ [frame]) = some after :=
          (replay_after_a_certified_combined_base rules lineage prefixFrames [frame] reached).trans proceeded
        have afterSound : SoundFor width rules.snapshot (ChosenAdmission rules lineage origin chosen) after.reads :=
          read_book_invariant_preserved rules lineage before frame.command _ sound
            (fun permit reply checked => ⟨before, prefixFrames, frame, suffix, permit, whole, reached, eligible, checked⟩)
        have suffixResult : replay rules lineage after suffix = some last := by simpa [replay, advanced] using replayed
        exact next _ after (by simpa [List.append_assoc] using whole) reachedAfter afterSound suffixResult
      · have blocked : step rules lineage before frame = none := by simp [step, eligible]
        simp [replay, blocked] at replayed

theorem every_recovered_live_row_comes_from_a_chosen_protected_admission
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity Payload Ticket)}
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    {origin : Image slots capacity Payload} (cut : Cut ledger) (base : Base rules lineage origin cut.frames)
    (physical : List (Frame slots capacity Payload Ticket)) {after : Image slots capacity Payload}
    (initial : SnapshotAdmission.Sound rules.snapshot origin.reads.view)
    (empty : ∀ slot, origin.reads.rows slot = none)
    (reopened : reopen rules lineage cut base physical = some after) :
    SoundFor width rules.snapshot (ChosenAdmission rules lineage origin cut.frames) after.reads := by
  have start : SoundFor width rules.snapshot (ChosenAdmission rules lineage origin cut.frames) origin.reads := by
    refine ⟨initial, ?_, ?_, ?_⟩ <;> simp [RecoverableRead.UniqueRows, empty]
  exact replay_preserves_provenance rules lineage origin cut.frames cut.frames [] origin after rfl rfl start
    (any_successful_reopen_is_exact rules lineage cut base physical reopened)

structure Serving (width slots capacity : Nat) (Payload : Type) where
  current : Image slots capacity Payload → Prop
  needs : SnapshotAdmission.Basis → EnvelopeCodec.Field width → Prop
  retained : EnvelopeCodec.Field width → Prop

def Serving.Ready (serving : Serving width slots capacity Payload) (after : Image slots capacity Payload) : Prop :=
  serving.current after ∧ ∀ object, JointReadRecovery.Needs serving.needs after.reads object → serving.retained object

noncomputable def recoverReply {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity Payload Ticket)}
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    {origin : Image slots capacity Payload} (cut : Cut ledger) (base : Base rules lineage origin cut.frames)
    (physical : List (Frame slots capacity Payload Ticket)) (serving : Serving width slots capacity Payload)
    (call : Invocation) (authenticate : Invocation → Prop)
    (sign : RTDBFailover.Route → EnvelopeCodec.Bytes → Signature) : Option (AppliedBarrierReceipt.Packet Signature) := by
  classical
  exact do
    let recovered ← reopen rules lineage cut base physical
    if serving.Ready recovered then RecoverableRead.recoverInvocation width recovered.reads call authenticate sign
    else none

theorem historical_admission_is_insufficient_when_current_custody_or_authority_is_missing
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity Payload Ticket)}
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    {origin : Image slots capacity Payload} (cut : Cut ledger) (base : Base rules lineage origin cut.frames)
    (physical : List (Frame slots capacity Payload Ticket)) (serving : Serving width slots capacity Payload)
    (call : Invocation) (authenticate : Invocation → Prop) (sign : RTDBFailover.Route → EnvelopeCodec.Bytes → Signature)
    (after : Image slots capacity Payload) (reopened : reopen rules lineage cut base physical = some after)
    (unavailable : ¬ serving.Ready after) :
    recoverReply rules lineage cut base physical serving call authenticate sign = none := by
  simp [recoverReply, reopened, unavailable]

theorem an_authenticated_live_invocation_recovers_without_recontacting_historical_issuers
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity Payload Ticket)}
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    {origin : Image slots capacity Payload} (cut : Cut ledger) (base : Base rules lineage origin cut.frames)
    (physical : List (Frame slots capacity Payload Ticket)) (serving : Serving width slots capacity Payload)
    (authenticate : Invocation → Prop) (sign : RTDBFailover.Route → EnvelopeCodec.Bytes → Signature)
    {after : Image slots capacity Payload} (reopened : reopen rules lineage cut base physical = some after)
    (initial : SnapshotAdmission.Sound rules.snapshot origin.reads.view) (empty : ∀ slot, origin.reads.rows slot = none)
    (ready : serving.Ready after) (slot : Fin capacity) (row : Row) (found : after.reads.rows slot = some row)
    (caller : authenticate row.reply.invocation) :
    let body := AppliedBarrierReceipt.encode width row.reply
    recoverReply rules lineage cut base physical serving row.reply.invocation authenticate sign =
      some ⟨body, sign (AppliedBarrierReceipt.sourceOf row.reply.invocation) body⟩ := by
  have sound := every_recovered_live_row_comes_from_a_chosen_protected_admission rules lineage cut base physical
    initial empty reopened
  simpa [recoverReply, reopened, ready] using
    RecoverableRead.the_original_invocation_can_recover_even_if_the_permit_reply_was_lost
      sound slot row authenticate sign found caller

#print axioms a_rival_or_missing_read_operation_cannot_reopen
#print axioms reopening_with_exact_coverage_uses_the_whole_chosen_history
#print axioms both_selectable_bases_recover_one_journal_and_read_book
#print axioms a_bare_journal_marker_cannot_admit_a_read
#print axioms every_admitted_reply_is_the_exact_marker_and_attested_basis
#print axioms a_stale_close_cannot_release_a_reused_slot
#print axioms a_sealed_source_cannot_choose_a_logical_release
#print axioms an_applied_close_clears_its_result_and_hold_at_one_ordered_position
#print axioms every_recovered_live_row_comes_from_a_chosen_protected_admission
#print axioms historical_admission_is_insufficient_when_current_custody_or_authority_is_missing
#print axioms an_authenticated_live_invocation_recovers_without_recontacting_historical_issuers

end OrderedReadReplay
