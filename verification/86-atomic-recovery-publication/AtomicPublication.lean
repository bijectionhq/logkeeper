import RankedNamedRecovery

set_option warningAsError true

namespace AtomicPublication

open ChosenReplay (Lineage)
open OrderedReadReplay (Frame Image Rules replay)
open RankedNamedRecovery (Capture Publication Store Staged Target cutoff)
open ConfigurationClosure (Generation)

variable {width slots capacity : Nat} {Payload Ticket Voter : Type}

structure Stamp (slots capacity : Nat) (Payload Ticket : Type) where
  lineage : Lineage
  revision : Nat
  frontier : List (Frame slots capacity Payload Ticket)
  session : Nat

structure Endpoint (slots capacity : Nat) (Payload Ticket : Type) where
  stamp : Stamp slots capacity Payload Ticket
  opened : Option (Image slots capacity Payload)

structure Candidate (rules : Rules width slots capacity Payload Ticket) (origin : Image slots capacity Payload) where
  private mk ::
  stamp : Stamp slots capacity Payload Ticket
  image : Image slots capacity Payload
  applied : replay rules stamp.lineage origin stamp.frontier = some image

def Candidate.fromRanked
    {rules : Rules width slots capacity Payload Ticket} {store : Store width slots capacity Payload Ticket}
    {source : Generation Voter (Frame slots capacity Payload Ticket)}
    {lineage : Lineage} {origin : Image slots capacity Payload}
    {capture : Capture source} {successor : Nat} {publication : Publication rules store source lineage origin}
    {media : List (Frame slots capacity Payload Ticket)}
    (staged : Staged capture successor publication media) (target : Target Voter slots capacity Payload Ticket)
    (captured : Stamp slots capacity Payload Ticket)
    (scope : captured.lineage = lineage ∧ captured.revision = successor ∧ captured.frontier = cutoff capture)
    (image : Image slots capacity Payload)
    (activated : RankedNamedRecovery.activate staged target = some image) :
    Candidate rules origin := by
  refine ⟨captured, image, ?_⟩
  rw [scope.1, scope.2.2]
  exact (RankedNamedRecovery.activation_requires_current_quorum_installation_of_the_exact_recovered_image
    staged target activated).2.2.2.2

def CanAttach (endpoint : Endpoint slots capacity Payload Ticket)
    (stamp : Stamp slots capacity Payload Ticket) : Prop :=
  endpoint.stamp = stamp ∧ endpoint.opened = none

theorem attachment_compares_the_entire_current_stamp_and_empty_slot
    (endpoint : Endpoint slots capacity Payload Ticket) (stamp : Stamp slots capacity Payload Ticket) :
    CanAttach endpoint stamp ↔ endpoint.stamp = stamp ∧ endpoint.opened = none := by
  exact Iff.rfl

noncomputable def attach {rules : Rules width slots capacity Payload Ticket} {origin : Image slots capacity Payload}
    (endpoint : Endpoint slots capacity Payload Ticket) (candidate : Candidate rules origin) :
    Option (Endpoint slots capacity Payload Ticket) := by
  classical
  exact if CanAttach endpoint candidate.stamp then
    some {endpoint with opened := some candidate.image}
  else none

def Sound (rules : Rules width slots capacity Payload Ticket) (origin : Image slots capacity Payload)
    (endpoint : Endpoint slots capacity Payload Ticket) : Prop :=
  ∀ image, endpoint.opened = some image →
    replay rules endpoint.stamp.lineage origin endpoint.stamp.frontier = some image

theorem attachment_at_effect_time_binds_the_exact_applied_image
    {rules : Rules width slots capacity Payload Ticket} {origin : Image slots capacity Payload}
    (before after : Endpoint slots capacity Payload Ticket) (candidate : Candidate rules origin)
    (attached : attach before candidate = some after) :
    before.stamp = candidate.stamp ∧ before.opened = none ∧ after.stamp = before.stamp ∧
    after.opened = some candidate.image ∧ Sound rules origin after := by
  unfold attach at attached
  split at attached
  · next permitted =>
      cases attached
      obtain ⟨bound, empty⟩ := (attachment_compares_the_entire_current_stamp_and_empty_slot _ _).1 permitted
      refine ⟨bound, empty, rfl, rfl, ?_⟩
      intro image visible
      cases Option.some.inj visible
      simpa [bound] using candidate.applied
  · simp at attached

theorem the_current_empty_endpoint_can_attach_the_chosen_recovered_image
    {rules : Rules width slots capacity Payload Ticket} {origin : Image slots capacity Payload}
    (endpoint : Endpoint slots capacity Payload Ticket) (candidate : Candidate rules origin)
    (bound : endpoint.stamp = candidate.stamp) (empty : endpoint.opened = none) :
    attach endpoint candidate = some {endpoint with opened := some candidate.image} := by
  have permitted := (attachment_compares_the_entire_current_stamp_and_empty_slot _ _).2 ⟨bound, empty⟩
  simp [attach, permitted]

theorem an_already_attached_endpoint_refuses_every_replacement_by_recovery
    {rules : Rules width slots capacity Payload Ticket} {origin : Image slots capacity Payload}
    (endpoint : Endpoint slots capacity Payload Ticket) (candidate : Candidate rules origin)
    (image : Image slots capacity Payload) (visible : endpoint.opened = some image) :
    attach endpoint candidate = none := by
  have blocked : ¬ CanAttach endpoint candidate.stamp := by
    intro permitted
    have empty := (attachment_compares_the_entire_current_stamp_and_empty_slot _ _).1 permitted |>.2
    simp [visible] at empty
  simp [attach, blocked]

theorem an_exact_precheck_does_not_authorize_publication_after_the_stamp_changes
    {rules : Rules width slots capacity Payload Ticket} {origin : Image slots capacity Payload}
    (checked now : Endpoint slots capacity Payload Ticket) (candidate : Candidate rules origin)
    (precheck : CanAttach checked candidate.stamp) (changed : now.stamp ≠ checked.stamp) :
    attach now candidate = none := by
  have previous := (attachment_compares_the_entire_current_stamp_and_empty_slot _ _).1 precheck |>.1
  have refused : ¬ CanAttach now candidate.stamp := by
    intro permitted
    have binding := (attachment_compares_the_entire_current_stamp_and_empty_slot _ _).1 permitted |>.1
    exact changed (binding.trans previous.symm)
  simp [attach, refused]

def NoRollback (old new : Stamp slots capacity Payload Ticket) : Prop :=
  old.lineage = new.lineage ∧ old.revision ≤ new.revision ∧ old.frontier <+: new.frontier ∧ old.session ≤ new.session

theorem no_rollback_is_transitive {first middle last : Stamp slots capacity Payload Ticket}
    (earlier : NoRollback first middle) (later : NoRollback middle last) : NoRollback first last :=
  ⟨earlier.1.trans later.1, Nat.le_trans earlier.2.1 later.2.1,
    earlier.2.2.1.trans later.2.2.1, Nat.le_trans earlier.2.2.2 later.2.2.2⟩

noncomputable def observe (endpoint : Endpoint slots capacity Payload Ticket)
    (known : Stamp slots capacity Payload Ticket) : Option (Endpoint slots capacity Payload Ticket) := by
  classical
  exact if NoRollback endpoint.stamp known ∧ endpoint.stamp ≠ known then some ⟨known, none⟩
  else none

theorem advancing_an_observation_clears_the_old_slot_in_the_same_step
    (before after : Endpoint slots capacity Payload Ticket) (known : Stamp slots capacity Payload Ticket)
    (observed : observe before known = some after) :
    NoRollback before.stamp after.stamp ∧ after.stamp = known ∧
    after.opened = none ∧ before.stamp ≠ after.stamp := by
  unfold observe at observed
  split at observed
  · next valid =>
      cases observed
      exact ⟨valid.1, rfl, rfl, valid.2⟩
  · simp at observed

theorem an_increased_component_cannot_return_to_the_old_stamp
    (old changed latest : Stamp slots capacity Payload Ticket)
    (progress : NoRollback old changed) (different : old ≠ changed)
    (later : NoRollback changed latest) :
    latest ≠ old := by
  intro rolledBack
  subst latest
  have revision := Nat.le_antisymm progress.2.1 later.2.1
  have session := Nat.le_antisymm progress.2.2.2 later.2.2.2
  have frontier := progress.2.2.1.eq_of_length_le later.2.2.1.length_le
  cases old
  cases changed
  simp_all [NoRollback]

structure ChosenExtension {Voter : Type}
    (ledger : PrefixAgreement.Ledger Voter (Frame slots capacity Payload Ticket))
    (stamp : Stamp slots capacity Payload Ticket) where
  ballot : Nat
  suffix : List (Frame slots capacity Payload Ticket)
  chosen : PrefixAgreement.Chosen ledger ballot (stamp.frontier ++ suffix)

structure JournalScope (Voter : Type) (slots capacity : Nat) (Payload Ticket : Type) where
  lineage : Lineage
  revision : Nat
  ledger : PrefixAgreement.Ledger Voter (Frame slots capacity Payload Ticket)

def JournalScope.Matches (journal : JournalScope Voter slots capacity Payload Ticket)
    (stamp : Stamp slots capacity Payload Ticket) : Prop :=
  journal.lineage = stamp.lineage ∧ journal.revision = stamp.revision

def Candidate.fromReopen
    (rules : Rules width slots capacity Payload Ticket) {origin : Image slots capacity Payload}
    (captured : Stamp slots capacity Payload Ticket) (journal : JournalScope Voter slots capacity Payload Ticket)
    (_scope : journal.Matches captured) (cut : OrderedReadReplay.Cut journal.ledger)
    (frontier : cut.frames = captured.frontier)
    (base : OrderedReadReplay.Base rules captured.lineage origin cut.frames) (media : List (Frame slots capacity Payload Ticket))
    (image : Image slots capacity Payload) (recovered : OrderedReadReplay.reopen rules captured.lineage cut base media = some image) :
    Candidate rules origin := by
  refine ⟨captured, image, ?_⟩
  rw [← frontier]
  exact OrderedReadReplay.any_successful_reopen_is_exact rules captured.lineage cut base media recovered

theorem a_new_process_can_attach_the_already_installed_journals_later_certified_cut
    (rules : Rules width slots capacity Payload Ticket) {origin : Image slots capacity Payload}
    (before : Endpoint slots capacity Payload Ticket) (journal : JournalScope Voter slots capacity Payload Ticket)
    (scope : journal.Matches before.stamp) (cut : OrderedReadReplay.Cut journal.ledger)
    (frontier : cut.frames = before.stamp.frontier)
    (base : OrderedReadReplay.Base rules before.stamp.lineage origin cut.frames) (media : List (Frame slots capacity Payload Ticket))
    (image : Image slots capacity Payload) (recovered : OrderedReadReplay.reopen rules before.stamp.lineage cut base media = some image)
    (empty : before.opened = none) :
    attach before (Candidate.fromReopen rules before.stamp journal scope cut frontier base media image recovered) =
      some {before with opened := some image} :=
  the_current_empty_endpoint_can_attach_the_chosen_recovered_image before _ rfl empty

noncomputable def applyChosen (rules : Rules width slots capacity Payload Ticket)
    (before : Endpoint slots capacity Payload Ticket) (journal : JournalScope Voter slots capacity Payload Ticket)
    (extension : ChosenExtension journal.ledger before.stamp) : Option (Endpoint slots capacity Payload Ticket) := by
  classical
  exact if journal.Matches before.stamp then do
    let current ← before.opened
    let next ← replay rules before.stamp.lineage current extension.suffix
    some ⟨{before.stamp with frontier := before.stamp.frontier ++ extension.suffix}, some next⟩
  else none

theorem a_chosen_extension_from_another_scope_cannot_replace_the_live_book
    (rules : Rules width slots capacity Payload Ticket)
    (before : Endpoint slots capacity Payload Ticket) (journal : JournalScope Voter slots capacity Payload Ticket)
    (extension : ChosenExtension journal.ledger before.stamp) (foreign : ¬ journal.Matches before.stamp) :
    applyChosen rules before journal extension = none := by
  simp [applyChosen, foreign]

theorem applying_a_chosen_suffix_keeps_a_single_exact_serving_image
    (rules : Rules width slots capacity Payload Ticket) (origin : Image slots capacity Payload)
    (before after : Endpoint slots capacity Payload Ticket) (journal : JournalScope Voter slots capacity Payload Ticket)
    (extension : ChosenExtension journal.ledger before.stamp)
    (sound : Sound rules origin before) (applied : applyChosen rules before journal extension = some after) :
    NoRollback before.stamp after.stamp ∧ after.stamp.frontier = before.stamp.frontier ++ extension.suffix ∧
    Sound rules origin after := by
  have sameScope : journal.Matches before.stamp := by
    by_cases valid : journal.Matches before.stamp
    · exact valid
    · simp [applyChosen, valid] at applied
  cases visible : before.opened with
  | none => simp [applyChosen, sameScope, visible] at applied
  | some first =>
      cases replayed : replay rules before.stamp.lineage first extension.suffix with
      | none => simp [applyChosen, sameScope, visible, replayed] at applied
      | some second =>
          simp [applyChosen, sameScope, visible, replayed] at applied
          subst after
          refine ⟨⟨rfl, Nat.le_refl _, ⟨extension.suffix, rfl⟩, Nat.le_refl _⟩, rfl, ?_⟩
          intro image exactly
          cases Option.some.inj exactly
          change replay rules before.stamp.lineage origin (before.stamp.frontier ++ extension.suffix) = some second
          rw [OrderedReadReplay.replay_after_a_certified_combined_base rules _ _ _ (sound first visible)]
          exact replayed

inductive Step (rules : Rules width slots capacity Payload Ticket) (origin : Image slots capacity Payload)
    (Voter : Type) : Endpoint slots capacity Payload Ticket → Endpoint slots capacity Payload Ticket → Prop
  | attach {before after} (candidate : Candidate rules origin)
      (accepted : attach before candidate = some after) : Step rules origin Voter before after
  | observe {before after} (known : Stamp slots capacity Payload Ticket)
      (accepted : observe before known = some after) : Step rules origin Voter before after
  | apply {before after} (journal : JournalScope Voter slots capacity Payload Ticket)
      (extension : ChosenExtension journal.ledger before.stamp)
      (accepted : applyChosen rules before journal extension = some after) : Step rules origin Voter before after

inductive Trace (rules : Rules width slots capacity Payload Ticket) (origin : Image slots capacity Payload)
    (Voter : Type) : Endpoint slots capacity Payload Ticket → Endpoint slots capacity Payload Ticket → Prop
  | nil (state : Endpoint slots capacity Payload Ticket) : Trace rules origin Voter state state
  | next {first before after} : Trace rules origin Voter first before →
      Step rules origin Voter before after → Trace rules origin Voter first after

theorem every_interleaving_preserves_exact_publication_and_monotone_progress
    (rules : Rules width slots capacity Payload Ticket) (origin : Image slots capacity Payload)
    {first last : Endpoint slots capacity Payload Ticket}
    (initial : Sound rules origin first) (trace : Trace rules origin Voter first last) :
    NoRollback first.stamp last.stamp ∧ Sound rules origin last := by
  induction trace with
  | nil => exact ⟨⟨rfl, Nat.le_refl _, List.prefix_rfl, Nat.le_refl _⟩, initial⟩
  | next _ operation earlier =>
      rcases earlier with ⟨progress, sound⟩
      cases operation with
      | attach candidate applied =>
          obtain ⟨_, _, same, _, correct⟩ := attachment_at_effect_time_binds_the_exact_applied_image _ _ candidate applied
          exact ⟨same.symm ▸ progress, correct⟩
      | observe known applied =>
          obtain ⟨monotone, _, cleared, _⟩ := advancing_an_observation_clears_the_old_slot_in_the_same_step _ _ known applied
          exact ⟨no_rollback_is_transitive progress monotone, by simp [Sound, cleared]⟩
      | apply journal extension applied =>
          obtain ⟨monotone, _, correct⟩ := applying_a_chosen_suffix_keeps_a_single_exact_serving_image
            rules origin _ _ journal extension sound applied
          exact ⟨no_rollback_is_transitive progress monotone, correct⟩

structure ReachabilityObservation where
  returnedVotes : List Nat
  actualReachable : Bool

theorem delayed_messages_cannot_certify_instantaneous_reachability
    (detect : List Nat → Bool) (observations : List Nat) :
    ¬ (∀ world : ReachabilityObservation, world.returnedVotes = observations →
      detect world.returnedVotes = world.actualReachable) := by
  intro exact
  have reachable := exact ⟨observations, true⟩ rfl
  have unreachable := exact ⟨observations, false⟩ rfl
  have impossible : true = false := reachable.symm.trans unreachable
  cases impossible

open RTDBFailover (Invocation Route)
open RecoverableRead (Permit Row)
open SnapshotAdmission (Basis)
open AppliedBarrierReceipt (Packet)

variable {Borrow Signature : Type}

structure ReadGate (slots capacity : Nat) (Payload Ticket Borrow : Type) where
  authority : Stamp slots capacity Payload Ticket → Invocation → Prop
  authenticate : Invocation → Prop
  reserve : Stamp slots capacity Payload Ticket → Invocation → Permit capacity → Basis → Borrow → Prop

def ReadGate.MayStart (gate : ReadGate slots capacity Payload Ticket Borrow)
    (stamp : Stamp slots capacity Payload Ticket) (call : Invocation) : Prop :=
  gate.authority stamp call ∧ gate.authenticate call

theorem starting_fresh_use_requires_its_own_ordered_authorization
    (gate : ReadGate slots capacity Payload Ticket Borrow) (stamp : Stamp slots capacity Payload Ticket)
    (call : Invocation) :
    gate.MayStart stamp call ↔ gate.authority stamp call ∧ gate.authenticate call := by
  exact Iff.rfl

structure ReplyUse (capacity : Nat) (Borrow Signature : Type) where
  private mk ::
  call : Invocation
  permit : Permit capacity
  basis : Basis
  borrow : Borrow
  packet : Packet Signature

noncomputable def beginReply (width : Nat)
    (endpoint : Endpoint slots capacity Payload Ticket) (gate : ReadGate slots capacity Payload Ticket Borrow)
    (call : Invocation) (borrow : Borrow) (sign : Route → EnvelopeCodec.Bytes → Signature) :
    Option (ReplyUse capacity Borrow Signature) := by
  classical
  exact if gate.MayStart endpoint.stamp call then do
    let image ← endpoint.opened
    let permit ← (List.finRange capacity).findSome? (RecoverableRead.permitAt image.reads call)
    let basis ← image.reads.view.snapshots permit.serial
    if gate.reserve endpoint.stamp call permit basis borrow then
      let packet ← RecoverableRead.reissue width image.reads permit call sign
      some ⟨call, permit, basis, borrow, packet⟩
    else none
  else none

noncomputable def finishReply (use : ReplyUse capacity Borrow Signature)
    (held : Invocation → Permit capacity → Basis → Borrow → Prop) : Option (Packet Signature) := by
  classical
  exact if held use.call use.permit use.basis use.borrow then some use.packet else none

structure ChosenDelivery (rules : Rules width slots capacity Payload Ticket)
    (journal : JournalScope Voter slots capacity Payload Ticket) (origin : Image slots capacity Payload) where
  history : List (Frame slots capacity Payload Ticket)
  before : Image slots capacity Payload
  request : OrderedReadReplay.Delivery capacity
  evidence : Ticket
  ballot : Nat
  reply : RTDBFailover.Barrier
  applied : replay rules journal.lineage origin history = some before
  chosen : PrefixAgreement.Chosen journal.ledger ballot
    (history ++ [OrderedReadReplay.deliveryFrame journal.lineage before request evidence])
  accepted : OrderedReadReplay.decideDelivery rules journal.lineage before request evidence = .delivery reply

noncomputable def authorizeDelivery (rules : Rules width slots capacity Payload Ticket)
    (journal : JournalScope Voter slots capacity Payload Ticket) (origin : Image slots capacity Payload)
    (history : List (Frame slots capacity Payload Ticket)) (before : Image slots capacity Payload)
    (request : OrderedReadReplay.Delivery capacity) (evidence : Ticket) (ballot : Nat)
    (applied : replay rules journal.lineage origin history = some before)
    (chosen : PrefixAgreement.Chosen journal.ledger ballot
      (history ++ [OrderedReadReplay.deliveryFrame journal.lineage before request evidence])) :
    Option (ChosenDelivery rules journal origin) :=
  match decided : OrderedReadReplay.decideDelivery rules journal.lineage before request evidence with
  | .delivery reply => some ⟨history, before, request, evidence, ballot, reply, applied, chosen, decided⟩
  | _ => none

def beginChosenReply
    {rules : Rules width slots capacity Payload Ticket}
    {journal : JournalScope Voter slots capacity Payload Ticket} {origin : Image slots capacity Payload}
    (selected : ChosenDelivery rules journal origin) (sign : Route → EnvelopeCodec.Bytes → Signature) :
    ReplyUse capacity Ticket Signature :=
  let body := AppliedBarrierReceipt.encode width selected.reply
  ⟨selected.request.call, selected.request.permit, selected.request.basis, selected.evidence,
    ⟨body, sign (AppliedBarrierReceipt.sourceOf selected.request.call) body⟩⟩

theorem an_attached_image_alone_cannot_start_a_recovered_reply (width : Nat)
    (endpoint : Endpoint slots capacity Payload Ticket) (gate : ReadGate slots capacity Payload Ticket Borrow)
    (call : Invocation) (borrow : Borrow) (sign : Route → EnvelopeCodec.Bytes → Signature)
    (refused : ¬ gate.authority endpoint.stamp call) :
    beginReply width endpoint gate call borrow sign = none := by
  have unavailable : ¬ gate.MayStart endpoint.stamp call :=
    fun starts => refused ((starting_fresh_use_requires_its_own_ordered_authorization _ _ _).1 starts).1
  simp [beginReply, unavailable]

theorem beginning_reissue_binds_the_original_book_and_exact_protected_basis (width : Nat)
    (endpoint : Endpoint slots capacity Payload Ticket) (gate : ReadGate slots capacity Payload Ticket Borrow)
    (call : Invocation) (borrow : Borrow) (sign : Route → EnvelopeCodec.Bytes → Signature)
    (use : ReplyUse capacity Borrow Signature) (begun : beginReply width endpoint gate call borrow sign = some use) :
    use.call = call ∧ use.borrow = borrow ∧ gate.authority endpoint.stamp call ∧ gate.authenticate call ∧
    ∃ image, endpoint.opened = some image ∧ image.reads.view.snapshots use.permit.serial = some use.basis ∧
      gate.reserve endpoint.stamp call use.permit use.basis borrow ∧
      RecoverableRead.reissue width image.reads use.permit call sign = some use.packet := by
  classical
  by_cases starts : gate.MayStart endpoint.stamp call
  · have scope := (starting_fresh_use_requires_its_own_ordered_authorization _ _ _).1 starts
    cases opened : endpoint.opened with
    | none => simp [beginReply, starts, opened] at begun
    | some image =>
        cases found : (List.finRange capacity).findSome? (RecoverableRead.permitAt image.reads call) with
        | none => simp [beginReply, starts, opened, found] at begun
        | some permit =>
            cases held : image.reads.view.snapshots permit.serial with
            | none => simp [beginReply, starts, opened, found, held] at begun
            | some basis =>
                by_cases reserve : gate.reserve endpoint.stamp call permit basis borrow
                · cases receipt : RecoverableRead.reissue width image.reads permit call sign with
                  | none => simp [beginReply, starts, opened, found, held, receipt] at begun
                  | some packet =>
                      simp [beginReply, starts, opened, found, held, reserve, receipt] at begun
                      subst use
                      exact ⟨rfl, rfl, scope.1, scope.2, image, rfl, held, reserve, receipt⟩
                · simp [beginReply, starts, opened, found, held, reserve] at begun
  · simp [beginReply, starts] at begun

theorem an_exact_authorized_live_read_can_recover_without_its_lost_permit (width : Nat)
    (endpoint : Endpoint slots capacity Payload Ticket) (gate : ReadGate slots capacity Payload Ticket Borrow)
    (borrow : Borrow) (sign : Route → EnvelopeCodec.Bytes → Signature)
    (image : Image slots capacity Payload) (opened : endpoint.opened = some image)
    (slot : Fin capacity) (row : Row) (found : image.reads.rows slot = some row)
    (unique : RecoverableRead.UniqueRows (fun item => item.reply.invocation) image.reads.rows)
    (basis : Basis) (held : image.reads.view.snapshots row.serial = some basis) (exactCut : basis.stop = row.reply.cut)
    (authority : gate.authority endpoint.stamp row.reply.invocation) (caller : gate.authenticate row.reply.invocation)
    (paid : gate.reserve endpoint.stamp row.reply.invocation ⟨slot, row.serial⟩ basis borrow) :
    ∃ use, beginReply width endpoint gate row.reply.invocation borrow sign = some use ∧
      use.permit = ⟨slot, row.serial⟩ ∧ use.basis = basis ∧
      use.packet = ⟨AppliedBarrierReceipt.encode width row.reply, sign
        (AppliedBarrierReceipt.sourceOf row.reply.invocation) (AppliedBarrierReceipt.encode width row.reply)⟩ := by
  classical
  have scope := (starting_fresh_use_requires_its_own_ordered_authorization _ _ _).2 ⟨authority, caller⟩
  have located := RecoverableRead.the_exact_live_permit_is_found_by_its_invocation image.reads slot row found unique
  let body := AppliedBarrierReceipt.encode width row.reply
  let packet := (⟨body, sign (AppliedBarrierReceipt.sourceOf row.reply.invocation) body⟩ : Packet Signature)
  refine ⟨⟨row.reply.invocation, ⟨slot, row.serial⟩, basis, borrow, packet⟩, ?_, rfl, rfl, rfl⟩
  have receipt := RecoverableRead.a_live_row_can_reissue_without_loading_the_marker_frame
    width image.reads ⟨slot, row.serial⟩ row basis sign found rfl held exactCut
  simp [beginReply, scope, opened, located, held, paid, receipt, packet, body]

theorem an_admitted_reply_can_finish_using_its_own_still_held_borrow
    (use : ReplyUse capacity Borrow Signature)
    (held : Invocation → Permit capacity → Basis → Borrow → Prop)
    (stillHeld : held use.call use.permit use.basis use.borrow) :
    finishReply use held = some use.packet := by
  simp [finishReply, stillHeld]

theorem an_admitted_reply_cannot_finish_after_its_own_borrow_is_stopped
    (use : ReplyUse capacity Borrow Signature)
    (held : Invocation → Permit capacity → Basis → Borrow → Prop)
    (stopped : ¬ held use.call use.permit use.basis use.borrow) :
    finishReply use held = none := by
  simp [finishReply, stopped]

#print axioms attachment_compares_the_entire_current_stamp_and_empty_slot
#print axioms attachment_at_effect_time_binds_the_exact_applied_image
#print axioms the_current_empty_endpoint_can_attach_the_chosen_recovered_image
#print axioms an_already_attached_endpoint_refuses_every_replacement_by_recovery
#print axioms an_exact_precheck_does_not_authorize_publication_after_the_stamp_changes
#print axioms no_rollback_is_transitive
#print axioms advancing_an_observation_clears_the_old_slot_in_the_same_step
#print axioms an_increased_component_cannot_return_to_the_old_stamp
#print axioms a_new_process_can_attach_the_already_installed_journals_later_certified_cut
#print axioms a_chosen_extension_from_another_scope_cannot_replace_the_live_book
#print axioms applying_a_chosen_suffix_keeps_a_single_exact_serving_image
#print axioms every_interleaving_preserves_exact_publication_and_monotone_progress
#print axioms delayed_messages_cannot_certify_instantaneous_reachability
#print axioms starting_fresh_use_requires_its_own_ordered_authorization
#print axioms an_attached_image_alone_cannot_start_a_recovered_reply
#print axioms beginning_reissue_binds_the_original_book_and_exact_protected_basis
#print axioms an_exact_authorized_live_read_can_recover_without_its_lost_permit
#print axioms an_admitted_reply_can_finish_using_its_own_still_held_borrow
#print axioms an_admitted_reply_cannot_finish_after_its_own_borrow_is_stopped

end AtomicPublication
