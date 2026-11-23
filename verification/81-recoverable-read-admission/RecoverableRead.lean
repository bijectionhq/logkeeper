import AppliedBarrierReceipt

set_option warningAsError true

namespace RecoverableRead

open RTDBFailover (Invocation Route Barrier barrierAt)
open AppliedBarrierReceipt (ChosenMarker Fits Issuable Packet)
open JointSource (Rules Image Frame)
open SnapshotAdmission (Environment View Basis Protected setSlot)

variable {capacity width slots : Nat} {Payload Ticket Voter Signature : Type}

structure Permit (capacity : Nat) where
  slot : Fin capacity
  serial : Nat

structure Row where
  serial : Nat
  reply : Barrier

structure State (capacity : Nat) where
  view : View
  rows : Fin capacity → Option Row

def setRow (rows : Fin capacity → Option Row) (slot : Fin capacity) (row : Option Row) :
    Fin capacity → Option Row :=
  fun candidate => if candidate = slot then row else rows candidate

def captured (state : State capacity) (slot : Fin capacity) (reply : Barrier) : State capacity × Permit capacity :=
  let serial := state.view.issued + 1
  (⟨SnapshotAdmission.snapshotView state.view, setRow state.rows slot (some ⟨serial, reply⟩)⟩, ⟨slot, serial⟩)

def Reservable (width : Nat) (env : Environment) (state : State capacity) (slot : Fin capacity)
    (reply : Barrier) : Prop :=
  state.view.head = reply.cut ∧ state.rows slot = none ∧ env.canReserve state.view ∧
    state.view.issued + 1 < EnvelopeCodec.wordLimit width ∧ Fits width reply ∧
    (∀ occupied prior, state.rows occupied = some prior → prior.reply.invocation ≠ reply.invocation)

noncomputable def admit (env : Environment)
    {rules : Rules width slots Payload Ticket} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    {origin : Image slots Payload} {call : Invocation}
    (state : State capacity) (current : Image slots Payload)
    (marker : ChosenMarker rules ledger origin call) (slot : Fin capacity) : Option (State capacity × Permit capacity) := by
  classical
  let reply := barrierAt call marker.before
  exact if marker.before = current ∧ marker.result = .stream (.readCut call.nonce reply.cut) ∧
      Reservable width env state slot reply then
    some (captured state slot reply)
  else none

def cleared (state : State capacity) (permit : Permit capacity) : State capacity :=
  ⟨{state.view with snapshots := setSlot state.view.snapshots permit.serial none}, setRow state.rows permit.slot none⟩

noncomputable def close (env : Environment) (state : State capacity) (permit : Permit capacity) :
    Option (State capacity) := by
  classical
  exact match state.rows permit.slot with
  | some row =>
      if row.serial = permit.serial ∧ env.drained state.view permit.serial then some (cleared state permit) else none
  | none => none

noncomputable def reissue (width : Nat) (state : State capacity) (permit : Permit capacity)
    (call : Invocation) (sign : Route → EnvelopeCodec.Bytes → Signature) : Option (Packet Signature) := by
  classical
  exact do
    let row ← state.rows permit.slot
    let basis ← state.view.snapshots permit.serial
    if row.serial = permit.serial ∧ row.reply.invocation = call ∧ basis.stop = row.reply.cut then
      let body := AppliedBarrierReceipt.encode width row.reply
      some ⟨body, sign (AppliedBarrierReceipt.sourceOf row.reply.invocation) body⟩
    else none

noncomputable def permitAt (state : State capacity) (call : Invocation) (slot : Fin capacity) :
    Option (Permit capacity) := by
  classical
  exact (state.rows slot).bind fun row =>
    if row.reply.invocation = call then some ⟨slot, row.serial⟩ else none

noncomputable def recoverInvocation (width : Nat) (state : State capacity) (call : Invocation)
    (authenticate : Invocation → Prop) (sign : Route → EnvelopeCodec.Bytes → Signature) : Option (Packet Signature) := by
  classical
  exact if authenticate call then
    ((List.finRange capacity).findSome? (permitAt state call)).bind fun permit =>
      reissue width state permit call sign
  else none

def UniqueRows (key : Row → Value) (rows : Fin capacity → Option Row) : Prop :=
  ∀ left right first second, rows left = some first → rows right = some second →
    key first = key second → left = right

private theorem insert_preserves_unique_keys (key : Row → Value)
    (rows : Fin capacity → Option Row) (slot : Fin capacity) (row : Row)
    (unique : UniqueRows key rows)
    (fresh : ∀ other previous, rows other = some previous → key previous ≠ key row) :
    UniqueRows key (setRow rows slot (some row)) := by
  intro left right first second foundFirst foundSecond sameKey
  by_cases leftNew : left = slot
  · by_cases rightNew : right = slot
    · exact leftNew.trans rightNew.symm
    · have firstNew : first = row := by simpa [setRow, leftNew] using foundFirst.symm
      have previously : rows right = some second := by simpa [setRow, rightNew] using foundSecond
      exact False.elim (fresh right second previously (sameKey.symm.trans (congrArg key firstNew)))
  · have previously : rows left = some first := by simpa [setRow, leftNew] using foundFirst
    by_cases rightNew : right = slot
    · have secondNew : second = row := by simpa [setRow, rightNew] using foundSecond.symm
      exact False.elim (fresh left first previously (sameKey.trans (congrArg key secondNew)))
    · exact unique left right first second previously (by simpa [setRow, rightNew] using foundSecond) sameKey

structure SoundFor (width : Nat) (env : Environment) (historical : Barrier → Prop)
    (state : State capacity) : Prop where
  snapshot : SnapshotAdmission.Sound env state.view
  rows : ∀ slot row, state.rows slot = some row →
    Fits width row.reply ∧ row.serial < EnvelopeCodec.wordLimit width ∧
      historical row.reply ∧
      ∃ basis, state.view.snapshots row.serial = some basis ∧ basis.stop = row.reply.cut
  unique : UniqueRows Row.serial state.rows
  invocations : UniqueRows (fun row => row.reply.invocation) state.rows

abbrev Sound (env : Environment) (rules : Rules width slots Payload Ticket)
    (ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket))
    (origin : Image slots Payload) (state : State capacity) : Prop :=
  SoundFor width env (Issuable rules ledger origin) state

theorem empty_result_slots_are_sound
    {env : Environment} {historical : Barrier → Prop}
    (view : View) (backed : SnapshotAdmission.Sound env view) :
    SoundFor width env historical (⟨view, fun _ => none⟩ : State capacity) := by
  refine ⟨backed, ?_, ?_, ?_⟩ <;> simp [UniqueRows]

theorem preserve_on_capture {env : Environment} {historical : Barrier → Prop}
    {state : State capacity} {slot : Fin capacity} {reply : Barrier}
    (sound : SoundFor width env historical state) (permitted : Reservable width env state slot reply)
    (actual : historical reply) :
    let (after, permit) := captured state slot reply
    SoundFor width env historical after ∧ after.rows permit.slot = some ⟨permit.serial, reply⟩ ∧
      after.view.snapshots permit.serial = some (SnapshotAdmission.currentBasis state.view) ∧
      Protected after.view (SnapshotAdmission.currentBasis state.view) := by
  let serial := state.view.issued + 1
  obtain ⟨currentCut, _, room, serialFits, fitsReply, noPrior⟩ := permitted
  have reserved : SnapshotAdmission.Step env state.view (SnapshotAdmission.snapshotView state.view) := .reserve room
  have valid := SnapshotAdmission.step_preserves_admitted_basis sound.snapshot reserved
  have newBasis : (SnapshotAdmission.snapshotView state.view).snapshots serial =
      some (SnapshotAdmission.currentBasis state.view) := by
    simp [SnapshotAdmission.snapshotView, setSlot, serial]
  have oldSerial {oldSlot old} (live : state.rows oldSlot = some old) : old.serial < serial := by
    obtain ⟨_, _, _, basis, recorded, _⟩ := sound.rows oldSlot old live
    exact Nat.lt_succ_of_le (sound.snapshot.issued old.serial basis recorded)
  have pair : SoundFor width env historical (captured state slot reply).1 := by
    refine ⟨valid, ?_, ?_, ?_⟩
    · intro scanned row held
      by_cases same : scanned = slot
      · have exactRow : row = ⟨serial, reply⟩ := by
          exact (Option.some.inj (by simpa [captured, setRow, same, serial] using held)).symm
        subst row
        exact ⟨fitsReply, serialFits, actual, _, newBasis, currentCut⟩
      · have still : state.rows scanned = some row := by
          simpa [captured, setRow, same] using held
        obtain ⟨fits, representable, historical, basis, recorded, cut⟩ := sound.rows scanned row still
        have earlier : row.serial ≠ serial := Nat.ne_of_lt (oldSerial still)
        exact ⟨fits, representable, historical, basis,
          by simpa [captured, SnapshotAdmission.snapshotView, setSlot, serial, earlier] using recorded, cut⟩
    · exact insert_preserves_unique_keys Row.serial state.rows slot ⟨serial, reply⟩ sound.unique
        (fun _ _ held => Nat.ne_of_lt (oldSerial held))
    · exact insert_preserves_unique_keys (fun row => row.reply.invocation) state.rows slot ⟨serial, reply⟩
        sound.invocations noPrior
  refine ⟨pair, ?_, newBasis, valid.live serial _ newBasis⟩
  simp [setRow]

theorem a_chosen_admission_commits_a_protected_exact_result
    {env : Environment} {rules : Rules width slots Payload Ticket}
    {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)} {origin : Image slots Payload}
    {call : Invocation} {state after : State capacity} {current : Image slots Payload}
    {marker : ChosenMarker rules ledger origin call} {slot : Fin capacity} {permit : Permit capacity}
    (sound : Sound env rules ledger origin state)
    (accepted : admit env state current marker slot = some (after, permit)) :
    Sound env rules ledger origin after ∧
      after.rows permit.slot = some ⟨permit.serial, barrierAt call marker.before⟩ ∧
      after.view.snapshots permit.serial = some (SnapshotAdmission.currentBasis state.view) ∧
      Protected after.view (SnapshotAdmission.currentBasis state.view) := by
  unfold admit at accepted
  dsimp only at accepted
  split at accepted
  next permitted =>
    cases accepted
    exact preserve_on_capture sound permitted.2.2 ⟨marker, rfl, permitted.2.1⟩
  next => contradiction

theorem a_retired_or_stale_marker_cannot_capture_a_fresh_reservation
    (env : Environment) {rules : Rules width slots Payload Ticket}
    {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)} {origin : Image slots Payload}
    {call : Invocation} (state : State capacity) (current : Image slots Payload)
    (marker : ChosenMarker rules ledger origin call) (slot : Fin capacity)
    (blocked : marker.before ≠ current ∨ marker.result = .stream .refused) :
    admit env state current marker slot = none := by
  rcases blocked with stale | refused
  · simp [admit, stale]
  · simp [admit, refused]

theorem ordinary_snapshot_changes_preserve_live_results_and_protection
    {env : Environment} {historical : Barrier → Prop}
    {state : State capacity} {next : View} (sound : SoundFor width env historical state)
    (step : SnapshotAdmission.Step env state.view next) (same : next.snapshots = state.view.snapshots) :
    SoundFor width env historical {state with view := next} := by
  refine ⟨SnapshotAdmission.step_preserves_admitted_basis sound.snapshot step, ?_, sound.unique, sound.invocations⟩
  intro slot row live
  obtain ⟨fits, representable, original, basis, held, stop⟩ := sound.rows slot row live
  exact ⟨fits, representable, original, basis, same ▸ held, stop⟩

theorem terminal_release_clears_the_exact_hold_and_preserves_other_reads
    {env : Environment} {historical : Barrier → Prop}
    {state after : State capacity} {permit : Permit capacity}
    (sound : SoundFor width env historical state) (closed : close env state permit = some after) :
    SoundFor width env historical after ∧ after.rows permit.slot = none ∧ after.view.snapshots permit.serial = none := by
  cases seen : state.rows permit.slot with
  | none => simp [close, seen] at closed
  | some row =>
      simp only [close, seen] at closed
      split at closed
      next stopped =>
        cases closed
        have release : SnapshotAdmission.Step env state.view (cleared state permit).view :=
          .release permit.serial stopped.2
        have kept {slot other} (remains : (cleared state permit).rows slot = some other) :
            state.rows slot = some other := by
          by_cases same : slot = permit.slot
          · simp [cleared, setRow, same] at remains
          · simpa [cleared, setRow, same] using remains
        refine ⟨⟨SnapshotAdmission.step_preserves_admitted_basis sound.snapshot release, ?_, ?_, ?_⟩, ?_, ?_⟩
        · intro slot other remains
          have distinct : slot ≠ permit.slot := by
            intro same
            simp [cleared, setRow, same] at remains
          have previously : state.rows slot = some other := by
            simpa [cleared, setRow, distinct] using remains
          have notAlias : other.serial ≠ permit.serial := by
            intro aliases
            exact distinct (sound.unique slot permit.slot other row previously seen (aliases.trans stopped.1.symm))
          obtain ⟨fits, representable, applied, basis, held, exactCut⟩ := sound.rows slot other previously
          exact ⟨fits, representable, applied, basis, by simpa [cleared, setSlot, notAlias] using held, exactCut⟩
        · intro l r first second left right serial
          exact sound.unique l r first second (kept left) (kept right) serial
        · intro l r first second left right invocation
          exact sound.invocations l r first second (kept left) (kept right) invocation
        · simp [cleared, setRow]
        · simp [cleared, setSlot]
      next => contradiction

theorem reissue_from_retained_rows_refines_the_original_guarded_issuer
    {env : Environment} {rules : Rules width slots Payload Ticket}
    {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)} {origin : Image slots Payload}
    (state : State capacity) (permit : Permit capacity) (call : Invocation)
    (sign : Route → EnvelopeCodec.Bytes → Signature) {packet : Packet Signature}
    (sound : Sound env rules ledger origin state) (positive : 0 < width)
    (issued : reissue width state permit call sign = some packet) :
    ∃ row basis, state.rows permit.slot = some row ∧ row.serial = permit.serial ∧ row.reply.invocation = call ∧
      state.view.snapshots permit.serial = some basis ∧ basis.stop = row.reply.cut ∧ Protected state.view basis ∧
      AppliedBarrierReceipt.issue width rules ledger origin sign row.reply = some packet := by
  cases found : state.rows permit.slot with
  | none => simp [reissue, found] at issued
  | some row =>
      cases held : state.view.snapshots permit.serial with
      | none => simp [reissue, found, held] at issued
      | some basis =>
          by_cases checked : row.serial = permit.serial ∧ row.reply.invocation = call ∧ basis.stop = row.reply.cut
          · have exactPacket : (⟨AppliedBarrierReceipt.encode width row.reply,
                sign (AppliedBarrierReceipt.sourceOf row.reply.invocation)
                  (AppliedBarrierReceipt.encode width row.reply)⟩ : Packet Signature) = packet := by
              simpa [reissue, found, held, checked] using issued
            subst packet
            obtain ⟨fits, _, original, _, _, _⟩ := sound.rows permit.slot row found
            refine ⟨row, basis, rfl, checked.1, checked.2.1, rfl, checked.2.2,
              sound.snapshot.live permit.serial basis held, ?_⟩
            have permitted : 0 < width ∧ Fits width row.reply ∧ Issuable rules ledger origin row.reply :=
              ⟨positive, fits, original⟩
            simp only [AppliedBarrierReceipt.issue, ite_eq_left permitted]
          · simp [reissue, found, held, checked] at issued

theorem a_live_row_can_reissue_without_loading_the_marker_frame
    (width : Nat) (state : State capacity) (permit : Permit capacity) (row : Row) (basis : Basis)
    (sign : Route → EnvelopeCodec.Bytes → Signature)
    (found : state.rows permit.slot = some row) (identity : row.serial = permit.serial)
    (held : state.view.snapshots permit.serial = some basis) (exactCut : basis.stop = row.reply.cut) :
    let body := AppliedBarrierReceipt.encode width row.reply
    reissue width state permit row.reply.invocation sign =
      some ⟨body, sign (AppliedBarrierReceipt.sourceOf row.reply.invocation) body⟩ := by
  simp [reissue, found, held, identity, exactCut]

theorem a_recycled_slot_refuses_both_old_reissue_and_old_close
    (env : Environment) (width : Nat) (state : State capacity) (permit : Permit capacity) (new : Row)
    (call : Invocation) (sign : Route → EnvelopeCodec.Bytes → Signature)
    (found : state.rows permit.slot = some new) (different : new.serial ≠ permit.serial) :
    reissue width state permit call sign = none ∧ close env state permit = none := by
  constructor
  · cases held : state.view.snapshots permit.serial <;> simp [reissue, found, held, different]
  · simp [close, found, different]

theorem a_second_admission_cannot_charge_the_same_live_invocation
    (env : Environment) {rules : Rules width slots Payload Ticket}
    {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)} {origin : Image slots Payload}
    {call : Invocation} (state : State capacity) (current : Image slots Payload)
    (marker : ChosenMarker rules ledger origin call) (target occupied : Fin capacity) (prior : Row)
    (live : state.rows occupied = some prior) (same : prior.reply.invocation = call) :
    admit env state current marker target = none := by
  have repeated : ¬ (∀ slot previous, state.rows slot = some previous → previous.reply.invocation ≠ call) :=
    fun fresh => (fresh occupied prior live) same
  simp [admit, Reservable, barrierAt, repeated]

theorem the_exact_live_permit_is_found_by_its_invocation
    (state : State capacity) (slot : Fin capacity) (row : Row) (retained : state.rows slot = some row)
    (unique : UniqueRows (fun prior => prior.reply.invocation) state.rows) :
    (List.finRange capacity).findSome? (permitAt state row.reply.invocation) = some ⟨slot, row.serial⟩ := by
  cases found : (List.finRange capacity).findSome? (permitAt state row.reply.invocation) with
  | none =>
      have absent := List.findSome?_eq_none_iff.mp found slot (List.mem_finRange slot)
      simp [permitAt, retained] at absent
  | some permit =>
      obtain ⟨scanned, _, matchPermit⟩ := List.exists_of_findSome?_eq_some found
      cases scannedRow : state.rows scanned with
      | none => simp [permitAt, scannedRow] at matchPermit
      | some prior =>
          by_cases same : prior.reply.invocation = row.reply.invocation
          · have exactPermit : permit = ⟨scanned, prior.serial⟩ := by
              simpa [permitAt, scannedRow, same] using matchPermit.symm
            have sameSlot := unique scanned slot prior row scannedRow retained same
            subst scanned
            have sameRow := Option.some.inj (scannedRow.symm.trans retained)
            subst prior
            exact congrArg some exactPermit
          · simp [permitAt, scannedRow, same] at matchPermit

theorem the_original_invocation_can_recover_even_if_the_permit_reply_was_lost
    {env : Environment} {historical : Barrier → Prop}
    {state : State capacity} (sound : SoundFor width env historical state)
    (slot : Fin capacity) (row : Row) (authenticate : Invocation → Prop) (sign : Route → EnvelopeCodec.Bytes → Signature)
    (retained : state.rows slot = some row) (authorized : authenticate row.reply.invocation) :
    let body := AppliedBarrierReceipt.encode width row.reply
    recoverInvocation width state row.reply.invocation authenticate sign =
      some ⟨body, sign (AppliedBarrierReceipt.sourceOf row.reply.invocation) body⟩ := by
  have picked := the_exact_live_permit_is_found_by_its_invocation state slot row retained sound.invocations
  obtain ⟨_, _, _, basis, held, exactCut⟩ := sound.rows slot row retained
  have exactPacket := a_live_row_can_reissue_without_loading_the_marker_frame width state
    ⟨slot, row.serial⟩ row basis sign retained rfl held exactCut
  simpa [recoverInvocation, authorized, picked] using exactPacket

theorem knowing_the_invocation_identity_alone_does_not_authorize_recovery
    (width : Nat) (state : State capacity) (call : Invocation) (authenticate : Invocation → Prop)
    (sign : Route → EnvelopeCodec.Bytes → Signature) (refused : ¬ authenticate call) :
    recoverInvocation width state call authenticate sign = none := by
  simp [recoverInvocation, refused]

theorem an_absent_invocation_cannot_be_reminted
    (width : Nat) (state : State capacity) (call : Invocation) (authenticate : Invocation → Prop)
    (sign : Route → EnvelopeCodec.Bytes → Signature)
    (absent : ∀ slot row, state.rows slot = some row → row.reply.invocation ≠ call) :
    recoverInvocation width state call authenticate sign = none := by
  have missing : (List.finRange capacity).findSome? (permitAt state call) = none := by
    apply List.findSome?_eq_none_iff.mpr
    intro slot _
    cases found : state.rows slot with
    | none => simp [permitAt, found]
    | some row => simp [permitAt, found, absent slot row found]
  simp [recoverInvocation, missing]

theorem the_admission_program_recovers_before_the_first_receipt_is_emitted
    {env : Environment} {rules : Rules width slots Payload Ticket}
    {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)} {origin : Image slots Payload}
    {call : Invocation} {state committed recovered : State capacity} {current : Image slots Payload}
    {marker : ChosenMarker rules ledger origin call} {slot : Fin capacity} {permit : Permit capacity}
    (before : Sound env rules ledger origin state)
    (accepted : admit env state current marker slot = some (committed, permit))
    (exactControl : recovered = committed)
    (authenticate : Invocation → Prop) (sign : Route → EnvelopeCodec.Bytes → Signature)
    (authorized : authenticate call) :
    let body := AppliedBarrierReceipt.encode width (barrierAt call marker.before)
    recoverInvocation width recovered call authenticate sign =
      some ⟨body, sign (AppliedBarrierReceipt.sourceOf call) body⟩ := by
  obtain ⟨sound, live, _, _⟩ := a_chosen_admission_commits_a_protected_exact_result before accepted
  rw [exactControl]
  exact the_original_invocation_can_recover_even_if_the_permit_reply_was_lost sound permit.slot
    ⟨permit.serial, barrierAt call marker.before⟩ authenticate sign live authorized

def encodeRow (width : Nat) (row : Row) : EnvelopeCodec.Bytes :=
  EnvelopeCodec.wordBytes width row.serial ++ AppliedBarrierReceipt.encode width row.reply

def decodeRow (width : Nat) (wire : EnvelopeCodec.Bytes) : Option Row := do
  let (serial, tail) ← EnvelopeCodec.takeField width wire
  let reply ← AppliedBarrierReceipt.decode width tail
  pure ⟨EnvelopeCodec.readWord serial.val, reply⟩

theorem a_live_result_row_has_an_exact_fixed_width_checkpoint_body
    (row : Row) (positive : 0 < width) (serialFits : row.serial < EnvelopeCodec.wordLimit width)
    (replyFits : Fits width row.reply) :
    decodeRow width (encodeRow width row) = some row ∧
      (encodeRow width row).length = 1 + 10 * width := by
  have serial := EnvelopeCodec.takeField_on_encoded_word (EnvelopeCodec.word width row.serial)
    (AppliedBarrierReceipt.encode width row.reply)
  change EnvelopeCodec.takeField width
    (EnvelopeCodec.wordBytes width row.serial ++ AppliedBarrierReceipt.encode width row.reply) =
    some (EnvelopeCodec.word width row.serial, AppliedBarrierReceipt.encode width row.reply) at serial
  constructor
  · have parsed := AppliedBarrierReceipt.a_representable_reply_round_trips row.reply positive replyFits
    have readSerial : EnvelopeCodec.readWord (EnvelopeCodec.word width row.serial).val = row.serial :=
      EnvelopeCodec.fixed_width_words_roundtrip serialFits
    simp [decodeRow, encodeRow, serial, parsed, readSerial]
  · simp only [encodeRow, List.length_append, EnvelopeCodec.wordBytes_length,
      AppliedBarrierReceipt.an_encoded_reply_has_constant_length]
    omega

#print axioms empty_result_slots_are_sound
#print axioms a_chosen_admission_commits_a_protected_exact_result
#print axioms a_retired_or_stale_marker_cannot_capture_a_fresh_reservation
#print axioms ordinary_snapshot_changes_preserve_live_results_and_protection
#print axioms terminal_release_clears_the_exact_hold_and_preserves_other_reads
#print axioms reissue_from_retained_rows_refines_the_original_guarded_issuer
#print axioms a_live_row_can_reissue_without_loading_the_marker_frame
#print axioms a_recycled_slot_refuses_both_old_reissue_and_old_close
#print axioms a_second_admission_cannot_charge_the_same_live_invocation
#print axioms the_original_invocation_can_recover_even_if_the_permit_reply_was_lost
#print axioms knowing_the_invocation_identity_alone_does_not_authorize_recovery
#print axioms an_absent_invocation_cannot_be_reminted
#print axioms the_admission_program_recovers_before_the_first_receipt_is_emitted
#print axioms a_live_result_row_has_an_exact_fixed_width_checkpoint_body

end RecoverableRead
