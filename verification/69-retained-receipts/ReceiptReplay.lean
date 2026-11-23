import CoreReference

set_option warningAsError true

namespace ReceiptReplay

open CoreReference (stream)
open SnapshotAdmission (setSlot)
open ChosenReplay (Lineage Image Frame Applied Rules)

variable {slots : Nat} {Payload Ticket : Type}

structure Key (Payload : Type) where
  lineage : Lineage
  writer : Kernel.Writer
  lsn : Nat
  payload : Payload

structure Receipt (Payload : Type) where
  binding : Key Payload
  position : Nat
  endLsn : Nat

abbrev Rows (Payload : Type) := Nat → Option (Receipt Payload)

structure View (slots : Nat) (Payload : Type) where
  image : Image slots Payload
  rows : Rows Payload

inductive Lookup (Payload : Type) where
  | committed (receipt : Receipt Payload)
  | trimmed (firstRetained : Nat)
  | conflict
  | unresolved
  | refused

def record (rows : Rows Payload) (applied : Applied slots Payload Ticket) : Rows Payload :=
  match applied.frame.command, applied.reply with
  | .append request, .stream (.appended lsn _) =>
    let receipt : Receipt Payload :=
      ⟨⟨applied.frame.lineage, request.writer, request.lsn, request.payload⟩, applied.frame.position, lsn + 1⟩
    setSlot rows lsn (some receipt)
  | _, _ => rows

def retain (rows : Rows Payload) (floor : Nat) : Rows Payload :=
  fun lsn => if lsn < floor then none else rows lsn

def useApplied (rows : Rows Payload) (result : ChosenReplay.Outcomes slots Payload Ticket) :
    View slots Payload :=
  ⟨result.1, retain (result.2.foldl record rows) (stream result.1).firstRetained⟩

noncomputable def replay (rules : Rules slots Payload Ticket) (lineage : Lineage)
    (before : View slots Payload) (frames : List (Frame slots Payload Ticket)) :
    Option (View slots Payload × List (Applied slots Payload Ticket)) :=
  (ChosenReplay.replay rules lineage before.image frames).map fun result =>
    (useApplied before.rows result, result.2)

def Matches (receipt : Receipt Payload) (key : Key Payload) : Prop :=
  receipt.binding = key

noncomputable def lookup (lineage : Lineage) (authorized : Prop) (view : View slots Payload)
    (key : Key Payload) : Lookup Payload := by
  classical
  exact if authorized ∧ key.lineage = lineage then
    if key.lsn < (stream view.image).firstRetained then .trimmed (stream view.image).firstRetained
    else if (stream view.image).history.length ≤ key.lsn then .unresolved
    else match view.rows key.lsn with
      | none => .unresolved
      | some receipt => if Matches receipt key then .committed receipt else .conflict
  else .refused

theorem a_positive_lookup_binds_the_exact_original_request
    {lineage : Lineage} {authorized : Prop} {view : View slots Payload} {key : Key Payload}
    {receipt : Receipt Payload} (returned : lookup lineage authorized view key = .committed receipt) :
    authorized ∧ key.lineage = lineage ∧ (stream view.image).firstRetained ≤ key.lsn ∧
      key.lsn < (stream view.image).history.length ∧
      view.rows key.lsn = some receipt ∧ receipt.binding = key := by
  unfold lookup at returned
  split at returned
  · rename_i scope
    split at returned
    · cases returned
    · rename_i notTrimmed
      split at returned
      · cases returned
      · rename_i notFuture
        cases saved : view.rows key.lsn with
        | none => simp [saved] at returned
        | some observed =>
            simp only [saved] at returned
            split at returned
            · rename_i exactBinding
              cases returned
              refine ⟨scope.1, scope.2, Nat.le_of_not_gt notTrimmed, Nat.lt_of_not_ge notFuture, rfl, ?_⟩
              exact exactBinding
            · cases returned
  · cases returned

theorem a_same_lsn_lookup_with_changed_binding_cannot_confirm
    {lineage : Lineage} {authorized : Prop} {view : View slots Payload} {key : Key Payload}
    {original : Receipt Payload} (saved : view.rows key.lsn = some original) (changed : original.binding ≠ key) :
    ∀ receipt, lookup lineage authorized view key ≠ .committed receipt := by
  intro receipt returned
  have proves := a_positive_lookup_binds_the_exact_original_request returned
  have same := Option.some.inj (proves.2.2.2.2.1.symm.trans saved)
  exact changed (same ▸ proves.2.2.2.2.2)

theorem trim_ends_receipt_authority_even_with_a_stale_row
    {lineage : Lineage} {authorized : Prop} {view : View slots Payload} {key : Key Payload}
    (approved : authorized ∧ key.lineage = lineage) (below : key.lsn < (stream view.image).firstRetained) :
    lookup lineage authorized view key = .trimmed (stream view.image).firstRetained := by
  simp [lookup, approved, below]

theorem the_exact_retained_receipt_is_available_without_appending
    {lineage : Lineage} {authorized : Prop} {view : View slots Payload} {key : Key Payload}
    {receipt : Receipt Payload} (approved : authorized ∧ key.lineage = lineage)
    (held : (stream view.image).firstRetained ≤ key.lsn) (chosen : key.lsn < (stream view.image).history.length)
    (saved : view.rows key.lsn = some receipt)
    (same : receipt.binding = key) :
    lookup lineage authorized view key = .committed receipt := by
  have matched : Matches receipt key := by
    rw [← same]
    simp [Matches]
  simp [lookup, approved, Nat.not_lt_of_ge held, Nat.not_le_of_gt chosen, saved, matched]

private theorem record_respects_a_pointwise_lookup
    (applied : Applied slots Payload Ticket) {left right : Rows Payload} {lsn : Nat}
    (same : left lsn = right lsn) : record left applied lsn = record right applied lsn := by
  rcases applied with ⟨frame, reply⟩
  rcases frame with ⟨lineage, position, command⟩
  cases command <;> try exact same
  case append request =>
    cases reply <;> try exact same
    case stream response =>
      cases response <;> try exact same
      case appended index entry =>
        simp [record, setSlot, same]

private theorem folding_respects_a_pointwise_lookup
    (events : List (Applied slots Payload Ticket)) {left right : Rows Payload} {lsn : Nat}
    (same : left lsn = right lsn) :
    (events.foldl record left) lsn = (events.foldl record right) lsn := by
  induction events generalizing left right with
  | nil => exact same
  | cons event rest prior => exact prior (record_respects_a_pointwise_lookup event same)

theorem closing_an_earlier_book_preserves_the_final_retained_receipts
    (rows : Rows Payload) (earlier later : List (Applied slots Payload Ticket))
    (baseFloor finalFloor : Nat) (advances : baseFloor ≤ finalFloor) :
    retain (later.foldl record (retain (earlier.foldl record rows) baseFloor)) finalFloor =
      retain ((earlier ++ later).foldl record rows) finalFloor := by
  funext lsn
  by_cases trimmed : lsn < finalFloor
  · simp [retain, trimmed]
  · have pastBase : ¬ lsn < baseFloor := fun lower => trimmed (Nat.lt_of_lt_of_le lower advances)
    simp only [retain, ite_eq_right trimmed, List.foldl_append]
    exact folding_respects_a_pointwise_lookup later (by simp [retain, pastBase])

private theorem kernel_trim_floor_is_monotone {limits : Kernel.Limits} {first last : Kernel.State Payload}
    (trace : Kernel.Trace limits first last) : first.firstRetained ≤ last.firstRetained := by
  induction trace with
  | same => exact Nat.le_refl _
  | next _ event prior =>
      cases event with
      | trim _ _ advances _ _ => exact Nat.le_trans prior advances
      | _ => exact prior

theorem a_selected_receipt_checkpoint_reconstructs_the_whole_retained_book
    (rules : Rules slots Payload Ticket) (lineage : Lineage)
    (origin base final : View slots Payload)
    (earlier suffix : List (Frame slots Payload Ticket))
    {prefixResults tailResults : List (Applied slots Payload Ticket)}
    (selected : replay rules lineage origin earlier = some (base, prefixResults))
    (recovered : replay rules lineage base suffix = some (final, tailResults)) :
    replay rules lineage origin (earlier ++ suffix) = some (final, prefixResults ++ tailResults) := by
  cases opened : ChosenReplay.replay rules lineage origin.image earlier with
  | none => simp [replay, opened] at selected
  | some baseReplay =>
    cases continued : ChosenReplay.replay rules lineage base.image suffix with
    | none => simp [replay, continued] at recovered
    | some tail =>
      have prefixExact : (useApplied origin.rows baseReplay, baseReplay.2) = (base, prefixResults) := by
        simpa [replay, opened] using selected
      have tailExact : (useApplied base.rows tail, tail.2) = (final, tailResults) := by
        simpa [replay, continued] using recovered
      obtain ⟨baseExact, prefixExact⟩ := Prod.mk.inj prefixExact
      obtain ⟨finalExact, tailExact⟩ := Prod.mk.inj tailExact
      have samePrefix : baseReplay.1 = base.image := congrArg View.image baseExact
      have tailTrace := CoreReference.every_replayed_history_refines_one_logical_trace
        rules lineage base.image tail.1 suffix tail.2 (by cases tail; exact continued)
      have advances := kernel_trim_floor_is_monotone tailTrace
      have inherited : ChosenReplay.replay rules lineage origin.image (earlier ++ suffix) =
          some (tail.1, baseReplay.2 ++ tail.2) := by
        have original : ChosenReplay.replay rules lineage origin.image earlier = some (base.image, baseReplay.2) := by
          rw [opened, ← samePrefix]
        rw [ChosenReplay.replay_after_a_certified_prefix _ _ _ _ _ _ original, continued]
        rfl
      rw [replay, inherited]
      simp only [Option.map_some, Option.some.injEq]
      refine Prod.ext ?_ (by rw [prefixExact, tailExact])
      rw [← baseExact] at advances
      have retained := closing_an_earlier_book_preserves_the_final_retained_receipts origin.rows baseReplay.2 tail.2
        (stream baseReplay.1).firstRetained (stream tail.1).firstRetained advances
      rw [← finalExact, ← baseExact]
      exact congrArg (View.mk tail.1) retained.symm

theorem trim_clears_old_metadata_from_a_recovered_view
    (rows : Rows Payload) (result : ChosenReplay.Outcomes slots Payload Ticket) (lsn : Nat)
    (trimmed : lsn < (stream result.1).firstRetained) : (useApplied rows result).rows lsn = none := by
  simp [useApplied, retain, trimmed]

structure Base (rules : Rules slots Payload Ticket) (lineage : Lineage)
    (origin : View slots Payload) (chosen : List (Frame slots Payload Ticket)) where
  cut : Nat
  view : View slots Payload
  within : cut ≤ chosen.length
  certified : ∃ outcomes, replay rules lineage origin (chosen.take cut) = some (view, outcomes)

noncomputable def reopen {Voter : Type} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    (rules : Rules slots Payload Ticket) (lineage : Lineage) (origin : View slots Payload)
    (chosen : ChosenReplay.CertifiedCut ledger) (base : Base rules lineage origin chosen.frames)
    (physical : List (Frame slots Payload Ticket)) :
    Option (View slots Payload × List (Applied slots Payload Ticket)) :=
  (ChosenReplay.selectSuffix (chosen.frames.drop base.cut) physical).bind (replay rules lineage base.view)

theorem either_selectable_base_retains_the_same_lookup
    {Voter : Type} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    (rules : Rules slots Payload Ticket) (lineage : Lineage) (origin : View slots Payload)
    (chosen : ChosenReplay.CertifiedCut ledger) (old new : Base rules lineage origin chosen.frames)
    (oldPhysical newPhysical : List (Frame slots Payload Ticket))
    {left right : View slots Payload} {leftTail rightTail : List (Applied slots Payload Ticket)}
    (oldRecovered : reopen rules lineage origin chosen old oldPhysical = some (left, leftTail))
    (newRecovered : reopen rules lineage origin chosen new newPhysical = some (right, rightTail)) :
    left = right ∧ ∀ authorized key, lookup lineage authorized left key = lookup lineage authorized right key := by
  have recovers {base : Base rules lineage origin chosen.frames} {physical final tail}
      (opened : reopen rules lineage origin chosen base physical = some (final, tail)) :
      ∃ before, replay rules lineage origin chosen.frames = some (final, before ++ tail) := by
    unfold reopen at opened
    cases read : ChosenReplay.selectSuffix (chosen.frames.drop base.cut) physical with
    | none => simp [read] at opened
    | some readTail =>
      have only := (ChosenReplay.checked_suffix_is_exact read).1
      subst readTail
      rw [read] at opened
      change replay rules lineage base.view (chosen.frames.drop base.cut) = some (final, tail) at opened
      obtain ⟨before, sealed⟩ := base.certified
      refine ⟨before, ?_⟩
      have whole := a_selected_receipt_checkpoint_reconstructs_the_whole_retained_book rules lineage origin
        base.view final (chosen.frames.take base.cut) (chosen.frames.drop base.cut) sealed opened
      rwa [List.take_append_drop] at whole
  obtain ⟨_, leftWhole⟩ := recovers oldRecovered
  obtain ⟨_, rightWhole⟩ := recovers newRecovered
  have same : left = right := congrArg Prod.fst (Option.some.inj (leftWhole.symm.trans rightWhole))
  exact ⟨same, fun _ _ => by rw [same]⟩

#print axioms a_positive_lookup_binds_the_exact_original_request
#print axioms a_same_lsn_lookup_with_changed_binding_cannot_confirm
#print axioms trim_ends_receipt_authority_even_with_a_stale_row
#print axioms the_exact_retained_receipt_is_available_without_appending
#print axioms closing_an_earlier_book_preserves_the_final_retained_receipts
#print axioms a_selected_receipt_checkpoint_reconstructs_the_whole_retained_book
#print axioms trim_clears_old_metadata_from_a_recovered_view
#print axioms either_selectable_base_retains_the_same_lookup

end ReceiptReplay
