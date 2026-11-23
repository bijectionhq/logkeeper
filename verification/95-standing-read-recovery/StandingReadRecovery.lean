import StandingReadCredit
import SealedDeliveryHandoff

set_option warningAsError true

namespace StandingReadRecovery

open EnvelopeCodec (Bytes Field readWord word wordLimit flattenFields readFields)
open ChosenReplay (Lineage)
open StandingReadCredit (Rules State StandingGrant Fence)
open SourceOutcomes (Key)

variable {width slots capacity limit : Nat} {Payload Ticket : Type}

structure Saved (width : Nat) where
  through : Field width
  current : Option (Field width × Field width)

def encode (saved : Saved width) : Bytes :=
  match saved.current with
  | none => 0 :: flattenFields [saved.through]
  | some (name, used) => 1 :: flattenFields [saved.through, name, used]

def decode (width : Nat) (wire : Bytes) : Option (Saved width) :=
  match wire with
  | 0 :: body => match readFields width 1 body with
    | some [through] => some ⟨through, none⟩
    | _ => none
  | 1 :: body => match readFields width 3 body with
    | some [through, name, used] => some ⟨through, some (name, used)⟩
    | _ => none
  | _ => none

theorem a_saved_window_has_an_exact_bounded_encoding (saved : Saved width) :
    decode width (encode saved) = some saved ∧ (encode saved).length ≤ 1 + 3 * width := by
  have abs (through : Field width) : readFields width 1 (flattenFields [through]) = some [through] :=
    EnvelopeCodec.readFields_after_flatten [through]
  have pres (through name used : Field width) :
      readFields width 3 (flattenFields [through, name, used]) = some [through, name, used] :=
    EnvelopeCodec.readFields_after_flatten [through, name, used]
  cases saved with
  | mk through current =>
      cases current with
      | none =>
          constructor
          · simp [encode, decode, abs]
          · simp only [encode, List.length_cons, EnvelopeCodec.flattenFields_size, List.length_nil, Nat.zero_add, Nat.one_mul]
            omega
      | some pair =>
          obtain ⟨name, used⟩ := pair
          constructor
          · simp [encode, decode, pres]
          · simp [encode, EnvelopeCodec.flattenFields_size, Nat.add_comm, Nat.mul_comm]

def placementOf : Kernel.Authority → Option Kernel.Placement
  | .active writer | .vacant writer => some writer.placement
  | _ => none

structure Restored (Ticket : Type) where
  installedThrough : Nat
  current : Option (StandingGrant Ticket)

structure Matches (lineage : Lineage) (authority : Kernel.Authority) (generation used : Nat)
    (window : StandingReadCredit.Window) : Prop where
  lineageBound : window.lineage = lineage
  samePlacement : placementOf authority = some window.placement
  sameGeneration : window.generation = generation
  withinRange : used ≤ window.serials.size

theorem resume_checks_the_exact_placement
    (lineage : Lineage) (authority : Kernel.Authority) (generation used : Nat)
    (window : StandingReadCredit.Window) (valid : Matches lineage authority generation used window) :
    placementOf authority = some window.placement := by
  exact valid.samePlacement

noncomputable def openSaved (rules : Rules width slots capacity limit Payload Ticket)
    (archive : Field width → Option Ticket) (lineage : Lineage) (authority : Kernel.Authority)
    (saved : Saved width) : Option (Restored Ticket) := by
  classical
  let through := readWord saved.through.val
  exact match saved.current with
  | none => some ⟨through, none⟩
  | some (name, cursor) =>
      match archive name with
      | none => none
      | some proof =>
          match rules.certified proof with
          | none => none
          | some window =>
              let used := readWord cursor.val
              if Matches lineage authority through used window then some ⟨through, some ⟨window, proof, used⟩⟩
              else none

def capture (width through : Nat) (named : Option (Field width × Nat)) : Saved width :=
  ⟨word width through, named.map fun (name, used) => (name, word width used)⟩

theorem recovery_restores_even_an_exhausted_current_range_without_resetting_it
    (rules : Rules width slots capacity limit Payload Ticket) (archive : Field width → Option Ticket)
    (lineage : Lineage) (authority : Kernel.Authority) (through : Nat) (name : Field width)
    (grant : StandingGrant Ticket) (known : archive name = some grant.proof)
    (authentic : rules.certified grant.proof = some grant.window)
    (bound : Matches lineage authority through grant.used grant.window)
    (throughFits : through < wordLimit width) (cursorFits : grant.used < wordLimit width) :
    openSaved rules archive lineage authority (capture width through (some (name, grant.used))) =
      some ⟨through, some grant⟩ := by
  classical
  have generation : readWord (word width through).val = through := EnvelopeCodec.fixed_width_words_roundtrip throughFits
  have used : readWord (word width grant.used).val = grant.used := EnvelopeCodec.fixed_width_words_roundtrip cursorFits
  simp only [openSaved, capture, Option.map_some, known, authentic]
  change (if Matches lineage authority (readWord (word width through).val)
      (readWord (word width grant.used).val) grant.window then some
        (⟨readWord (word width through).val, some ⟨grant.window, grant.proof, readWord (word width grant.used).val⟩⟩ :
          Restored Ticket)
    else none) = _
  rw [generation, used, ite_eq_left bound]

theorem absent_window_still_recovers_the_full_installed_watermark
    (rules : Rules width slots capacity limit Payload Ticket) (archive : Field width → Option Ticket)
    (lineage : Lineage) (authority : Kernel.Authority) (through : Nat) (fits : through < wordLimit width) :
    openSaved rules archive lineage authority (capture width through none) = some ⟨through, none⟩ :=
  congrArg (fun value => some (⟨value, none⟩ : Restored Ticket)) (EnvelopeCodec.fixed_width_words_roundtrip fits)

theorem a_window_certificate_of_another_placement_cannot_restore_a_current_grant
    (rules : Rules width slots capacity limit Payload Ticket) (archive : Field width → Option Ticket)
    (lineage : Lineage) (authority : Kernel.Authority) (through cursor name : Field width)
    (window : StandingReadCredit.Window) (proof : Ticket)
    (known : archive name = some proof) (attested : rules.certified proof = some window)
    (foreign : placementOf authority ≠ some window.placement) :
    openSaved rules archive lineage authority ⟨through, some (name, cursor)⟩ = none := by
  have blocked : ¬ Matches lineage authority (readWord through.val) (readWord cursor.val) window :=
    fun valid => foreign (resume_checks_the_exact_placement lineage authority _ _ window valid)
  simp [openSaved, known, attested, blocked]

structure Control (width slots capacity limit : Nat) (Payload : Type) where
  retained : DeliveryRecovery.Control width slots capacity limit Payload
  credit : Bytes

abbrev Catalog (width slots capacity limit : Nat) (Payload : Type) :=
  EnvelopeRecovery.Catalog width (Control width slots capacity limit Payload) (FundedAppend.Source slots Payload)

abbrev Contents (width slots capacity limit : Nat) (Payload : Type) :=
  EnvelopeRecovery.Contents width (Control width slots capacity limit Payload) (FundedAppend.Source slots Payload)

def project (catalog : Catalog width slots capacity limit Payload) :
    DeliveryRecovery.Catalog width slots capacity limit Payload :=
  ⟨fun name => (catalog.control name).map Control.retained, catalog.data, catalog.manifests, catalog.retained⟩

structure Store (width slots capacity limit : Nat) (Payload Ticket : Type) where
  catalog : Catalog width slots capacity limit Payload
  archive : Field width → Option Ticket
  authenticate : Bytes → Prop
  coreNeeds : Field width → Prop
  readNeeds : SnapshotAdmission.Basis → Field width → Prop
  deliveryNeeds : DeliveryBook.Entry capacity → Field width → Prop

def merge (retained : RetainedDelivery.Image slots capacity limit Payload) (recovered : Restored Ticket) :
    State slots capacity limit Payload Ticket :=
  ⟨retained, recovered.current, recovered.installedThrough⟩

noncomputable def openCheckpoint (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (store : Store width slots capacity limit Payload Ticket) (anchor : EnvelopeRecovery.Anchor width)
    (wire : Bytes) : Option (State slots capacity limit Payload Ticket) :=
  match EnvelopeRecovery.openChecked store.catalog store.authenticate anchor store.coreNeeds wire with
  | none => none
  | some (_, contents) =>
      match DeliveryRecovery.openCheckpoint rules.retained (project store.catalog) store.authenticate anchor
          store.coreNeeds store.readNeeds store.deliveryNeeds wire with
      | none => none
      | some retained =>
          match decode width contents.control.credit with
          | none => none
          | some saved =>
              (openSaved rules store.archive lineage (OrderedReadReplay.authority retained.ordered) saved).map
                (merge retained)

theorem a_named_checkpoint_reopens_the_books_and_standing_cursor_from_one_cut
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (store : Store width slots capacity limit Payload Ticket) (anchor : EnvelopeRecovery.Anchor width) (wire : Bytes)
    (header : EnvelopeCodec.Envelope width) (contents : Contents width slots capacity limit Payload)
    (retained : RetainedDelivery.Image slots capacity limit Payload) (saved : Saved width) (binding : Restored Ticket)
    (named : EnvelopeRecovery.openChecked store.catalog store.authenticate anchor store.coreNeeds wire =
      some (header, contents))
    (books : DeliveryRecovery.openCheckpoint rules.retained (project store.catalog) store.authenticate anchor
      store.coreNeeds store.readNeeds store.deliveryNeeds wire = some retained)
    (credit : decode width contents.control.credit = some saved)
    (grant : openSaved rules store.archive lineage (OrderedReadReplay.authority retained.ordered) saved = some binding) :
    openCheckpoint rules lineage store anchor wire = some (merge retained binding) := by
  simp [openCheckpoint, named, books, credit, grant]

noncomputable def freshOpen (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (physical : StandingReadCredit.Window → SnapshotAdmission.Basis → Prop)
    (state : State slots capacity limit Payload Ticket) (call : RTDBFailover.Invocation)
    (readSlot : Fin capacity) (deliverySlot : Fin limit) :
    Option (State slots capacity limit Payload Ticket × AtomicReadCapture.Reply Payload capacity) := by
  classical
  exact match state.current with
  | none => none
  | some grant =>
      if physical grant.window (AtomicReadCapture.basisAt state.retained) then
        some (StandingReadCredit.tryOpen rules lineage state call readSlot deliverySlot)
      else none

theorem historical_proof_alone_cannot_admit_fresh_work
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (physical : StandingReadCredit.Window → SnapshotAdmission.Basis → Prop)
    (state : State slots capacity limit Payload Ticket) (call : RTDBFailover.Invocation)
    (readSlot : Fin capacity) (deliverySlot : Fin limit) (grant : StandingGrant Ticket)
    (selected : state.current = some grant)
    (absent : ¬ physical grant.window (AtomicReadCapture.basisAt state.retained)) :
    freshOpen rules lineage physical state call readSlot deliverySlot = none := by
  simp [freshOpen, selected, absent]

theorem every_chosen_cursor_fits_even_at_exhaustion
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before after : State slots capacity limit Payload Ticket) (call : RTDBFailover.Invocation)
    (readSlot : Fin capacity) (deliverySlot : Fin limit) (permit : RecoverableRead.Permit capacity)
    (reply : RTDBFailover.Barrier) (valid : before.retained.deliveries.Valid width)
    (opened : StandingReadCredit.tryOpen rules lineage before call readSlot deliverySlot = (after, .opened permit reply)) :
    ∃ grant, after.current = some grant ∧ grant.used < wordLimit width := by
  obtain ⟨grant, _, _, ready, spent, _, _, _, _, _⟩ :=
    StandingReadCredit.a_successful_choice_advances_both_cursors_and_keeps_the_original_borrow
      rules lineage before after call readSlot deliverySlot permit reply valid opened
  exact ⟨_, spent, Nat.lt_of_le_of_lt (Nat.succ_le_of_lt ready.available) ready.cursorFits⟩

inductive Command (slots capacity limit : Nat) (Payload Ticket : Type) where
  | existing (command : RetainedDelivery.Command slots capacity limit Payload Ticket)
  | openRead (call : RTDBFailover.Invocation) (readSlot : Fin capacity) (deliverySlot : Fin limit)
  | install (writer : Kernel.Writer) (window : StandingReadCredit.Window) (proof : Ticket)

structure Frame (slots capacity limit : Nat) (Payload Ticket : Type) where
  lineage : Lineage
  ordinal : Nat
  command : Command slots capacity limit Payload Ticket

noncomputable def applyCommand (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (state : State slots capacity limit Payload Ticket)
    (command : Command slots capacity limit Payload Ticket) : State slots capacity limit Payload Ticket :=
  match command with
  | .existing command => {state with retained := (RetainedDelivery.decide rules.retained lineage state.retained command).1}
  | .openRead call readSlot deliverySlot => (StandingReadCredit.tryOpen rules lineage state call readSlot deliverySlot).1
  | .install writer window proof => match StandingReadCredit.installWindow rules lineage state writer window proof with
    | some (next, _) => next
    | none => (StandingReadCredit.refused state).1

theorem a_live_submission_replays_the_same_decision_without_live_provider_state
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (physical : StandingReadCredit.Window → SnapshotAdmission.Basis → Prop)
    (state after : State slots capacity limit Payload Ticket) (call : RTDBFailover.Invocation)
    (readSlot : Fin capacity) (deliverySlot : Fin limit) (reply : AtomicReadCapture.Reply Payload capacity)
    (admitted : freshOpen rules lineage physical state call readSlot deliverySlot = some (after, reply)) :
    applyCommand rules lineage state (.openRead call readSlot deliverySlot) = after := by
  cases selected : state.current with
  | none => simp [freshOpen, selected] at admitted
  | some grant =>
      by_cases can : physical grant.window (AtomicReadCapture.basisAt state.retained)
      · have same : StandingReadCredit.tryOpen rules lineage state call readSlot deliverySlot = (after, reply) := by
          simpa [freshOpen, selected, can] using admitted
        exact congrArg Prod.fst same
      · simp [freshOpen, selected, can] at admitted

noncomputable def replay (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (state : State slots capacity limit Payload Ticket)
    (history : List (Frame slots capacity limit Payload Ticket)) : Option (State slots capacity limit Payload Ticket) := by
  classical
  exact history.foldlM (fun before frame => if frame.lineage = lineage ∧
      frame.ordinal = RetainedDelivery.position before.retained + 1 then
    some (applyCommand rules lineage before frame.command) else none) state

theorem every_exact_selectable_base_replays_the_same_credit_and_delivery_cursors
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin first second : State slots capacity limit Payload Ticket)
    (history : List (Frame slots capacity limit Payload Ticket)) (older newer : Nat)
    (a : replay rules lineage origin (history.take older) = some first)
    (b : replay rules lineage origin (history.take newer) = some second) :
    replay rules lineage first (history.drop older) = replay rules lineage second (history.drop newer) := by
  have same (restored : State slots capacity limit Payload Ticket) (cut : Nat)
      (base : replay rules lineage origin (history.take cut) = some restored) :
      replay rules lineage restored (history.drop cut) = replay rules lineage origin history := by
    calc
      replay rules lineage restored (history.drop cut) =
        replay rules lineage origin (history.take cut ++ history.drop cut) := by
          simp only [replay] at base ⊢
          rw [List.foldlM_append, base]
          rfl
      _ = replay rules lineage origin history := by rw [List.take_append_drop]
  exact (same first older a).trans (same second newer b).symm


theorem the_saved_watermark_survives_every_successful_decode
    (rules : Rules width slots capacity limit Payload Ticket) (archive : Field width → Option Ticket)
    (lineage : Lineage) (authority : Kernel.Authority) (saved : Saved width) (result : Restored Ticket)
    (restored : openSaved rules archive lineage authority saved = some result) :
    result.installedThrough = readWord saved.through.val := by
  cases sectionValue : saved.current with
  | none => simp [openSaved, sectionValue] at restored
            exact (congrArg Restored.installedThrough restored).symm
  | some pair =>
      obtain ⟨name, used⟩ := pair
      cases archived : archive name with
      | none => simp [openSaved, sectionValue, archived] at restored
      | some proof =>
          cases certificate : rules.certified proof with
          | none => simp [openSaved, sectionValue, archived, certificate] at restored
          | some bound =>
              simp only [openSaved, sectionValue, archived, certificate] at restored
              split at restored
              · exact (congrArg Restored.installedThrough (Option.some.inj restored)).symm
              · contradiction

structure SealControl (width capacity limit : Nat) where
  retained : SealedDeliveryHandoff.Control width capacity limit
  standing : Bytes

abbrev SealCatalog (width capacity limit : Nat) :=
  EnvelopeRecovery.Catalog width (SealControl width capacity limit) Unit

structure SealStore (width capacity limit : Nat) where
  catalog : SealCatalog width capacity limit
  authenticate : Bytes → Prop
  readNeeds : SnapshotAdmission.Basis → Field width → Prop
  deliveryNeeds : DeliveryBook.Entry capacity → Field width → Prop

def SealStore.project (store : SealStore width capacity limit) : SealedDeliveryHandoff.Store width capacity limit :=
  let catalog := store.catalog
  ⟨⟨fun name => (catalog.control name).map SealControl.retained, catalog.data, catalog.manifests,
    catalog.retained⟩, store.authenticate, store.readNeeds, store.deliveryNeeds⟩

noncomputable def openSealSection (rules : JointSource.Rules width slots Payload Ticket) (lineage : Lineage)
    (sealed : JointSource.Image slots Payload) (key : Key slots)
    (store : SealStore width capacity limit) (anchor : EnvelopeRecovery.Anchor width) : Option (Saved width) :=
  match JointSource.openSeal rules lineage sealed key with
  | none => none
  | some (record, evidence, _) =>
      if SealedDeliveryHandoff.atPosition anchor record.anchor.position then
        (EnvelopeRecovery.openChecked store.catalog store.authenticate anchor (fun _ => False)
          evidence.readControl).bind fun (_, contents) => decode width contents.control.standing
      else none

def freezeStanding (source : State slots capacity limit Payload Ticket)
    (sealed : RetainedDelivery.Image slots capacity limit Payload) :
    State slots capacity limit Payload Ticket × Option (Fence capacity limit Ticket) :=
  (⟨sealed, none, source.installedThrough⟩,
    source.current.map fun grant => ⟨grant, RetainedDelivery.position sealed, sealed.deliveries⟩)

noncomputable def chooseSeal (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (source : State slots capacity limit Payload Ticket) (writer : Kernel.Writer)
    (key : Key slots) (vector : RealizedSource.Vector) (body : JointSource.SealEvidence) (evidence : Ticket)
    (store : SealStore width capacity limit) (archive : Field width → Option Ticket) (anchor : EnvelopeRecovery.Anchor width) :
    Option (State slots capacity limit Payload Ticket × Option (Fence capacity limit Ticket)) := by
  classical
  exact match SealedDeliveryHandoff.chooseSeal rules.retained lineage source.retained writer key vector body evidence
      store.project anchor with
  | none => none
  | some sealed =>
      match openSealSection rules.retained.ordered.journal lineage sealed.ordered.journal key store anchor with
      | none => none
      | some saved =>
          if openSaved rules archive lineage (OrderedReadReplay.authority source.retained.ordered) saved =
              some ⟨source.installedThrough, source.current⟩ then
            some (freezeStanding source sealed)
          else none

theorem a_chosen_seal_preserves_the_watermark_and_fences_the_original_window
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (source sealed : State slots capacity limit Payload Ticket) (writer : Kernel.Writer)
    (key : Key slots) (vector : RealizedSource.Vector) (body : JointSource.SealEvidence) (evidence : Ticket)
    (store : SealStore width capacity limit) (archive : Field width → Option Ticket) (anchor : EnvelopeRecovery.Anchor width)
    (fence : Option (Fence capacity limit Ticket))
    (accepted : chooseSeal rules lineage source writer key vector body evidence store archive anchor = some (sealed, fence)) :
    sealed.current = none ∧ sealed.installedThrough = source.installedThrough ∧
      fence = source.current.map (fun grant => ⟨grant, RetainedDelivery.position sealed.retained, sealed.retained.deliveries⟩) ∧
      SealedDeliveryHandoff.chooseSeal rules.retained lineage source.retained writer key vector body evidence
        store.project anchor = some sealed.retained ∧
      ∃ saved, openSealSection rules.retained.ordered.journal lineage sealed.retained.ordered.journal key store anchor =
          some saved ∧
        openSaved rules archive lineage (OrderedReadReplay.authority source.retained.ordered) saved =
          some ⟨source.installedThrough, source.current⟩ := by
  cases applied : SealedDeliveryHandoff.chooseSeal rules.retained lineage source.retained writer key vector body evidence
      store.project anchor with
  | none => simp [chooseSeal, applied] at accepted
  | some retained =>
      cases attachment : openSealSection rules.retained.ordered.journal lineage retained.ordered.journal key store anchor with
      | none => simp [chooseSeal, applied, attachment] at accepted
      | some saved =>
          simp only [chooseSeal, applied, attachment] at accepted
          split at accepted
          · next exactState =>
              obtain ⟨rfl, rfl⟩ := Option.some.inj accepted |> Prod.mk.inj
              exact ⟨rfl, rfl, rfl, rfl, saved, attachment, exactState⟩
          · contradiction

noncomputable def activate (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (sealed : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (store : SealStore width capacity limit) (anchor : EnvelopeRecovery.Anchor width) :
    Option (State slots capacity limit Payload Ticket) :=
  match openSealSection rules.retained.ordered.journal lineage sealed
      install.original.installation.anchor.decision.key store anchor with
  | none => none
  | some saved =>
      (SealedDeliveryHandoff.activate rules.retained lineage sealed install store.project anchor).map
        fun retained => ⟨retained, none, readWord saved.through.val⟩

theorem target_activation_restores_the_fence_watermark_without_reviving_old_credit
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (sealed : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (store : SealStore width capacity limit) (anchor : EnvelopeRecovery.Anchor width)
    (target : State slots capacity limit Payload Ticket) (saved : Saved width)
    (mounted : openSealSection rules.retained.ordered.journal lineage sealed
      install.original.installation.anchor.decision.key store anchor = some saved)
    (active : activate rules lineage sealed install store anchor = some target) :
    target.current = none ∧ target.installedThrough = readWord saved.through.val := by
  cases chosen : SealedDeliveryHandoff.activate rules.retained lineage sealed install store.project anchor with
  | none => simp [activate, mounted, chosen] at active
  | some retained =>
      have same : (⟨retained, none, readWord saved.through.val⟩ : State slots capacity limit Payload Ticket) = target := by
        simpa [activate, mounted, chosen] using active
      cases same
      exact ⟨rfl, rfl⟩

theorem the_successor_rejects_the_predecessor_window_even_after_source_loss
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (source sealed target : State slots capacity limit Payload Ticket) (writer successor : Kernel.Writer)
    (key : Key slots) (vector : RealizedSource.Vector) (body : JointSource.SealEvidence) (evidence : Ticket)
    (install : RealizedSource.Install slots Payload Ticket) (same : install.original.installation.anchor.decision.key = key)
    (store : SealStore width capacity limit) (archive : Field width → Option Ticket) (anchor : EnvelopeRecovery.Anchor width)
    (fence : Option (Fence capacity limit Ticket))
    (accepted : chooseSeal rules lineage source writer key vector body evidence store archive anchor = some (sealed, fence))
    (active : activate rules lineage sealed.retained.ordered.journal install store anchor = some target)
    (original : StandingReadCredit.Window) (paid : Ticket) (old : original.generation ≤ source.installedThrough) :
    StandingReadCredit.installWindow rules lineage target successor original paid = none := by
  obtain ⟨_, _, _, _, saved, named, archived⟩ :=
    a_chosen_seal_preserves_the_watermark_and_fences_the_original_window rules lineage source sealed writer key vector body
      evidence store archive anchor fence accepted
  have sourceFloor := the_saved_watermark_survives_every_successful_decode rules archive lineage
    (OrderedReadReplay.authority source.retained.ordered) saved ⟨source.installedThrough, source.current⟩ archived
  have targetFloor := (target_activation_restores_the_fence_watermark_without_reviving_old_credit rules lineage
    sealed.retained.ordered.journal install store anchor target saved (by rwa [same]) active).2
  exact StandingReadCredit.a_window_at_or_below_the_installed_watermark_is_never_reinstalled rules lineage target
    successor original paid ((sourceFloor.trans targetFloor.symm) ▸ old)

theorem a_funded_handoff_preserves_the_entire_old_delivery_book_without_active_credit
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (source sealed target : State slots capacity limit Payload Ticket) (writer : Kernel.Writer)
    (key : Key slots) (vector : RealizedSource.Vector) (body : JointSource.SealEvidence) (evidence : Ticket)
    (install : RealizedSource.Install slots Payload Ticket) (same : install.original.installation.anchor.decision.key = key)
    (store : SealStore width capacity limit) (archive : Field width → Option Ticket) (anchor : EnvelopeRecovery.Anchor width)
    (fence : Option (Fence capacity limit Ticket))
    (accepted : chooseSeal rules lineage source writer key vector body evidence store archive anchor = some (sealed, fence))
    (active : activate rules lineage sealed.retained.ordered.journal install store anchor = some target) :
    target.retained.deliveries = source.retained.deliveries ∧ target.current = none := by
  obtain ⟨_, _, _, sealedCore, saved, named, _⟩ :=
    a_chosen_seal_preserves_the_watermark_and_fences_the_original_window rules lineage source sealed writer key vector body
      evidence store archive anchor fence accepted
  have mounted : openSealSection rules.retained.ordered.journal lineage sealed.retained.ordered.journal
      install.original.installation.anchor.decision.key store anchor = some saved := by rwa [same]
  cases core : SealedDeliveryHandoff.activate rules.retained lineage sealed.retained.ordered.journal install
      store.project anchor with
  | none => simp [activate, mounted, core] at active
  | some retained =>
      have restored : (⟨retained, none, readWord saved.through.val⟩ : State slots capacity limit Payload Ticket) = target := by
        simpa [activate, mounted, core] using active
      cases restored
      exact ⟨SealedDeliveryHandoff.source_to_target_preserves_each_delivery_and_the_issuance_floor
        rules.retained lineage source.retained sealed.retained retained writer key vector body evidence
        install store.project anchor sealedCore same core, rfl⟩

#print axioms a_saved_window_has_an_exact_bounded_encoding
#print axioms resume_checks_the_exact_placement
#print axioms recovery_restores_even_an_exhausted_current_range_without_resetting_it
#print axioms absent_window_still_recovers_the_full_installed_watermark
#print axioms a_window_certificate_of_another_placement_cannot_restore_a_current_grant
#print axioms a_named_checkpoint_reopens_the_books_and_standing_cursor_from_one_cut
#print axioms historical_proof_alone_cannot_admit_fresh_work
#print axioms every_chosen_cursor_fits_even_at_exhaustion
#print axioms a_live_submission_replays_the_same_decision_without_live_provider_state
#print axioms every_exact_selectable_base_replays_the_same_credit_and_delivery_cursors

#print axioms the_saved_watermark_survives_every_successful_decode
#print axioms a_chosen_seal_preserves_the_watermark_and_fences_the_original_window
#print axioms target_activation_restores_the_fence_watermark_without_reviving_old_credit
#print axioms the_successor_rejects_the_predecessor_window_even_after_source_loss
#print axioms a_funded_handoff_preserves_the_entire_old_delivery_book_without_active_credit

end StandingReadRecovery
