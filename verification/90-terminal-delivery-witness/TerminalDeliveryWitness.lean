import SealedDeliveryHandoff

set_option warningAsError true

namespace TerminalDeliveryWitness

open ChosenReplay (Lineage)
open EnvelopeCodec (Field)
open DeliveryBook (Entry atKey)
open RetainedDelivery (Rules Image)
open SealedDeliveryHandoff (Catalog Contents Restored withJournal)
open SourceOutcomes (Key)

variable {width slots capacity limit : Nat} {Payload Ticket Signature : Type}

structure Store (width capacity limit : Nat) (Ticket : Type) where
  original : SealedDeliveryHandoff.Store width capacity limit
  baseNeeds : Field width → Prop
  durable : Ticket → Prop
  receipts : Fin limit → Option Ticket

def Terminal (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (store : Store width capacity limit Ticket) (slot : Fin limit) (row : Entry capacity) : Prop :=
  ∃ receipt, store.receipts slot = some receipt ∧ store.durable receipt ∧
    rules.settled lineage ⟨slot, row.serial⟩ row receipt

def TerminalOnly (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (store : Store width capacity limit Ticket) (image : Restored capacity limit) (object : Field width) : Prop :=
  DeliveryRecovery.Needs store.original.deliveryNeeds image.delivery object ∧
    ¬ store.baseNeeds object ∧
    ¬ JointReadRecovery.Needs store.original.readNeeds image.reads object ∧
    ∀ slot row, image.delivery.rows slot = some row → store.original.deliveryNeeds row object →
      Terminal rules lineage store slot row

theorem an_extent_required_for_base_replay_cannot_be_replaced_by_a_stop
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (store : Store width capacity limit Ticket) (image : Restored capacity limit) (object : Field width)
    (necessary : store.baseNeeds object) (replacement : TerminalOnly rules lineage store image object) : False := by
  exact replacement.2.1 necessary

def Covered (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (store : Store width capacity limit Ticket) (contents : Contents width capacity limit)
    (restored : Restored capacity limit) : Prop :=
  (∀ object, store.baseNeeds object → object ∈ contents.dependencies) ∧
    ∀ object ∈ contents.dependencies,
      store.original.catalog.retained object ∨ TerminalOnly rules lineage store restored object

theorem coverage_keeps_replay_and_protected_reads_in_custody
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (store : Store width capacity limit Ticket) (contents : Contents width capacity limit)
    (restored : Restored capacity limit) (covered : Covered rules lineage store contents restored)
    (object : Field width) :
    (store.baseNeeds object → store.original.catalog.retained object) ∧
    (object ∈ contents.dependencies → JointReadRecovery.Needs store.original.readNeeds restored.reads object →
      store.original.catalog.retained object) := by
  constructor
  · intro needed
    exact (covered.2 object (covered.1 object needed)).resolve_right
      (an_extent_required_for_base_replay_cannot_be_replaced_by_a_stop rules lineage store restored object needed)
  · intro member needed
    exact (covered.2 object member).resolve_right (fun terminal => terminal.2.2.1 needed)

theorem a_shared_extent_needs_terminal_evidence_for_every_delivery_before_substitution
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (store : Store width capacity limit Ticket) (contents : Contents width capacity limit)
    (restored : Restored capacity limit) (covered : Covered rules lineage store contents restored)
    (object : Field width) (listed : object ∈ contents.dependencies)
    (missing : ¬ store.original.catalog.retained object)
    (slot : Fin limit) (row : Entry capacity) (pending : restored.delivery.rows slot = some row)
    (needed : store.original.deliveryNeeds row object) :
    Terminal rules lineage store slot row := by
  exact ((covered.2 object listed).resolve_left missing).2.2.2 slot row pending needed

theorem an_unproven_or_volatile_stop_cannot_replace_a_missing_delivery_extent
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (store : Store width capacity limit Ticket) (contents : Contents width capacity limit)
    (restored : Restored capacity limit) (slot : Fin limit) (row : Entry capacity)
    (pending : restored.delivery.rows slot = some row)
    (object : Field width) (listed : object ∈ contents.dependencies)
    (needed : store.original.deliveryNeeds row object) (missing : ¬ store.original.catalog.retained object)
    (unproven : ∀ receipt, store.receipts slot = some receipt →
      ¬ (store.durable receipt ∧ rules.settled lineage ⟨slot, row.serial⟩ row receipt)) :
    ¬ Covered rules lineage store contents restored := by
  intro covered
  obtain ⟨receipt, found, proof⟩ := a_shared_extent_needs_terminal_evidence_for_every_delivery_before_substitution
    rules lineage store contents restored covered object listed missing slot row pending needed
  exact unproven receipt found proof

theorem exact_durable_stops_can_supply_the_delivery_only_portion_of_coverage
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (store : Store width capacity limit Ticket) (contents : Contents width capacity limit)
    (restored : Restored capacity limit)
    (baseListed : ∀ object, store.baseNeeds object → object ∈ contents.dependencies)
    (missing : ∀ object ∈ contents.dependencies, ¬ store.original.catalog.retained object →
      TerminalOnly rules lineage store restored object) :
    Covered rules lineage store contents restored := by
  classical
  refine ⟨baseListed, ?_⟩
  intro object member
  by_cases retained : store.original.catalog.retained object
  · exact Or.inl retained
  · exact Or.inr (missing object member retained)

def namedCatalog (catalog : Catalog width capacity limit) : Catalog width capacity limit :=
  {catalog with retained := fun _ => True}

noncomputable def openNamedCut (rules : JointSource.Rules width slots Payload Ticket)
    (lineage : Lineage) (sealed : JointSource.Image slots Payload) (key : Key slots)
    (store : Store width capacity limit Ticket) (anchor : EnvelopeRecovery.Anchor width) :
    Option (Contents width capacity limit × Restored capacity limit) :=
  match JointSource.openSeal rules lineage sealed key with
  | none => none
  | some (record, body, _) =>
      if SealedDeliveryHandoff.atPosition anchor record.anchor.position then
        SealedDeliveryHandoff.openControl (namedCatalog store.original.catalog) store.original.authenticated
          anchor store.original.readNeeds store.original.deliveryNeeds body.readControl
      else none

noncomputable def mount (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (sealed : JointSource.Image slots Payload) (key : Key slots)
    (store : Store width capacity limit Ticket) (anchor : EnvelopeRecovery.Anchor width) :
    Option (Restored capacity limit) := by
  classical
  exact match openNamedCut rules.ordered.journal lineage sealed key store anchor with
  | none => none
  | some (contents, restored) =>
      if Covered rules lineage store contents restored then some restored else none

theorem mount_needs_exact_named_control_and_present_or_terminal_coverage
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (sealed : JointSource.Image slots Payload) (key : Key slots)
    (store : Store width capacity limit Ticket) (anchor : EnvelopeRecovery.Anchor width)
    (restored : Restored capacity limit) (mounted : mount rules lineage sealed key store anchor = some restored) :
    ∃ contents, openNamedCut rules.ordered.journal lineage sealed key store anchor = some (contents, restored) ∧
      Covered rules lineage store contents restored := by
  cases checked : openNamedCut rules.ordered.journal lineage sealed key store anchor with
  | none => simp [mount, checked] at mounted
  | some pair =>
      obtain ⟨contents, cut⟩ := pair
      simp only [mount, checked] at mounted
      split at mounted
      · next covered =>
          cases mounted
          exact ⟨contents, rfl, covered⟩
      · contradiction

theorem mounting_recovers_exactly_the_named_cut_across_two_ready_media_realizations
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (sealed : JointSource.Image slots Payload) (key : Key slots)
    (store alternative : Store width capacity limit Ticket) (anchor : EnvelopeRecovery.Anchor width)
    (sameNames : namedCatalog store.original.catalog = namedCatalog alternative.original.catalog)
    (sameAuthentication : store.original.authenticated = alternative.original.authenticated)
    (sameReads : store.original.readNeeds = alternative.original.readNeeds)
    (sameDeliveries : store.original.deliveryNeeds = alternative.original.deliveryNeeds)
    (first second : Restored capacity limit)
    (ready : mount rules lineage sealed key store anchor = some first)
    (otherReady : mount rules lineage sealed key alternative anchor = some second) :
    first = second := by
  obtain ⟨contents, before, _⟩ := mount_needs_exact_named_control_and_present_or_terminal_coverage
    rules lineage sealed key store anchor first ready
  obtain ⟨otherContents, after, _⟩ := mount_needs_exact_named_control_and_present_or_terminal_coverage
    rules lineage sealed key alternative anchor second otherReady
  unfold openNamedCut at before after
  rw [sameNames, sameAuthentication, sameReads, sameDeliveries] at before
  exact congrArg Prod.snd (Option.some.inj (before.symm.trans after))

noncomputable def activate (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (sealed : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (store : Store width capacity limit Ticket) (anchor : EnvelopeRecovery.Anchor width) :
    Option (Image slots capacity limit Payload) :=
  match mount rules lineage sealed install.original.installation.anchor.decision.key store anchor with
  | none => none
  | some restored =>
      SealedDeliveryHandoff.acceptedJournal (RetainedDelivery.decide rules lineage (withJournal restored sealed)
        (.source (.journal (.activate install))))

theorem exact_local_terminal_coverage_allows_activation_without_recontact
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (sealed : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (store : Store width capacity limit Ticket) (anchor : EnvelopeRecovery.Anchor width)
    (contents : Contents width capacity limit) (restored : Restored capacity limit)
    (target : Image slots capacity limit Payload)
    (named : openNamedCut rules.ordered.journal lineage sealed install.original.installation.anchor.decision.key
      store anchor = some (contents, restored))
    (covered : Covered rules lineage store contents restored)
    (installed : RetainedDelivery.decide rules lineage (withJournal restored sealed) (.source (.journal (.activate install))) =
      (target, .source (.journal .accepted))) :
    activate rules lineage sealed install store anchor = some target := by
  simp [activate, mount, named, ite_eq_left covered, SealedDeliveryHandoff.acceptedJournal_iff, installed]

theorem activation_does_not_consume_or_reissue_the_original_delivery_rows
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (sealed : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (store : Store width capacity limit Ticket) (anchor : EnvelopeRecovery.Anchor width)
    (restored : Restored capacity limit) (target : Image slots capacity limit Payload)
    (mounted : mount rules lineage sealed install.original.installation.anchor.decision.key store anchor = some restored)
    (installed : activate rules lineage sealed install store anchor = some target) :
    target.deliveries = restored.delivery := by
  have applied := (SealedDeliveryHandoff.acceptedJournal_iff _ target).mp
    (by simpa only [activate, mounted] using installed)
  exact (congrArg (fun result => result.1.deliveries) applied).symm

theorem a_durable_terminal_witness_cannot_authorize_a_stopped_reply
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (store : Store width capacity limit Ticket) (restored : Restored capacity limit)
    (slot : Fin limit) (row : Entry capacity) (found : restored.delivery.rows slot = some row)
    (terminal : Terminal rules lineage store slot row)
    (call : RTDBFailover.Invocation) (authenticate : RTDBFailover.Invocation → Prop)
    (held : Key limit → PoolState.Identity → OrderedReadReplay.Delivery capacity → Prop)
    (sign : RTDBFailover.Route → EnvelopeCodec.Bytes → Signature)
    (stable : ∀ receipt, rules.settled lineage ⟨slot, row.serial⟩ row receipt →
      ¬ held ⟨slot, row.serial⟩ row.borrow row.request) :
    RetainedDelivery.finish width restored.delivery ⟨slot, row.serial⟩ call authenticate held sign = none := by
  obtain ⟨receipt, _, _, stopped⟩ := terminal
  exact RetainedDelivery.possession_of_the_retained_result_cannot_finish_after_its_borrow_stops width restored.delivery
    ⟨slot, row.serial⟩ row call authenticate held sign (by simp [atKey, found]) (stable receipt stopped)

theorem after_activation_the_same_proof_can_drive_exact_ordered_settlement
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (sealed : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (store : Store width capacity limit Ticket) (anchor : EnvelopeRecovery.Anchor width)
    (restored : Restored capacity limit) (target : Image slots capacity limit Payload)
    (mounted : mount rules lineage sealed install.original.installation.anchor.decision.key store anchor = some restored)
    (installed : activate rules lineage sealed install store anchor = some target)
    (slot : Fin limit) (row : Entry capacity) (found : restored.delivery.rows slot = some row)
    (terminal : Terminal rules lineage store slot row)
    (openTarget : OrderedReadReplay.deliveryOpen (OrderedReadReplay.authority target.ordered) = true) :
    ∃ receipt after, store.receipts slot = some receipt ∧
      RetainedDelivery.decide rules lineage target (.settle ⟨slot, row.serial⟩ row.borrow receipt) = (after, .settled) ∧
      after.deliveries = DeliveryBook.clear restored.delivery ⟨slot, row.serial⟩ ∧
      after.deliveries.issued = restored.delivery.issued := by
  have preserved := activation_does_not_consume_or_reissue_the_original_delivery_rows
    rules lineage sealed install store anchor restored target mounted installed
  obtain ⟨receipt, exactReceipt, _, stop⟩ := terminal
  let after := {RetainedDelivery.advance target with deliveries := DeliveryBook.clear restored.delivery ⟨slot, row.serial⟩}
  refine ⟨receipt, after, exactReceipt, ?_, rfl, rfl⟩
  have atTarget : atKey target.deliveries ⟨slot, row.serial⟩ = some row := by
    rw [preserved]
    simp [atKey, found]
  simp [after, RetainedDelivery.decide, atTarget, openTarget, stop]
  rw [preserved]

structure Basis (width capacity limit : Nat) (Ticket : Type) where
  store : Store width capacity limit Ticket
  contents : Contents width capacity limit
  restored : Restored capacity limit

def withoutExtent (store : Store width capacity limit Ticket) (removed : Field width) :
    Store width capacity limit Ticket :=
  {store with original := {store.original with catalog :=
    {store.original.catalog with retained := fun object => object ≠ removed ∧ store.original.catalog.retained object}}}

def CanDispose (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (paths : List (Basis width capacity limit Ticket)) (object : Field width) : Prop :=
  ∀ basis ∈ paths, Covered rules lineage (withoutExtent basis.store object) basis.contents basis.restored

theorem a_selectable_base_with_an_unsubstituted_replay_need_blocks_disposal
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (paths : List (Basis width capacity limit Ticket)) (basis : Basis width capacity limit Ticket)
    (selectable : basis ∈ paths) (object : Field width) (needed : basis.store.baseNeeds object) :
    ¬ CanDispose rules lineage paths object := by
  intro authorized
  have retained : (withoutExtent basis.store object).original.catalog.retained object :=
    (coverage_keeps_replay_and_protected_reads_in_custody rules lineage (withoutExtent basis.store object)
      basis.contents basis.restored (authorized basis selectable) object).1 needed
  exact retained.1 rfl

theorem an_older_selectable_delivery_basis_needs_its_own_recoverable_receipt_before_disposal
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (paths : List (Basis width capacity limit Ticket)) (basis : Basis width capacity limit Ticket)
    (selectable : basis ∈ paths) (object : Field width) (listed : object ∈ basis.contents.dependencies)
    (slot : Fin limit) (row : Entry capacity) (pending : basis.restored.delivery.rows slot = some row)
    (needed : basis.store.original.deliveryNeeds row object)
    (unproven : ∀ receipt, basis.store.receipts slot = some receipt →
      ¬ (basis.store.durable receipt ∧ rules.settled lineage ⟨slot, row.serial⟩ row receipt)) :
    ¬ CanDispose rules lineage paths object := by
  intro authorized
  exact an_unproven_or_volatile_stop_cannot_replace_a_missing_delivery_extent rules lineage
    (withoutExtent basis.store object) basis.contents basis.restored slot row pending object listed needed
    (fun retained => retained.1 rfl) unproven (authorized basis selectable)

#print axioms an_extent_required_for_base_replay_cannot_be_replaced_by_a_stop
#print axioms coverage_keeps_replay_and_protected_reads_in_custody
#print axioms a_shared_extent_needs_terminal_evidence_for_every_delivery_before_substitution
#print axioms an_unproven_or_volatile_stop_cannot_replace_a_missing_delivery_extent
#print axioms exact_durable_stops_can_supply_the_delivery_only_portion_of_coverage
#print axioms mount_needs_exact_named_control_and_present_or_terminal_coverage
#print axioms mounting_recovers_exactly_the_named_cut_across_two_ready_media_realizations
#print axioms exact_local_terminal_coverage_allows_activation_without_recontact
#print axioms activation_does_not_consume_or_reissue_the_original_delivery_rows
#print axioms a_durable_terminal_witness_cannot_authorize_a_stopped_reply
#print axioms after_activation_the_same_proof_can_drive_exact_ordered_settlement

#print axioms a_selectable_base_with_an_unsubstituted_replay_need_blocks_disposal
#print axioms an_older_selectable_delivery_basis_needs_its_own_recoverable_receipt_before_disposal

end TerminalDeliveryWitness
