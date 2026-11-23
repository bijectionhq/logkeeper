import EnvelopeCodec
import JointCheckpoint

set_option warningAsError true

namespace EnvelopeRecovery

open EnvelopeCodec

variable {width : Nat} {Control Data : Type}

structure Anchor (width : Nat) where
  format : UInt8
  lineage : Field width
  position : Field width
  prefixCommitment : Field width
  dataEnd : Field width

def Matches (header : Envelope width) (expected : Anchor width) : Prop :=
  header.format = expected.format ∧ header.lineage = expected.lineage ∧
  header.position = expected.position ∧ header.prefixCommitment = expected.prefixCommitment ∧
  header.dataEnd = expected.dataEnd

theorem genuine_checkpoint_binds_the_ordered_position
    {header : Envelope width} {expected : Anchor width} (checked : Matches header expected) :
    header.position = expected.position := by
  exact checked.2.2.1

structure Catalog (width : Nat) (Control Data : Type) where
  control : Field width → Option Control
  data : Field width → Option Data
  manifests : Field width → Option (List (Field width))
  retained : Field width → Prop

structure Contents (width : Nat) (Control Data : Type) where
  control : Control
  data : Data
  dependencies : List (Field width)

def readNamed (catalog : Catalog width Control Data) (header : Envelope width) :
    Option (Contents width Control Data) := do
  let control ← catalog.control header.control
  let data ← catalog.data header.data
  let dependencies ← catalog.manifests header.evidence
  pure ⟨control, data, dependencies⟩

theorem exact_loading_resolves_all_three_named_components
    {catalog : Catalog width Control Data} {header : Envelope width} {contents : Contents width Control Data}
    (loaded : readNamed catalog header = some contents) :
    catalog.control header.control = some contents.control ∧ catalog.data header.data = some contents.data ∧
    catalog.manifests header.evidence = some contents.dependencies := by
  cases control : catalog.control header.control with
  | none => simp [readNamed, control] at loaded
  | some controlValue =>
      cases data : catalog.data header.data with
      | none => simp [readNamed, control, data] at loaded
      | some dataValue =>
          cases evidence : catalog.manifests header.evidence with
          | none => simp [readNamed, control, data, evidence] at loaded
          | some dependencies =>
              simp [readNamed, control, data, evidence] at loaded
              subst contents
              exact ⟨rfl, rfl, rfl⟩

structure Opened (catalog : Catalog width Control Data) (authenticated : Bytes → Prop)
    (expected : Anchor width) (necessary : Field width → Prop)
    (wire : Bytes) (header : Envelope width) (contents : Contents width Control Data) : Prop where
  canonical : decode width wire = some header
  authorized : authenticated wire
  anchor : Matches header expected
  named : readNamed catalog header = some contents
  manifestCovers : ∀ object, necessary object → object ∈ contents.dependencies
  covered : ∀ object ∈ contents.dependencies, catalog.retained object

def DependencyCoverage (catalog : Catalog width Control Data) (necessary : Field width → Prop)
    (contents : Contents width Control Data) : Prop :=
  (∀ object, necessary object → object ∈ contents.dependencies) ∧
  (∀ object ∈ contents.dependencies, catalog.retained object)

noncomputable def openChecked (catalog : Catalog width Control Data) (authenticated : Bytes → Prop)
    (expected : Anchor width) (necessary : Field width → Prop) (wire : Bytes) :
    Option (Envelope width × Contents width Control Data) := by
  classical
  exact match decode width wire with
  | none => none
  | some header =>
      if authenticated wire ∧ Matches header expected then
        match readNamed catalog header with
        | none => none
        | some contents =>
            if DependencyCoverage catalog necessary contents then some (header, contents) else none
      else none

theorem a_successful_open_has_all_authentication_and_custody_checks
    {catalog : Catalog width Control Data} {authenticated : Bytes → Prop} {expected : Anchor width}
    {necessary : Field width → Prop} {wire : Bytes} {header : Envelope width}
    {contents : Contents width Control Data}
    (accepted : openChecked catalog authenticated expected necessary wire = some (header, contents)) :
    Opened catalog authenticated expected necessary wire header contents := by
  cases decoded : decode width wire with
  | none => simp [openChecked, decoded] at accepted
  | some decodedHeader =>
      simp only [openChecked, decoded] at accepted
      split at accepted
      next verified =>
        cases named : readNamed catalog decodedHeader with
        | none => simp [named] at accepted
        | some body =>
            simp only [named] at accepted
            split at accepted
            next complete =>
              cases accepted
              exact ⟨decoded, verified.1, verified.2, named, complete.1, complete.2⟩
            next => simp at accepted
      next => simp at accepted

theorem authenticating_a_complete_message_binds_each_component
    {catalog : Catalog width Control Data} {authenticated : Bytes → Prop} {expected : Anchor width}
    {necessary : Field width → Prop} {wire : Bytes} {header : Envelope width}
    {contents : Contents width Control Data}
    (opened : Opened catalog authenticated expected necessary wire header contents) :
    authenticated (encode header) ∧ header.position = expected.position ∧
    catalog.control header.control = some contents.control ∧ catalog.data header.data = some contents.data ∧
    catalog.manifests header.evidence = some contents.dependencies := by
  have exactWire := accepted_envelope_has_one_canonical_encoding opened.canonical
  exact ⟨exactWire.symm ▸ opened.authorized, genuine_checkpoint_binds_the_ordered_position opened.anchor,
    exact_loading_resolves_all_three_named_components opened.named⟩

theorem identical_certified_bytes_cannot_open_a_different_body
    {catalog : Catalog width Control Data} {authenticated : Bytes → Prop} {expected : Anchor width}
    {necessary : Field width → Prop} {wire : Bytes} {first second : Envelope width}
    {body alternate : Contents width Control Data}
    (left : Opened catalog authenticated expected necessary wire first body)
    (right : Opened catalog authenticated expected necessary wire second alternate) :
    first = second ∧ body = alternate := by
  have exactHeader := Option.some.inj (left.canonical.symm.trans right.canonical)
  subst second
  exact ⟨rfl, Option.some.inj (left.named.symm.trans right.named)⟩

theorem opened_checkpoint_covers_every_required_object
    {catalog : Catalog width Control Data} {authenticated : Bytes → Prop} {expected : Anchor width}
    {necessary : Field width → Prop} {wire : Bytes} {header : Envelope width}
    {contents : Contents width Control Data}
    (opened : Opened catalog authenticated expected necessary wire header contents)
    (object : Field width) (needed : necessary object) : catalog.retained object := by
  exact opened.covered object (opened.manifestCovers object needed)

theorem a_new_control_cut_can_reuse_the_exact_data_component
    {catalog : Catalog width Control Data} {first next : Envelope width}
    {before after : Contents width Control Data}
    (old : readNamed catalog first = some before) (new : readNamed catalog next = some after)
    (sameRoot : first.data = next.data) : before.data = after.data := by
  have beforeData := (exact_loading_resolves_all_three_named_components old).2.1
  have afterData := (exact_loading_resolves_all_three_named_components new).2.1
  rw [sameRoot] at beforeData
  exact Option.some.inj (beforeData.symm.trans afterData)

variable {slots : Nat} {Pool Payload Root Ticket Db : Type}

abbrev JointContents (width slots : Nat) (Pool Root Db Payload : Type) :=
  Contents width (JointCheckpoint.ControlImage slots Pool Root)
    (CheckpointReconstruction.Image Db Payload Root)

theorem a_joint_checkpoint_recovers_control_and_data_from_the_same_certified_cut
    (engine : CheckpointReconstruction.Engine Db Payload Root)
    (limits : Kernel.Limits) (rules : UnifiedSource.Rules slots Pool Payload Ticket)
    (initial checkpoint : UnifiedSource.State slots Pool Payload)
    (earlier tail : List (UnifiedSource.Command slots Pool Payload Ticket))
    (catalog : Catalog width (JointCheckpoint.ControlImage slots Pool Root)
      (CheckpointReconstruction.Image Db Payload Root))
    (authenticated : Bytes → Prop) (expected : Anchor width) (needed : Field width → Prop)
    (wire : Bytes) (header : Envelope width) (contents : JointContents width slots Pool Root Db Payload)
    (opened : Opened catalog authenticated expected needed wire header contents)
    (chosen : checkpoint = (UnifiedSource.replay limits rules initial earlier).1)
    (control : contents.control = JointCheckpoint.summarize engine.stream contents.data.root checkpoint)
    (certifiedData : CheckpointReconstruction.Certified engine checkpoint.core.stream contents.data)
    (target : CheckpointReconstruction.Cut) (records : List (Kernel.Entry Payload))
    (admitted : CheckpointReconstruction.Admitted engine checkpoint.core.stream contents.data target records) :
    authenticated (encode header) ∧
      contents.control.position = (UnifiedSource.replay limits rules initial earlier).1.position ∧
      (∀ object, needed object → catalog.retained object) ∧
      (UnifiedSource.replay limits rules checkpoint tail).1 =
        (UnifiedSource.replay limits rules initial (earlier ++ tail)).1 ∧
      CheckpointReconstruction.replay engine contents.data.root records =
        some (CheckpointReconstruction.stateAt engine checkpoint.core.stream.history target.next) := by
  have matched := authenticating_a_complete_message_binds_each_component opened
  have fullTail := UnifiedSource.a_certified_joint_checkpoint_replays_the_same_tail limits rules
    initial checkpoint earlier tail chosen
  have stateTail := congrArg Prod.fst fullTail
  refine ⟨matched.1, ?_, fun object use => opened_checkpoint_covers_every_required_object opened object use,
    stateTail, CheckpointReconstruction.admitted_replay_recovers_exact_cut certifiedData admitted⟩
  rw [control, chosen]
  rfl

#print axioms genuine_checkpoint_binds_the_ordered_position
#print axioms exact_loading_resolves_all_three_named_components
#print axioms a_successful_open_has_all_authentication_and_custody_checks
#print axioms authenticating_a_complete_message_binds_each_component
#print axioms identical_certified_bytes_cannot_open_a_different_body
#print axioms opened_checkpoint_covers_every_required_object
#print axioms a_new_control_cut_can_reuse_the_exact_data_component
#print axioms a_joint_checkpoint_recovers_control_and_data_from_the_same_certified_cut

end EnvelopeRecovery
