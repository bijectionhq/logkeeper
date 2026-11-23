namespace Logkeeper.Premises

set_option warningAsError true

namespace BarrierKeys

/-- Authorized configurations carry the verification keys of their predecessor.
The keys in this model are public and scoped to one logical journal placement. -/
inductive Rotations {Key : Type} (first : List Key) : List Key → Prop where
  | start : Rotations first first
  | rotate {source target} : Rotations first source →
      (∀ key ∈ source, key ∈ target) → Rotations first target

theorem retained_across_rotations {Key : Type} {first last : List Key}
    (rotations : Rotations first last) {issuer : Key} (issued : issuer ∈ first) :
    issuer ∈ last := by
  induction rotations with
  | start => exact issued
  | rotate _ carries ih => exact carries issuer ih

theorem two_rotations_reachable : Rotations [1] [3, 2, 1] := by
  apply Rotations.rotate (source := [2, 1])
  · exact Rotations.rotate Rotations.start (by simp)
  · simp

-- Keeping only the immediate predecessor loses the oldest receipt's issuer.
theorem dropped_historical_key_control : ¬ (1 : Nat) ∈ [3, 2] := by decide

/-- The three public key sources for one trusted installation. -/
structure KeyRoster (Key : Type) where
  active : List Key
  predecessor : List Key
  retained : List Key

def verificationKeys (roster : KeyRoster Key) : List Key :=
  roster.active ++ roster.predecessor ++ roster.retained

def validSuccessorKeys (source target : KeyRoster Key) : Prop :=
  (∀ key ∈ target.predecessor, key ∈ source.active) ∧
  (∀ key ∈ verificationKeys source, key ∈ verificationKeys target)

def repairAuthority (target : KeyRoster Key) (key : Key) : Prop :=
  key ∈ target.predecessor

theorem valid_successor_extends_rotations {first : List Key} {source target : KeyRoster Key}
    (trace : Rotations first (verificationKeys source))
    (valid : validSuccessorKeys source target) :
    Rotations first (verificationKeys target) :=
  Rotations.rotate trace valid.2

theorem repair_authority_is_active {source target : KeyRoster Key} {key : Key}
    (valid : validSuccessorKeys source target) (authorized : repairAuthority target key) :
    key ∈ source.active :=
  valid.1 key authorized

private def firstRoster : KeyRoster Nat := ⟨[1], [], []⟩
private def secondRoster : KeyRoster Nat := ⟨[2], [1], []⟩
private def thirdRoster : KeyRoster Nat := ⟨[3], [2], [1]⟩

theorem retained_verification_only_reachable :
    Rotations (verificationKeys firstRoster) (verificationKeys thirdRoster) ∧
    1 ∈ verificationKeys thirdRoster ∧ ¬ repairAuthority thirdRoster 1 := by
  refine ⟨?_, by decide, by simp [repairAuthority, thirdRoster]⟩
  apply valid_successor_extends_rotations (source := secondRoster)
  · exact valid_successor_extends_rotations (source := firstRoster) Rotations.start
      (by simp [validSuccessorKeys, verificationKeys, firstRoster, secondRoster])
  · simp [validSuccessorKeys, verificationKeys, secondRoster, thirdRoster]

-- Selecting repair authority from the whole verification set admits key 1.
theorem historical_repair_key_control :
    1 ∈ verificationKeys thirdRoster ∧ 1 ∉ secondRoster.active := by decide

end BarrierKeys

namespace SignatureScope

inductive Domain where
  | barrier
  | rotation
  deriving DecidableEq

structure BarrierFields (Placement Reader Invocation Checkpoint Cut : Type) where
  placement : Placement
  reader : Reader
  invocation : Invocation
  position : Nat
  checkpoint : Checkpoint
  through : Cut

structure BarrierClaim (Placement Reader Invocation Checkpoint Cut : Type) where
  fields : BarrierFields Placement Reader Invocation Checkpoint Cut
  start : Cut

structure ExpectedBarrier (Placement Reader Invocation : Type) where
  isBarrier : Bool
  placement : Placement
  worker : Option Reader
  invocation : Invocation

def canonicalStart (checkpointCut : Checkpoint → Cut)
    (claim : BarrierClaim Placement Reader Invocation Checkpoint Cut) : Prop :=
  claim.start = checkpointCut claim.fields.checkpoint

def exactBarrierInvocation (scope : Placement) (expected : ExpectedBarrier Placement Reader Invocation)
    (fields : BarrierFields Placement Reader Invocation Checkpoint Cut) : Prop :=
  expected.isBarrier = true ∧ fields.placement = scope ∧ expected.placement = scope ∧
    expected.worker = some fields.reader ∧ fields.invocation = expected.invocation

structure ReceiptScope (Placement Reader Invocation : Type) where
  placement : Placement
  worker : Option Reader
  invocation : Invocation
  position : Nat

def exactBarrierReceipt (receipt : ReceiptScope Placement Reader Invocation)
    (outcome : Option (BarrierClaim Placement Reader Invocation Checkpoint Cut))
    (proof : Option (BarrierClaim Placement Reader Invocation Checkpoint Cut)) : Prop :=
  match outcome, proof with
  | none, none => True
  | some read, some claim =>
      read = claim ∧ receipt.placement = read.fields.placement ∧
        receipt.worker = some read.fields.reader ∧ receipt.invocation = read.fields.invocation ∧
        receipt.position = read.fields.position
  | _, _ => False

def exactReceiptScope (placement scope : Placement) (principal expectedPrincipal : Principal)
    (invocation expectedInvocation : Invocation) : Prop :=
  placement = scope ∧ principal = expectedPrincipal ∧ invocation = expectedInvocation

theorem accepted_receipt_scope_is_exact
    {placement scope : Placement} {principal expectedPrincipal : Principal}
    {invocation expectedInvocation : Invocation}
    (accepted : exactReceiptScope placement scope principal expectedPrincipal
      invocation expectedInvocation) :
    placement = scope ∧ principal = expectedPrincipal ∧ invocation = expectedInvocation :=
  accepted

/-- The ideal signature contract records the original domain and exact payload
for each key and signature. The byte representation is a separate refinement. -/
def verify (origin : Key → Signature → Option (Domain × Bytes))
    (key : Key) (domain : Domain) (bytes : Bytes) (signature : Signature) : Prop :=
  origin key signature = some (domain, bytes)

theorem canonical_fields_bind_claim {checkpointCut : Checkpoint → Cut}
    {a b : BarrierClaim Placement Reader Invocation Checkpoint Cut}
    (ha : canonicalStart checkpointCut a) (hb : canonicalStart checkpointCut b)
    (fields : a.fields = b.fields) : a = b := by
  cases a
  cases b
  cases fields
  simp_all [canonicalStart]

theorem accepted_barrier_binds_claim
    {checkpointCut : Checkpoint → Cut}
    {origin : Key → Signature → Option (Domain × BarrierFields Placement Reader Invocation Checkpoint Cut)}
    {scope : Placement} {expected : ExpectedBarrier Placement Reader Invocation}
    {claim signed : BarrierClaim Placement Reader Invocation Checkpoint Cut}
    {key : Key} {signature : Signature}
    (invocation : exactBarrierInvocation scope expected claim.fields)
    (first : verify origin key .barrier signed.fields signature)
    (second : verify origin key .barrier claim.fields signature)
    (hc : canonicalStart checkpointCut claim) (hs : canonicalStart checkpointCut signed) :
    claim = signed ∧ exactBarrierInvocation scope expected signed.fields := by
  have fields := congrArg Prod.snd (Option.some.inj (second.symm.trans first))
  have eq := canonical_fields_bind_claim hc hs fields
  exact ⟨eq, eq ▸ invocation⟩

theorem accepted_barrier_receipt_is_exact
    {receipt : ReceiptScope Placement Reader Invocation}
    {read claim : BarrierClaim Placement Reader Invocation Checkpoint Cut}
    (accepted : exactBarrierReceipt receipt (some read) (some claim)) :
    read = claim ∧ receipt.placement = claim.fields.placement ∧
      receipt.worker = some claim.fields.reader ∧ receipt.invocation = claim.fields.invocation ∧
      receipt.position = claim.fields.position := by
  obtain ⟨rfl, rest⟩ := accepted
  exact ⟨rfl, rest⟩

theorem rotation_domain_is_distinct {origin : Key → Signature → Option (Domain × Bytes)}
    {key : Key} {signature : Signature} {rotation barrier : Bytes}
    (signed : verify origin key .rotation rotation signature) :
    ¬ verify origin key .barrier barrier signature := by
  intro other
  have impossible := congrArg Prod.fst (Option.some.inj (signed.symm.trans other))
  cases impossible

private def sample : BarrierClaim Nat Nat Nat Nat Nat := ⟨⟨1, 2, 3, 4, 5, 6⟩, 5⟩
private def sampleReceipt : ReceiptScope Nat Nat Nat := ⟨1, some 2, 3, 4⟩

theorem exact_barrier_reachable :
    exactBarrierInvocation 1 ⟨true, 1, some 2, 3⟩ sample.fields ∧
    canonicalStart id sample ∧ exactBarrierReceipt sampleReceipt (some sample) (some sample) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

private def rotationOrigin (_ : Nat) (_ : Nat) : Option (Domain × List Nat) :=
  some (.rotation, [7, 8])

theorem rotation_evidence_reachable : verify rotationOrigin 1 .rotation [7, 8] 2 := rfl

-- All remaining request coordinates agree when the invocation check is omitted.
theorem omitted_invocation_control :
    let changed : ExpectedBarrier Nat Nat Nat := ⟨true, 1, some 2, 9⟩
    changed.isBarrier = true ∧ sample.fields.placement = 1 ∧ changed.placement = 1 ∧
      changed.worker = some sample.fields.reader ∧ ¬ exactBarrierInvocation 1 changed sample.fields := by
  simp [exactBarrierInvocation, sample]

-- The receipt still names the same invocation after its unsigned through cut changes.
theorem changed_receipt_cut_control :
    let changed := { sample with fields := { sample.fields with through := 7 } }
    exactReceiptScope sampleReceipt.placement sample.fields.placement sampleReceipt.worker
      (some changed.fields.reader) sampleReceipt.invocation changed.fields.invocation ∧
      ¬ exactBarrierReceipt sampleReceipt (some changed) (some sample) := by
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  intro accepted
  have cuts := congrArg (fun claim => claim.fields.through) accepted.1
  simp [sample] at cuts

-- A domain-blind rotation verifier can accept a signature on the same barrier payload.
theorem omitted_domain_control :
    verify (fun (_ : Nat) (_ : Nat) => some (Domain.barrier, [7])) 1 .barrier [7] 2 ∧
      ¬ verify (fun (_ : Nat) (_ : Nat) => some (Domain.barrier, [7])) 1 .rotation [7] 2 := by
  simp [verify]

end SignatureScope

namespace VoterSlots

/-- Model the latest durable selection and a potentially newer visible one.
The older generation, when still intact, cannot replace the latest durable
selection after its successful flush. A slot index is one bit. -/
structure Media (Image : Type) where
  durable : Option (Bool × Image)
  visible : Bool × Image
  ready : Bool

def initial (image : Image) : Media Image := ⟨some (false, image), (false, image), true⟩

/-- Overwrite the opposite slot and expose a valid header after the body is
flushed. The header may still be volatile. Conservatively discard any durable
selection in the overwritten slot as soon as the overwrite begins. -/
def stage (media : Media Image) (image : Image) : Media Image :=
  ⟨media.durable.filter (fun slot => slot.1 == media.visible.1),
    (!media.visible.1, image), false⟩

def warm (media : Media Image) : Media Image := { media with ready := false }

def flush (media : Media Image) : Media Image :=
  { media with durable := some media.visible, ready := true }

def powerLoss (media : Media Image) (survivor : Bool × Image) : Media Image :=
  { media with visible := survivor, ready := false }

/-- The chosen-prefix layer supplies exact receipt coverage for every later
candidate while the receipt remains retained. The media layer preserves it. -/
inductive Step (covers : Image → Prop) : Media Image → Media Image → Prop where
  | stage {media image} : media.ready = true → covers image →
      Step covers media (stage media image)
  | warm {media} : Step covers media (warm media)
  | flush {media} : Step covers media (flush media)
  | powerLoss {media survivor} : media.durable = some survivor →
      Step covers media (powerLoss media survivor)

inductive Reachable (covers : Image → Prop) (start : Media Image) : Media Image → Prop where
  | start : Reachable covers start start
  | next {before after} : Reachable covers start before → Step covers before after →
      Reachable covers start after

structure Safe (covers : Image → Prop) (media : Media Image) : Prop where
  recoverable : ∃ slot, media.durable = some slot ∧ covers slot.2
  visible : covers media.visible.2
  canRotate : media.ready = true → media.durable = some media.visible

theorem step_preserves_safety {covers : Image → Prop} {before after : Media Image}
    (safe : Safe covers before) (step : Step covers before after) : Safe covers after := by
  cases step with
  | stage ready covered =>
      refine ⟨⟨before.visible, ?_, safe.visible⟩, covered, by simp [stage]⟩
      simp [stage, safe.canRotate ready]
  | warm => exact ⟨safe.recoverable, safe.visible, by simp [warm]⟩
  | flush => exact ⟨⟨before.visible, rfl, safe.visible⟩, safe.visible, fun _ => rfl⟩
  | powerLoss selected =>
      obtain ⟨_, recovered, covered⟩ := safe.recoverable
      rw [selected] at recovered
      cases recovered
      exact ⟨safe.recoverable, covered, by simp [powerLoss]⟩

theorem acknowledged_receipt_survives {covers : Image → Prop} {image : Image}
    (acked : covers image) {after : Media Image}
    (trace : Reachable covers (initial image) after) :
    ∃ slot, after.durable = some slot ∧ covers slot.2 := by
  suffices Safe covers after from this.recoverable
  induction trace with
  | start => exact ⟨⟨(false, image), rfl, acked⟩, acked, fun _ => rfl⟩
  | next _ step ih => exact step_preserves_safety ih step

private def interrupted := warm (stage (initial 1) 2)
private def second := stage (flush interrupted) 3

/-- Two rotations, one warm restart and one power loss. The second rotation
can reuse the original slot only after re-flushing the warm selection. -/
theorem warm_rotation_then_power_loss_reachable :
    Reachable (fun n => 1 ≤ n) (initial 1) (powerLoss second (true, 2)) := by
  apply Reachable.next _ (Step.powerLoss rfl)
  apply Reachable.next _ (Step.stage rfl (by decide))
  apply Reachable.next _ Step.flush
  apply Reachable.next _ Step.warm
  exact Reachable.next Reachable.start (Step.stage rfl (by decide))

-- If warm reopen falsely permits rotation, it can overwrite the only durable slot.
example : (stage { interrupted with ready := true } 3).durable = none := rfl

end VoterSlots

#print axioms BarrierKeys.retained_across_rotations
#print axioms BarrierKeys.two_rotations_reachable
#print axioms BarrierKeys.valid_successor_extends_rotations
#print axioms BarrierKeys.repair_authority_is_active
#print axioms BarrierKeys.retained_verification_only_reachable
#print axioms BarrierKeys.dropped_historical_key_control
#print axioms BarrierKeys.historical_repair_key_control
#print axioms SignatureScope.accepted_barrier_binds_claim
#print axioms SignatureScope.accepted_barrier_receipt_is_exact
#print axioms SignatureScope.accepted_receipt_scope_is_exact
#print axioms SignatureScope.rotation_domain_is_distinct
#print axioms SignatureScope.exact_barrier_reachable
#print axioms SignatureScope.rotation_evidence_reachable
#print axioms SignatureScope.omitted_invocation_control
#print axioms SignatureScope.changed_receipt_cut_control
#print axioms SignatureScope.omitted_domain_control
#print axioms VoterSlots.step_preserves_safety
#print axioms VoterSlots.acknowledged_receipt_survives
#print axioms VoterSlots.warm_rotation_then_power_loss_reachable

end Logkeeper.Premises
