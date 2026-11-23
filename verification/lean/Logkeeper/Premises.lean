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
example : ¬ (1 : Nat) ∈ [3, 2] := by decide

end BarrierKeys

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
#print axioms VoterSlots.step_preserves_safety
#print axioms VoterSlots.acknowledged_receipt_survives
#print axioms VoterSlots.warm_rotation_then_power_loss_reachable

end Logkeeper.Premises
