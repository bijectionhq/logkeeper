set_option warningAsError true

namespace ErasureCommit

/-- A selectable recovery image: its root generation and the generations of its suffix records. -/
structure Image where
  root : Nat
  suffix : List Nat

/-- Recovery from an image reads only keys of generation above the erased one. -/
def Readable (erased : Nat) (image : Image) : Prop :=
  erased < image.root ∧ ∀ generation ∈ image.suffix, erased < generation

/-- Commit rule: every selectable root is a clean root from after the rotation. -/
def MayCommit (erased : Nat) (selectable : List Image) : Prop :=
  ∀ image ∈ selectable, erased < image.root

/-- The grant fence: every record after a clean root carries at least that root's generation. -/
def Fenced (selectable : List Image) : Prop :=
  ∀ image ∈ selectable, ∀ generation ∈ image.suffix, image.root ≤ generation

theorem every_selectable_recovery_avoids_the_revoked_generation (erased : Nat) (selectable : List Image)
    (commit : MayCommit erased selectable) (fenced : Fenced selectable) :
    ∀ image ∈ selectable, Readable erased image := by
  intro image member
  refine ⟨commit image member, fun generation listed => ?_⟩
  have := fenced image member generation listed
  have := commit image member
  omega

theorem an_older_selectable_root_forbids_the_commit (erased : Nat) (selectable : List Image)
    (image : Image) (member : image ∈ selectable) (older : image.root ≤ erased) :
    ¬ MayCommit erased selectable := by
  intro commit
  have := commit image member
  omega

theorem an_unfenced_old_record_is_unreadable_after_revocation (erased : Nat) (image : Image)
    (stale : erased ∈ image.suffix) : ¬ Readable erased image := by
  intro readable
  have := readable.2 erased stale
  omega

#print axioms every_selectable_recovery_avoids_the_revoked_generation
#print axioms an_older_selectable_root_forbids_the_commit
#print axioms an_unfenced_old_record_is_unreadable_after_revocation

end ErasureCommit
