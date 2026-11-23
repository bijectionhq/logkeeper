import Std

set_option warningAsError true

namespace Isolation

def append {Stream Record : Type} [DecidableEq Stream] (records : Stream → List Record)
    (target : Stream) (entry : Record) : Stream → List Record :=
  fun queried => if queried = target then records queried ++ [entry] else records queried

inductive OtherSteps {Stream Record : Type} [DecidableEq Stream] (observed : Stream) :
    (Stream → List Record) → (Stream → List Record) → Prop
  | same (records) : OtherSteps observed records records
  | next {first before} {target : Stream} (trace : OtherSteps observed first before)
      (different : observed ≠ target) (entry : Record) :
      OtherSteps observed first (append before target entry)

theorem record_projection_ignores_other_streams
    {Stream Record : Type} [DecidableEq Stream] {observed : Stream}
    {first last : Stream → List Record} (trace : OtherSteps observed first last) :
    last observed = first observed := by
  induction trace with
  | same => rfl
  | next _ different entry prior =>
      simpa [append, different] using prior

def CanAdmit (cap low high charge : Nat) : Prop :=
  low + high + charge ≤ cap

theorem pooled_admission_distinguishes_other_load (cap : Nat) (nonempty : 0 < cap) :
    CanAdmit cap 0 0 1 ∧ ¬ CanAdmit cap 0 cap 1 := by
  unfold CanAdmit
  omega

theorem reservation_protects_eligible_admission (cap reserved low high charge : Nat)
    (fitsPool : reserved ≤ cap) (highLimited : high ≤ cap - reserved)
    (lowEligible : low + charge ≤ reserved) : CanAdmit cap low high charge := by
  unfold CanAdmit
  omega

theorem borrowed_durable_capacity_blocks_guaranteed_arrival (cap low high charge : Nat)
    (poolFilled : low + high = cap) (positive : 0 < charge) :
    ¬ CanAdmit cap low high charge := by
  unfold CanAdmit
  omega

#print axioms record_projection_ignores_other_streams
#print axioms pooled_admission_distinguishes_other_load
#print axioms reservation_protects_eligible_admission
#print axioms borrowed_durable_capacity_blocks_guaranteed_arrival

end Isolation
