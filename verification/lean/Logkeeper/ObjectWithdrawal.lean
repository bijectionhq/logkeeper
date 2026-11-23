namespace Logkeeper.ObjectWithdrawal

inductive Role where
  | root | preparation | suffix | hold
  deriving DecidableEq

structure State where
  referenced : Role → Prop
  fenced : Bool

def Safe (s : State) : Prop :=
  s.fenced = true → ∀ role, ¬ s.referenced role

inductive Step : State → State → Prop where
  | acquire (s : State) (role : Role) (openName : s.fenced = false) :
      Step s ⟨fun r => r = role ∨ s.referenced r, s.fenced⟩
  | release (s : State) (role : Role) :
      Step s ⟨fun r => r ≠ role ∧ s.referenced r, s.fenced⟩
  | withdraw (s : State) (unreferenced : ∀ r, ¬ s.referenced r) :
      Step s ⟨s.referenced, true⟩
  | recover (s : State) : Step s s

theorem order_preserves_separation {before after : State}
    (safe : Safe before) (step : Step before after) : Safe after := by
  cases step with
  | acquire _ openName =>
      intro fenced
      simp_all
  | release _ =>
      intro fenced role reference
      exact safe fenced role reference.2
  | withdraw unreferenced => exact fun _ => unreferenced
  | recover => exact safe

inductive Trace : State → State → Prop where
  | empty (s : State) : Trace s s
  | next {start here after : State} (earlier : Trace start here) (step : Step here after) :
      Trace start after

theorem trace_preserves_separation {start finish : State}
    (safe : Safe start) (trace : Trace start finish) : Safe finish := by
  induction trace with
  | empty => exact safe
  | next _ step preceding => exact order_preserves_separation preceding step

def empty : State := ⟨fun _ => False, false⟩
def withdrawn : State := ⟨fun _ => False, true⟩
def late : State := ⟨fun r => r = .suffix ∨ False, true⟩

theorem reachable_fence : Step empty withdrawn :=
  Step.withdraw empty (fun _ h => h)

def AcquireWithoutFence (s t : State) : Prop :=
  t = ⟨fun r => r = .suffix ∨ s.referenced r, s.fenced⟩

theorem unchecked_acquire_violates_separation :
    AcquireWithoutFence withdrawn late ∧ ¬ Safe late :=
  ⟨rfl, fun safe => safe rfl .suffix (Or.inl rfl)⟩

def held : State := ⟨fun r => r = .hold ∨ False, false⟩

theorem reachable_hold : Step empty held :=
  Step.acquire empty .hold rfl

def WithdrawWithoutReferences (s t : State) : Prop :=
  t = ⟨s.referenced, true⟩

theorem unchecked_withdrawal_violates_separation :
    ∃ blocked, WithdrawWithoutReferences held blocked ∧ ¬ Safe blocked :=
  ⟨⟨held.referenced, true⟩, rfl, fun safe => safe rfl .hold (Or.inl rfl)⟩

#print axioms trace_preserves_separation
#print axioms reachable_fence
#print axioms reachable_hold
#print axioms unchecked_acquire_violates_separation
#print axioms unchecked_withdrawal_violates_separation

end Logkeeper.ObjectWithdrawal
