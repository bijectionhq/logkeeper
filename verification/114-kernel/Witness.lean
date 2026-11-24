import Collection
import Deletion

set_option warningAsError true

namespace Logkeeper.DecisionKernel

open Reducer (commitWithdrawal)

private def limits : Reducer.Limits :=
  ⟨⟨1024, 1024⟩, 1024, 128, 10, 7, 1, 1024, fun previous position time fingerprint =>
    previous + position + time + fingerprint⟩

private def initial : State :=
  let empty : Reducer.Cut := ⟨0, 0⟩
  let initialRoot : Reducer.Checkpoint := ⟨empty, 0, 1, 0⟩
  { placement := 1, position := 0, time := 0, commandHistory := 0,
    voterScope := 1, successor := none,
    history := ⟨⟨⟨1, 1⟩, 0, 0⟩, false, [], [], 0⟩, authority := ⟨none, 0, 1⟩,
    budget := ⟨⟨0, 0, 0⟩, 256⟩, window := ⟨1, 1, 256⟩, floor := empty, head := empty,
    checkpoints := ⟨initialRoot, none, fun _ => none, 0⟩,
    roster := fun _ => none, lastSerial := 0, holds := fun _ => none, leases := fun _ => none,
    objects := ⟨fun _ _ _ => False, fun _ => none, False, 0, 0⟩, book := fun _ => none }

private theorem initial_inv : Inv limits initial := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_, by decide, by decide⟩
    intro _ _ absent
    contradiction
  · change 0 ≤ 256 ∧ 0 + (256 - 0) ≤ 1024 ∧ 0 ≤ 128
    decide
  · change 0 < 1 ∧ 1 ≤ max 1 0
    decide
  · intro _ fenced
    exact False.elim (fenced rfl)
  · intro _ _ absent
    contradiction
  · intro _ _ absent
    contradiction

theorem reachable_refined_funding :
    ∃ bounds s t, Inv bounds s ∧ Trace bounds s t ∧
      t.position = 1 ∧ t.window.serial = 2 ∧ t.budget.window = 512 := by
  obtain ⟨s, t, inv, trace, position, serial, window⟩ := Reducer.reachable_funded_successor
  exact ⟨_, abstract s, abstract t, inv_image inv, trace_refines trace, position, serial, window⟩

theorem reachable_funding :
    ∃ bounds s t, Inv bounds s ∧ Trace bounds s t ∧
      s.window.serial = 1 ∧ t.position = 1 ∧ t.window.serial = 2 ∧ t.budget.window = 512 := by
  let window : Reducer.Window := ⟨2, 2, 512⟩
  let request : Request := ⟨1, .custodian, ⟨1, 4⟩, .fund window, 7⟩
  let chosen := advance limits initial 1 3 request
  let funded := { chosen with window, budget := Reducer.fundWindow chosen.budget.budget 512 }
  have paid : OrderedBudgets.admitsDebit chosen.budget.budget.ordinary 512 limits.ordinaryCapacity := by
    change 0 + 512 ≤ 1024
    decide
  have applied : Applied limits chosen request (.windowFunded window) funded := by
    refine ⟨?_, .stutter _, .stutter _, Or.inr (.fund _ 512 paid), Or.inl rfl,
      fun _ _ present => Or.inl present, ?_, rfl, rfl, ?_⟩
    · exact ⟨by simp [frame, chosen, funded], rfl, rfl, by decide, by decide, rfl, paid, rfl, rfl⟩
    · intro _ _ impossible
      contradiction
    · intro increased
      exact False.elim ((Nat.lt_irrefl _) increased)
  exact ⟨limits, initial, _, initial_inv,
    .next (.same initial) (.chosen rfl (.applied ⟨rfl, rfl, rfl⟩ applied)), rfl, rfl, rfl, rfl⟩

private theorem empty_graph {s : State} {node : Node}
    (noHolds : ∀ id, s.holds id = none)
    (noPreparation : s.checkpoints.preparing = none)
    (noSuffix : s.head.nextLsn ≤ s.checkpoints.selected.cut.nextLsn)
    (noLinks : ∀ name role owner, ¬ s.objects.references name role owner) :
    Reachable s node ↔ node = .replay ∨ node = .pending ∨ node = .checkpoint s.checkpoints.selected := by
  constructor
  · intro path
    cases path with
    | root root =>
      cases root with
      | replay => exact Or.inl rfl
      | pending => exact Or.inr (Or.inl rfl)
      | hold present => simp [noHolds] at present
    | next _ edge =>
      cases edge with
      | selected => exact Or.inr (Or.inr rfl)
      | suffix starts existsAt => omega
      | protectedRoot present | protectedRecord present _ _ => simp [noHolds] at present
      | pendingBase present | pendingObject present _ => simp [noPreparation] at present
      | rootObject references | recordObject references => exact False.elim (noLinks _ _ _ references)
  · rintro (rfl | rfl | rfl)
    · exact .root .replay
    · exact .root .pending
    · exact .next (.root .replay) .selected

/-- Both images follow one chosen decision from the same valid image. Only
the success installs a version, although the reachability relation agrees. -/
theorem fence_is_not_graph_determined :
    ∃ before plain fenced : State, Inv limits before ∧
      Trace limits before plain ∧ Trace limits before fenced ∧
      (∀ node, Reachable plain node ↔ Reachable fenced node) ∧
      before.objects.fence 1 = none ∧ plain.objects.fence 1 = none ∧
      fenced.objects.fence 1 = some 7 := by
  let request : Request := ⟨1, .custodian, ⟨1, 4⟩, .fence 1 7, 7⟩
  let chosen := advance limits initial 1 3 request
  let installed := { chosen with objects := commitWithdrawal chosen.objects 1 7 }
  have admitted : fresh limits chosen request := ⟨rfl, rfl, rfl⟩
  have available : ObjectWithdrawal.canWithdraw chosen.objects 1 :=
    ⟨id, fun ⟨_, _, present⟩ => present⟩
  have unused : ¬ ObjectWithdrawal.fenced chosen.objects 1 := fun fenced => fenced rfl
  have installedEffect : Applied limits chosen request (.objectWithdrawn 1 7) installed := by
    refine ⟨?_, .stutter _, .stutter _, Or.inl rfl,
      Or.inr (Reducer.commit_withdrawal_projects _ _ _ available unused),
      ?_, ?_, rfl, rfl, ?_⟩
    · exact ⟨by simp [frame, chosen, installed], rfl, rfl, rfl,
        Or.inr ⟨available, unused, rfl⟩⟩
    · intro _ _ present
      exact Or.inl present
    · intro _ _ present
      contradiction
    · intro increased
      exact False.elim ((Nat.lt_irrefl _) increased)
  let refusedBook := recordReceipt chosen.placement chosen.position request (.error .unavailable) chosen.book
  let plain := { chosen with book := refusedBook }
  let installedBook := recordReceipt chosen.placement chosen.position request
    (.ok (.objectWithdrawn 1 7)) (Reducer.pruneBook chosen.position installed.holds chosen.book)
  let fenced := { installed with book := installedBook }
  refine ⟨initial, plain, fenced, initial_inv,
    .next (.same initial) (.chosen rfl (.refused .unavailable admitted)),
    .next (.same initial) (.chosen rfl (.applied admitted installedEffect)), ?_, rfl, rfl, rfl⟩
  intro node
  have left := empty_graph (s := plain) (node := node)
    (fun _ => rfl) rfl (Nat.le_refl _) (fun _ _ _ h => h)
  have right := empty_graph (s := fenced) (node := node)
    (fun _ => rfl) rfl (Nat.le_refl _) (fun _ _ _ h => h)
  exact left.trans right.symm

end Logkeeper.DecisionKernel
