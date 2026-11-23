import Logkeeper.OrderedWriter

set_option warningAsError true

/- The recovery image and its fence originate in Study 112
   (112-erasure-rotation/ErasureCommit.lean). -/
namespace ErasureCommit

open Logkeeper.Kernel.Ordered (authorize_writer next_writer_epoch)

structure Image where
  root : Nat
  suffix : List Nat

def Readable (erased : Nat) (image : Image) : Prop :=
  erased < image.root ∧ ∀ generation ∈ image.suffix, erased < generation

def MayCommit (erased : Nat) (selectable : List Image) : Prop :=
  ∀ image ∈ selectable, erased < image.root

def Fenced (selectable : List Image) : Prop :=
  ∀ image ∈ selectable, ∀ generation ∈ image.suffix, image.root ≤ generation

theorem every_selectable_recovery_avoids_the_revoked_generation
    (erased : Nat) (selectable : List Image)
    (commit : MayCommit erased selectable) (fenced : Fenced selectable) :
    ∀ image ∈ selectable, Readable erased image := by
  intro image member
  exact ⟨commit image member, fun generation listed =>
    Nat.lt_of_lt_of_le (commit image member) (fenced image member generation listed)⟩

def rotation_head {Grant Cut Checkpoint : Type}
    [DecidableEq Grant] [DecidableEq Cut] [DecidableEq Checkpoint]
    (custodian : Bool) (current : Option Grant) (grant : Grant)
    (head requestedCut : Cut) (published requested : Checkpoint) : Bool :=
  custodian && decide (current = some grant ∧ head = requestedCut ∧ published ≠ requested)

def exact_preparation {Cut Root Custody : Type}
    [DecidableEq Cut] [DecidableEq Root] [DecidableEq Custody]
    (preparedCut cut : Cut) (preparedRoot root : Root) (preparedCustody custody : Custody)
    (manifestPresent : Bool) (observed : Option Cut) : Bool :=
  manifestPresent && decide (preparedCut = cut ∧ preparedRoot = root ∧
    preparedCustody = custody ∧ observed = some cut)

def successor_generation {Grant Checkpoint : Type} [DecidableEq Grant] [DecidableEq Checkpoint]
    (erasure : Bool) (preparedSource grant : Grant) (base published : Checkpoint)
    (generation bound : Nat) : Option Nat :=
  if erasure && decide (preparedSource = grant ∧ base = published) then
    next_writer_epoch generation bound
  else none

def erasure_floor (previous chosenCut : Nat) (closesHistory : Bool) : Nat :=
  if closesHistory then chosenCut else previous

def admits_history (floor start : Nat) : Bool := decide (floor ≤ start)

structure Authority (Owner : Type) where
  holder : Option Owner
  epoch : Nat
  generation : Nat

def abstract_grant {Owner : Type} (state : Authority Owner) : Option (Owner × Nat × Nat) :=
  state.holder.map (fun owner => (owner, state.epoch, state.generation))

def rotate {Owner : Type} (state : Authority Owner) : Authority Owner :=
  { state with epoch := state.epoch + 1, generation := state.generation + 1 }

def vacate {Owner : Type} (state : Authority Owner) : Authority Owner :=
  { state with holder := none }

inductive Step {Owner : Type} : Authority Owner → Authority Owner → Prop
  | rotate (state) : Step state (ErasureCommit.rotate state)
  | grant (state) (owner : Owner) :
      Step state { state with holder := some owner, epoch := state.epoch + 1 }
  | vacate (state) : Step state (ErasureCommit.vacate state)
  | stutter (state) : Step state state

inductive Trace {Owner : Type} : Authority Owner → Authority Owner → Prop
  | refl (state) : Trace state state
  | extend {first before after} : Trace first before → Step before after → Trace first after

theorem rotation_requires_exact_incumbent_and_head {Grant Cut Checkpoint : Type}
    [DecidableEq Grant] [DecidableEq Cut] [DecidableEq Checkpoint]
    {custodian : Bool} {current : Option Grant} {grant : Grant}
    {head cut : Cut} {published requested : Checkpoint}
    (accepted : rotation_head custodian current grant head cut published requested = true) :
    custodian = true ∧ current = some grant ∧ head = cut ∧ published ≠ requested := by
  simpa [rotation_head, Bool.and_eq_true] using accepted

theorem rotation_requires_exact_preparation {Cut Root Custody : Type}
    [DecidableEq Cut] [DecidableEq Root] [DecidableEq Custody]
    {preparedCut cut : Cut} {preparedRoot root : Root} {preparedCustody custody : Custody}
    {manifest : Bool} {observed : Option Cut}
    (accepted :
      exact_preparation preparedCut cut preparedRoot root preparedCustody custody manifest observed =
        true) :
    preparedCut = cut ∧ preparedRoot = root ∧ preparedCustody = custody ∧ observed = some cut := by
  exact (by simpa [exact_preparation, Bool.and_eq_true] using accepted :
    manifest = true ∧ _).2

theorem rotation_installs_successor_generation {Grant Checkpoint : Type}
    [DecidableEq Grant] [DecidableEq Checkpoint] {erasure : Bool} {source grant : Grant}
    {base published : Checkpoint} {generation bound next : Nat}
    (accepted : successor_generation erasure source grant base published generation bound = some next) :
    erasure = true ∧ source = grant ∧ base = published ∧ next = generation + 1 := by
  unfold successor_generation at accepted
  split at accepted <;> simp_all [next_writer_epoch]

theorem rotation_advances_epoch_and_generation {Owner : Type} (state : Authority Owner) :
    (rotate state).epoch = state.epoch + 1 ∧
      (rotate state).generation = state.generation + 1 ∧ (rotate state).holder = state.holder := by
  simp [rotate]

theorem generation_survives_vacancy {Owner : Type} (state : Authority Owner) :
    (vacate state).generation = state.generation ∧ (vacate state).epoch = state.epoch := by
  exact ⟨rfl, rfl⟩

theorem trace_keeps_generation_floor {Owner : Type} {first last : Authority Owner}
    (trace : Trace first last) : first.generation ≤ last.generation := by
  induction trace with
  | refl => exact Nat.le_refl _
  | extend _ step previous =>
    cases step <;> simp_all [rotate, vacate] <;> omega

theorem rotated_suffix_refuses_superseded_grant {Owner : Type} [DecidableEq Owner]
    {state later : Authority Owner} (owner : Owner) (trace : Trace (rotate state) later) :
    authorize_writer (some owner) (abstract_grant later) (owner, state.epoch, state.generation) =
      false := by
  have monotone := trace_keeps_generation_floor trace
  have higher : state.generation < later.generation := by
    simpa [rotate, Nat.succ_le_iff] using monotone
  have different : later.generation ≠ state.generation := by omega
  cases holder : later.holder <;> simp [authorize_writer, abstract_grant, holder, different]

theorem publication_closes_old_history {previous cut start : Nat} (older : start < cut) :
    admits_history (erasure_floor previous cut true) start = false := by
  exact decide_eq_false (Nat.not_le_of_lt older)

-- Concrete witness of an exact preparation, rotation, vacancy and regrant.
example :
    rotation_head true (some 3) 3 8 8 1 2 = true ∧
    exact_preparation 8 8 12 12 13 13 true (some 8) = true ∧
    successor_generation true 3 3 1 1 4 100 = some 5 ∧
    Trace (rotate (⟨some 3, 4, 4⟩ : Authority Nat)) ⟨some 5, 6, 5⟩ := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  exact .extend (.extend (.refl _) (.vacate _)) (.grant _ 5)

#print axioms every_selectable_recovery_avoids_the_revoked_generation
#print axioms rotation_requires_exact_incumbent_and_head
#print axioms rotation_requires_exact_preparation
#print axioms rotation_installs_successor_generation
#print axioms rotation_advances_epoch_and_generation
#print axioms generation_survives_vacancy
#print axioms trace_keeps_generation_floor
#print axioms rotated_suffix_refuses_superseded_grant
#print axioms publication_closes_old_history

end ErasureCommit
