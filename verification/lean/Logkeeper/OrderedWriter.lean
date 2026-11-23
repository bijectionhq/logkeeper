import Logkeeper.Kernel

set_option warningAsError true

namespace Logkeeper.Kernel.Ordered

def authorize_writer {Enrollment : Type} [DecidableEq Enrollment] (principal : Option Enrollment)
    (current : Option (Enrollment × Nat × Nat)) (presented : Enrollment × Nat × Nat) : Bool :=
  decide (principal = some presented.1 ∧ current = some presented)

def append_next_lsn (head expected limit : Nat) : Option Nat :=
  if head = expected ∧ expected < limit then some (expected + 1) else none

def next_writer_epoch (epoch limit : Nat) : Option Nat :=
  if epoch < limit then some (epoch + 1) else none

def withdraw_grant {Grant : Type} (grant : Option Grant) (holderMatches : Bool) : Option Grant :=
  if holderMatches then none else grant

theorem append_at_next_lsn {head expected limit next : Nat}
    (admitted : append_next_lsn head expected limit = some next) :
    expected = head ∧ next = head + 1 := by
  unfold append_next_lsn at admitted
  split at admitted <;> simp_all

/-- An ordered image and two pieces of trace evidence: the compacted prefix and,
during vacancy, the last installed writer. A fresh image uses epoch zero for
the vacant writer. The full writer identity includes the enrollment and key generation. -/
structure Image (Payload : Type) where
  writer : Writer
  active : Bool
  compacted : List (Entry Payload)
  records : List (Entry Payload)
  head : Nat

def abstract_authority (grant : Option Writer) (previous : Writer) : Authority :=
  match grant with
  | some current => .active current
  | none => .vacant previous

def abstract_history {Payload : Type} (compacted records : List (Entry Payload)) :
    List (Entry Payload) :=
  compacted ++ records

def abstract_state {Payload : Type} (image : Image Payload) : State Payload where
  authority := abstract_authority (if image.active then some image.writer else none) image.writer
  history := abstract_history image.compacted image.records

def WellFormed {Payload : Type} (image : Image Payload) : Prop :=
  image.head = (abstract_state image).history.length

def trimImage {Payload : Type} (image : Image Payload) (count : Nat) : Image Payload :=
  { image with compacted := image.compacted ++ image.records.take count,
               records := image.records.drop count }

theorem trim_keeps_the_logical_history {Payload : Type} (image : Image Payload) (count : Nat) :
    abstract_state (trimImage image count) = abstract_state image := by
  have same : (abstract_state (trimImage image count)).history = (abstract_state image).history := by
    simp [abstract_state, abstract_history, trimImage, List.append_assoc]
  exact congrArg (fun history => { abstract_state image with history }) same

/-- Project the writer and full logical history. Checkpoint and replay accounting
are outside this projection. The byte budgets of a concrete append are checked
by the reducer. Here the two abstract count limits can be the maximum LSN. -/
inductive ImageStep {Payload : Type} (limits : Limits) : Image Payload → Image Payload → Prop
  | append {image expected next} (request : Writer) (payload : Payload)
      (active : image.active = true) (exactGrant : image.writer = request)
      (advance : append_next_lsn image.head expected (min limits.recovery limits.retained) = some next) :
      ImageStep limits image
        { image with records := image.records ++ [⟨request.epoch, payload⟩], head := next }
  | fence {image} (successor : Writer) (samePlacement : successor.placement = image.writer.placement)
      (higher : image.writer.epoch < successor.epoch) :
      ImageStep limits image { image with writer := successor, active := true }
  | withdraw {image} (active : image.active = true) :
      ImageStep limits image { image with active := false }
  | trim {image} (count : Nat) :
      ImageStep limits image (trimImage image count)
  | stutter (image : Image Payload) : ImageStep limits image image

theorem image_step_refines_kernel {Payload : Type} {limits : Limits}
    {before after : Image Payload} (valid : WellFormed before) (step : ImageStep limits before after) :
    WellFormed after ∧
      (abstract_state after = abstract_state before ∨
        Step limits (abstract_state before) (abstract_state after)) := by
  cases step with
  | append request payload active exactGrant advance =>
      obtain ⟨rfl, nextEq⟩ := append_at_next_lsn advance
      have room : before.head < min limits.recovery limits.retained := by
        by_cases inside : before.head < min limits.recovery limits.retained
        · exact inside
        · simp [append_next_lsn, inside] at advance
      have roomRecovery := Nat.lt_of_lt_of_le room (Nat.min_le_left _ _)
      have roomRetained := Nat.lt_of_lt_of_le room (Nat.min_le_right _ _)
      have historyEq : (abstract_state before).history.length = before.head := valid.symm
      refine ⟨?_, Or.inr ?_⟩
      · simp only [WellFormed, abstract_state, abstract_history, nextEq,
          List.length_append, List.length_singleton]
        have count : before.head = before.compacted.length + before.records.length := by
          simpa only [abstract_state, abstract_history, List.length_append] using historyEq.symm
        omega
      · have appended := Step.append (limits := limits) (state := abstract_state before)
          (writer := request) before.head payload
          ⟨by simp [abstract_state, abstract_authority, active, exactGrant], valid,
            by change (abstract_state before).history.length + 1 - 0 ≤ limits.recovery
               rw [historyEq]
               omega,
            by change (abstract_state before).history.length + 1 - 0 ≤ limits.retained
               rw [historyEq]
               omega⟩
        simpa [abstract_state, abstract_history, List.append_assoc] using appended
  | fence successor samePlacement higher =>
      refine ⟨valid, Or.inr ?_⟩
      have atWriter : AtWriter (abstract_state before).authority before.writer := by
        cases active : before.active <;> simp [abstract_state, abstract_authority, AtWriter, active]
      exact Step.fenceWriter successor atWriter samePlacement higher
  | withdraw active =>
      refine ⟨valid, Or.inr ?_⟩
      exact Step.withdrawWriter (writer := before.writer)
        (by simp [abstract_state, abstract_authority, active])
  | trim count =>
      have same := trim_keeps_the_logical_history before count
      have headSame : (trimImage before count).head = before.head := rfl
      exact ⟨by simpa only [WellFormed, same, headSame] using valid, Or.inl same⟩
  | stutter => exact ⟨valid, Or.inl rfl⟩

inductive ImageTrace {Payload : Type} (limits : Limits) : Image Payload → Image Payload → Prop
  | same (image : Image Payload) : ImageTrace limits image image
  | step {first before after} : ImageTrace limits first before → ImageStep limits before after →
      ImageTrace limits first after

theorem image_trace_refines_kernel {Payload : Type} {limits : Limits}
    {first last : Image Payload} (valid : WellFormed first) (trace : ImageTrace limits first last) :
    WellFormed last ∧ Trace limits (abstract_state first) (abstract_state last) := by
  induction trace with
  | same => exact ⟨valid, .same _⟩
  | step _ step prior =>
      obtain ⟨afterValid, same | changes⟩ := image_step_refines_kernel prior.1 step
      · exact ⟨afterValid, same ▸ prior.2⟩
      · exact ⟨afterValid, .next prior.2 changes⟩

theorem history_is_irrevocable {Payload : Type} {limits : Limits}
    {first last : Image Payload} (valid : WellFormed first) (trace : ImageTrace limits first last)
    {lsn : Nat} (committed : lsn < (abstract_state first).history.length) :
    (abstract_state last).history[lsn]? = (abstract_state first).history[lsn]? := by
  obtain ⟨suffix, extendsHistory⟩ := trace_extends_history (image_trace_refines_kernel valid trace).2
  rw [extendsHistory, List.getElem?_append_left committed]

def Superseded {Payload : Type} (image : Image Payload) (writer : Writer) : Prop :=
  writer.epoch < image.writer.epoch ∨ (writer.epoch = image.writer.epoch ∧ image.active = false)

theorem superseded_stays_superseded {Payload : Type} {limits : Limits}
    {first last : Image Payload} {writer : Writer} (superseded : Superseded first writer)
    (trace : ImageTrace limits first last) : Superseded last writer := by
  induction trace with
  | same => exact superseded
  | step _ step prior =>
      cases step with
      | fence _ _ higher =>
          exact Or.inl (Nat.lt_of_le_of_lt (prior.elim Nat.le_of_lt (fun same => Nat.le_of_eq same.1))
            higher)
      | withdraw _ =>
          exact prior.elim Or.inl (fun same => Or.inr ⟨same.1, rfl⟩)
      | _ => exact prior

theorem superseded_grant_refused {Payload : Type} {image : Image Payload} {writer : Writer}
    (superseded : Superseded image writer) : (abstract_state image).authority ≠ .active writer := by
  rcases superseded with older | ⟨_, vacant⟩
  · cases active : image.active
    · simp [abstract_state, abstract_authority, active]
    · simp only [abstract_state, abstract_authority, active, ite_true]
      intro same
      exact (Nat.ne_of_lt older) (congrArg Writer.epoch (Authority.active.inj same)).symm
  · simp [abstract_state, abstract_authority, vacant]

theorem superseded_writer_cannot_append_again {Payload : Type} {limits : Limits}
    {first last : Image Payload} {writer : Writer} {lsn : Nat}
    (superseded : Superseded first writer) (trace : ImageTrace limits first last) :
    ¬ AppendAdmissible limits (abstract_state last) writer lsn :=
  stale_writer_refused (superseded_grant_refused (superseded_stays_superseded superseded trace))

/-- A reachable append, vacancy, suffix trim and successor fence. -/
example (placement : Placement) (payload : Unit) :
    ∃ first last : Image Unit, ImageTrace ⟨3, 3⟩ first last ∧
      WellFormed first ∧ Superseded last first.writer ∧ last.head = 1 ∧ last.records = [] := by
  let old : Writer := ⟨placement, 1, 1⟩
  let new : Writer := ⟨placement, 2, 1⟩
  let first : Image Unit := ⟨old, true, [], [], 0⟩
  let appended : Image Unit := { first with records := [⟨1, payload⟩], head := 1 }
  let vacant : Image Unit := { appended with active := false }
  let trimmed : Image Unit := { vacant with compacted := [⟨1, payload⟩], records := [] }
  let last : Image Unit := { trimmed with writer := new, active := true }
  have app : ImageStep ⟨3, 3⟩ first appended := .append (expected := 0) old payload rfl rfl rfl
  have withdraw : ImageStep ⟨3, 3⟩ appended vacant := .withdraw rfl
  have trim : ImageStep ⟨3, 3⟩ vacant trimmed := .trim 1
  have fence : ImageStep ⟨3, 3⟩ trimmed last := .fence new rfl (show 1 < 2 from by decide)
  exact ⟨first, last, .step (.step (.step (.step (.same first) app) withdraw) trim) fence,
    rfl, Or.inl (show 1 < 2 from by decide), rfl, rfl⟩

#print axioms append_at_next_lsn
#print axioms trim_keeps_the_logical_history
#print axioms image_step_refines_kernel
#print axioms image_trace_refines_kernel
#print axioms history_is_irrevocable
#print axioms superseded_stays_superseded
#print axioms superseded_grant_refused
#print axioms superseded_writer_cannot_append_again

end Logkeeper.Kernel.Ordered
