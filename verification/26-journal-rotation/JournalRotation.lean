import JournalRefinement

set_option warningAsError true

namespace JournalRotation

inductive Extent where
  | base (generation : Nat)
  | tail (position : Nat)
  deriving DecidableEq

structure View where
  generation : Nat
  cut : Nat
  deriving DecidableEq

abbrev Contents (Record : Type) := Extent → Option (List Record)

structure State (Record : Type) where
  history : List Record
  media : Contents Record
  pins : Contents Record
  stable : View
  visible : View
  namespaceChoices : View → Prop
  issued : Nat
  running : Bool

def Exact (state : State Record) (view : View) : Prop :=
  view.cut ≤ state.history.length ∧
  state.media (.base view.generation) = some (state.history.take view.cut) ∧
  ∀ position record, view.cut ≤ position → state.history[position]? = some record →
    state.media (.tail position) = some [record]

def Needed (view : View) : Extent → Prop
  | .base generation => generation = view.generation
  | .tail position => view.cut ≤ position

def Reclaimable (state : State Record) (extent : Extent) : Prop :=
  ¬ Needed state.stable extent ∧ ¬ Needed state.visible extent ∧ state.pins extent = none

def update (contents : Contents Record) (target : Extent) (value : Option (List Record)) :
    Contents Record :=
  fun extent => if extent = target then value else contents extent

def appendRecord (state : State Record) (record : Record) : State Record :=
  { state with
      history := state.history ++ [record]
      media := update state.media (.tail state.history.length) (some [record]) }

def stageBase (state : State Record) (generation cut : Nat) : State Record :=
  { state with
      issued := generation
      media := update state.media (.base generation) (some (state.history.take cut)) }

def initial : State Record :=
  ⟨[], update (fun _ => none) (.base 0) (some []), fun _ => none,
    ⟨0, 0⟩, ⟨0, 0⟩, (· = ⟨0, 0⟩), 0, true⟩

def Selectable (state : State Record) (view : View) : Prop :=
  view = state.stable ∨ view = state.visible

def TracksNamespace (state : State Record) : Prop :=
  ∀ view, state.namespaceChoices view ↔ Selectable state view

def CanPublish (state : State Record) : Prop :=
  state.stable = state.visible

structure Safe (state : State Record) : Prop where
  stableExact : Exact state state.stable
  visibleExact : Exact state state.visible
  pinsExact : ∀ extent contents, state.pins extent = some contents → state.media extent = some contents

inductive Step : State Record → State Record → Prop
  | append {state} (record : Record) (vacant : state.media (.tail state.history.length) = none) :
      Step state (appendRecord state record)
  | stage {state} (generation cut : Nat) (fresh : state.issued < generation)
      (vacant : state.media (.base generation) = none) :
      Step state (stageBase state generation cut)
  | publish {state} (candidate : View) (settled : CanPublish state)
      (later : state.visible.generation < candidate.generation)
      (complete : Exact state candidate) :
      Step state
        {state with visible := candidate, namespaceChoices := fun view =>
          state.namespaceChoices view ∨ view = candidate}
  | syncSelector (state : State Record) :
      Step state {state with stable := state.visible, namespaceChoices := (· = state.visible)}
  | warmRestart (state : State Record) : Step state {state with running := false}
  | powerLoss {state} (outcome : View) (survives : state.namespaceChoices outcome) :
      Step state
        { state with
            stable := outcome
            visible := outcome
            running := false
            namespaceChoices := (· = outcome) }
  | openJournal {state} (verified : Exact state state.visible) :
      Step state {state with running := true}
  | pin {state} (extent : Extent) (contents : List Record)
      (readable : state.media extent = some contents) :
      Step state {state with pins := update state.pins extent (some contents)}
  | finish (state : State Record) (extent : Extent) :
      Step state {state with pins := update state.pins extent none}
  | reclaim {state} (extent : Extent) (allowed : Reclaimable state extent) :
      Step state {state with media := update state.media extent none}

inductive Trace : State Record → State Record → Prop
  | same (state : State Record) : Trace state state
  | next {first before after : State Record} : Trace first before → Step before after → Trace first after

theorem initial_safe : Safe (initial : State Record) := by
  constructor
  · simp [Exact, initial, update]
  · simp [Exact, initial, update]
  · simp [initial]

theorem initial_tracks_namespace : TracksNamespace (initial : State Record) := by
  simp [TracksNamespace, Selectable, initial]

theorem step_tracks_all_crash_choices {before after : State Record}
    (tracked : TracksNamespace before) (step : Step before after) : TracksNamespace after := by
  cases step with
  | publish candidate allowed _ _ =>
      have settled : before.stable = before.visible := by
        exact allowed
      intro view
      change before.namespaceChoices view ∨ view = candidate ↔
        view = before.stable ∨ view = candidate
      rw [tracked view]
      simp [Selectable, settled]
  | syncSelector | powerLoss =>
      intro view
      simp [Selectable]
  | _ => exact tracked

theorem selectable_has_exact_cut {state : State Record} (safe : Safe state)
    {view : View} (selectable : Selectable state view) : Exact state view := by
  rcases selectable with rfl | rfl
  · exact safe.stableExact
  · exact safe.visibleExact

theorem forward_exact_base_can_replace_view {state : State Record} {previous candidate : View}
    (live : Exact state previous) (forward : previous.cut ≤ candidate.cut)
    (within : candidate.cut ≤ state.history.length)
    (image : state.media (.base candidate.generation) = some (state.history.take candidate.cut)) :
    Exact state candidate := by
  refine ⟨within, image, ?_⟩
  intro position record retained known
  exact live.2.2 position record (Nat.le_trans forward retained) known

private theorem store_preserves {media : Contents Record} {changed extent : Extent}
    {old new : List Record} (vacant : media changed = none)
    (stored : media extent = some old) :
    update media changed (some new) extent = some old := by
  by_cases same : extent = changed
  · subst extent
    rw [vacant] at stored
    cases stored
  · simp [update, same, stored]

private theorem append_preserves_exact {state : State Record} {view : View} (record : Record)
    (exactBefore : Exact state view) : Exact (appendRecord state record) view := by
  obtain ⟨within, base, tail⟩ := exactBefore
  refine ⟨by simp [appendRecord]; omega, ?_, ?_⟩
  · simpa [appendRecord, update, List.take_append_of_le_length within] using base
  · intro position value retained known
    change (state.history ++ [record])[position]? = some value at known
    change update state.media (.tail state.history.length) (some [record]) (.tail position) = some [value]
    by_cases earlier : position < state.history.length
    · rw [List.getElem?_append_left earlier] at known
      have different : position ≠ state.history.length := by omega
      simpa [update, different] using tail position value retained known
    · have inRange := (List.getElem?_eq_some_iff.mp known).1
      simp only [List.length_append, List.length_singleton] at inRange
      have last : position = state.history.length := by omega
      subst position
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at known
      have same : record = value := Option.some.inj known
      simp [update, same]

private theorem stage_preserves_exact {state : State Record} {view : View} (generation cut : Nat)
    (vacant : state.media (.base generation) = none)
    (exactBefore : Exact state view) : Exact (stageBase state generation cut) view :=
  ⟨exactBefore.1, store_preserves vacant exactBefore.2.1,
   fun position record retained known =>
     store_preserves (new := state.history.take cut) vacant
       (exactBefore.2.2 position record retained known)⟩

theorem protected_extent_is_not_reclaimable {state : State Record} {extent : Extent}
    (allowed : Reclaimable state extent) :
    ¬ Needed state.stable extent ∧ ¬ Needed state.visible extent ∧ state.pins extent = none := by
  exact allowed

private theorem erase_preserves_exact {state : State Record} {view : View} {extent : Extent}
    (exactBefore : Exact state view) (unneeded : ¬ Needed view extent) :
    Exact {state with media := update state.media extent none} view := by
  refine ⟨exactBefore.1, ?_, ?_⟩
  · change update state.media extent none (.base view.generation) = _
    have different : .base view.generation ≠ extent := by
      intro same
      subst extent
      exact unneeded rfl
    simpa [update, different] using exactBefore.2.1
  · intro position record retained known
    change update state.media extent none (.tail position) = _
    have different : .tail position ≠ extent := by
      intro same
      subst extent
      exact unneeded retained
    simpa [update, different] using exactBefore.2.2 position record retained known

theorem step_preserves_safety {before after : State Record} (safe : Safe before)
    (tracked : TracksNamespace before) (step : Step before after) : Safe after := by
  cases step with
  | append record vacant =>
      exact ⟨append_preserves_exact record safe.stableExact, append_preserves_exact record safe.visibleExact,
        fun extent contents pin => store_preserves vacant (safe.pinsExact extent contents pin)⟩
  | stage generation cut _ vacant =>
      exact ⟨stage_preserves_exact generation cut vacant safe.stableExact,
        stage_preserves_exact generation cut vacant safe.visibleExact,
        fun extent contents pin => store_preserves vacant (safe.pinsExact extent contents pin)⟩
  | publish _ _ _ complete =>
      exact ⟨safe.stableExact, complete, safe.pinsExact⟩
  | syncSelector =>
      exact ⟨safe.visibleExact, safe.visibleExact, safe.pinsExact⟩
  | warmRestart | openJournal _ =>
      exact ⟨safe.stableExact, safe.visibleExact, safe.pinsExact⟩
  | powerLoss outcome survives =>
      have complete := selectable_has_exact_cut safe ((tracked outcome).mp survives)
      exact ⟨complete, complete, safe.pinsExact⟩
  | pin extent contents readable =>
      refine ⟨safe.stableExact, safe.visibleExact, ?_⟩
      intro other held pin
      by_cases same : other = extent
      · subst other
        simp [update] at pin
        simpa [pin] using readable
      · exact safe.pinsExact other held (by simpa [update, same] using pin)
  | finish extent =>
      refine ⟨safe.stableExact, safe.visibleExact, ?_⟩
      intro other held pin
      by_cases same : other = extent
      · simp [update, same] at pin
      · exact safe.pinsExact other held (by simpa [update, same] using pin)
  | reclaim extent allowed =>
      obtain ⟨outsideStable, outsideVisible, unpinned⟩ := protected_extent_is_not_reclaimable allowed
      refine ⟨erase_preserves_exact safe.stableExact outsideStable,
        erase_preserves_exact safe.visibleExact outsideVisible, ?_⟩
      intro other held pin
      by_cases same : other = extent
      · subst other
        change before.pins extent = some held at pin
        rw [unpinned] at pin
        cases pin
      · simpa [update, same] using safe.pinsExact other held pin

theorem every_trace_preserves_safety {first last : State Record} (safe : Safe first)
    (tracked : TracksNamespace first) (trace : Trace first last) : Safe last ∧ TracksNamespace last := by
  induction trace with
  | same => exact ⟨safe, tracked⟩
  | next _ step prior =>
      exact ⟨step_preserves_safety prior.1 prior.2 step, step_tracks_all_crash_choices prior.2 step⟩

private theorem step_extends_history {before after : State Record} (step : Step before after) :
    ∃ added, after.history = before.history ++ added := by
  cases step with
  | append record _ => exact ⟨[record], rfl⟩
  | _ => exact ⟨[], by simp [stageBase]⟩

theorem trace_extends_history {before after : State Record} (trace : Trace before after) :
    ∃ added, after.history = before.history ++ added := by
  induction trace with
  | same => exact ⟨[], by simp⟩
  | next _ step prior =>
      obtain ⟨earlier, accumulated⟩ := prior
      obtain ⟨later, extended⟩ := step_extends_history step
      exact ⟨earlier ++ later, by rw [extended, accumulated, List.append_assoc]⟩

theorem recovery_paths_cover_the_same_history {state : State Record} (safe : Safe state)
    (tracked : TracksNamespace state) {view : View} (survives : state.namespaceChoices view) :
    ∃ base tail,
      state.media (.base view.generation) = some base ∧ base ++ tail = state.history ∧
      ∀ offset record, tail[offset]? = some record →
        state.media (.tail (view.cut + offset)) = some [record] := by
  obtain ⟨_, image, suffix⟩ := selectable_has_exact_cut safe ((tracked view).mp survives)
  refine ⟨state.history.take view.cut, state.history.drop view.cut, image,
    List.take_append_drop _ _, ?_⟩
  intro offset record found
  rw [List.getElem?_drop] at found
  exact suffix (view.cut + offset) record (Nat.le_add_right _ _) found

theorem warm_reopen_keeps_predecessor_selectable {state : State Record} (safe : Safe state) :
    let restarted := {state with running := false}
    let reopened := {restarted with running := true}
    Trace state reopened ∧ Selectable reopened state.stable ∧ Exact reopened state.stable := by
  exact ⟨.next (.next (.same _) (.warmRestart _)) (.openJournal safe.visibleExact),
    Or.inl rfl, safe.stableExact⟩

theorem two_root_bound {state : State Record} {first second third : View}
    (tracked : TracksNamespace state) (firstPossible : state.namespaceChoices first)
    (secondPossible : state.namespaceChoices second) (thirdPossible : state.namespaceChoices third) :
    first = second ∨ first = third ∨ second = third := by
  have firstAllowed := (tracked first).mp firstPossible
  have secondAllowed := (tracked second).mp secondPossible
  have thirdAllowed := (tracked third).mp thirdPossible
  rcases firstAllowed with rfl | rfl <;> rcases secondAllowed with rfl | rfl <;>
    rcases thirdAllowed with rfl | rfl <;> first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)

def Reads (state : State Record) (view : View) (position : Nat) (record : Record) : Prop :=
  (∃ base, state.media (.base view.generation) = some base ∧ base[position]? = some record) ∨
  state.media (.tail position) = some [record]

theorem exact_view_reads_acknowledged_record {state : State Record} {view : View}
    (exactView : Exact state view) {position : Nat} {record : Record}
    (known : state.history[position]? = some record) :
    Reads state view position record := by
  by_cases covered : position < view.cut
  · refine Or.inl ⟨state.history.take view.cut, exactView.2.1, ?_⟩
    simpa [List.getElem?_take, covered] using known
  · exact Or.inr (exactView.2.2 position record (Nat.le_of_not_lt covered) known)

theorem current_quorum_reads_exact_records_after_rotations
    {journal : JournalRefinement.Journal Replica Payload}
    (cut : JournalRefinement.CompleteCut journal) (available : Replica → Bool)
    (recovery : JournalRefinement.Majority journal.members available)
    (before recovered : Replica → State (Kernel.Entry Payload)) (selected : Replica → View)
    (trace : ∀ replica ∈ journal.members, available replica = true →
      Trace (before replica) (recovered replica))
    (startsSound : ∀ replica ∈ journal.members, available replica = true →
      Safe (before replica) ∧ TracksNamespace (before replica))
    (surviving : ∀ replica ∈ journal.members, available replica = true →
      (recovered replica).namespaceChoices (selected replica))
    (copyRefines : ∀ replica ∈ journal.members, ∀ position entry, available replica = true →
      journal.copies replica position entry → (before replica).history[position]? = some entry)
    {position : Nat} {entry : Kernel.Entry Payload}
    (retained : journal.logical.firstRetained ≤ position)
    (committed : journal.logical.history[position]? = some entry) :
    ∃ replica ∈ journal.members, available replica = true ∧
      Reads (recovered replica) (selected replica) position entry := by
  obtain ⟨replica, member, online, copy⟩ :=
    JournalRefinement.any_recovery_quorum_can_read_exact_entry cut available recovery retained committed
  obtain ⟨safe, tracked⟩ := startsSound replica member online
  have rotations := trace replica member online
  obtain ⟨safeLater, trackedLater⟩ :=
    every_trace_preserves_safety safe tracked rotations
  have allowed := (trackedLater (selected replica)).mp (surviving replica member online)
  have original : (before replica).history[position]? = some entry := by
    exact copyRefines replica member position entry online copy
  obtain ⟨_, extended⟩ := trace_extends_history rotations
  have known : (recovered replica).history[position]? = some entry := by
    rw [extended, List.getElem?_append_left (List.getElem?_eq_some_iff.mp original).1]
    exact original
  exact ⟨replica, member, online,
    exact_view_reads_acknowledged_record (selectable_has_exact_cut safeLater allowed) known⟩

#print axioms initial_safe
#print axioms initial_tracks_namespace
#print axioms step_tracks_all_crash_choices
#print axioms selectable_has_exact_cut
#print axioms forward_exact_base_can_replace_view
#print axioms protected_extent_is_not_reclaimable
#print axioms step_preserves_safety
#print axioms every_trace_preserves_safety
#print axioms trace_extends_history
#print axioms recovery_paths_cover_the_same_history
#print axioms warm_reopen_keeps_predecessor_selectable
#print axioms two_root_bound
#print axioms exact_view_reads_acknowledged_record
#print axioms current_quorum_reads_exact_records_after_rotations

end JournalRotation
