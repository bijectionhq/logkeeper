set_option warningAsError true

namespace FeedComposition

variable {Event : Type}

def slice (history : List Event) (first stop : Nat) : List Event :=
  (history.take stop).drop first

theorem adjacent_windows_join (history : List Event) {first seam stop : Nat}
    (starts : first ≤ seam) (ends : seam ≤ stop) :
    slice history first seam ++ slice history seam stop = slice history first stop := by
  let window := slice history first stop
  have leftWindow : window.take (seam - first) = slice history first seam := by
    unfold window slice
    rw [List.take_drop, Nat.add_sub_of_le starts, List.take_take, Nat.min_eq_left ends]
  have suffix : window.drop (seam - first) = slice history seam stop := by
    unfold window slice
    rw [List.drop_drop, Nat.add_sub_of_le starts]
  rw [← leftWindow, ← suffix, List.take_append_drop]

theorem archived_window_is_exact {history archive : List Event} {archiveEnd first stop : Nat}
    (covered : archive = history.take archiveEnd) (ends : stop ≤ archiveEnd) :
    slice archive first stop = slice history first stop := by
  rw [covered, slice, slice, List.take_take, Nat.min_eq_left ends]

theorem retained_window_is_exact {history journal : List Event} {floor first stop : Nat}
    (retained : journal = history.drop floor)
    (admitted : floor ≤ first) (ends : first ≤ stop) :
    slice journal (first - floor) (stop - floor) = slice history first stop := by
  have endOffset : floor + (stop - floor) = stop := Nat.add_sub_of_le (Nat.le_trans admitted ends)
  have startOffset : floor + (first - floor) = first := Nat.add_sub_of_le admitted
  rw [retained, slice, List.take_drop, endOffset, List.drop_drop, startOffset, slice]

theorem archive_and_tail_recover_exact_events {history archive journal : List Event}
    {archiveEnd floor first seam stop : Nat}
    (covered : archive = history.take archiveEnd) (retained : journal = history.drop floor)
    (starts : first ≤ seam) (ends : seam ≤ stop)
    (archiveCoversSeam : seam ≤ archiveEnd) (admitted : floor ≤ seam) :
    slice archive first seam ++ slice journal (seam - floor) (stop - floor) =
      slice history first stop := by
  have activeFloor : floor ≤ seam := admitted
  rw [archived_window_is_exact covered archiveCoversSeam,
    retained_window_is_exact retained activeFloor ends, adjacent_windows_join _ starts ends]

def readWindow (archive journal : List Event) (floor first seam stop : Nat) : List Event :=
  (if first = seam then [] else slice archive first seam) ++
  (if seam = stop then [] else slice journal (seam - floor) (stop - floor))

theorem empty_window (history : List Event) (position : Nat) :
    slice history position position = [] := by
  unfold slice
  apply List.drop_eq_nil_of_le
  rw [List.length_take]
  exact Nat.min_le_left _ _

theorem exact_window_can_replan_at_current_floor {history archive journal : List Event}
    {archiveEnd floor first stop : Nat} (covered : archive = history.take archiveEnd)
    (retained : journal = history.drop floor) (archivedFloor : floor ≤ archiveEnd)
    (withinCut : first ≤ stop) :
    ∃ seam, first ≤ seam ∧ seam ≤ stop ∧ (first = seam ∨ seam ≤ archiveEnd) ∧
      (seam = stop ∨ floor ≤ seam) ∧ readWindow archive journal floor first seam stop =
        slice history first stop := by
  let seam := max first (min archiveEnd stop)
  have starts : first ≤ seam := by omega
  have ends : seam ≤ stop := by omega
  have archiveGuard : first = seam ∨ seam ≤ archiveEnd := by omega
  have journalGuard : seam = stop ∨ floor ≤ seam := by omega
  refine ⟨seam, starts, ends, archiveGuard, journalGuard, ?_⟩
  have prefixExact : (if first = seam then [] else slice archive first seam) =
      slice history first seam := by
    by_cases empty : first = seam
    · simp [empty, empty_window]
    · simp only [empty, ite_false]
      exact archived_window_is_exact covered (archiveGuard.resolve_left empty)
  have suffixExact : (if seam = stop then [] else slice journal (seam - floor) (stop - floor)) =
      slice history seam stop := by
    by_cases empty : seam = stop
    · simp [empty, empty_window]
    · simp only [empty, ite_false]
      exact retained_window_is_exact retained (journalGuard.resolve_left empty) ends
  rw [readWindow, prefixExact, suffixExact, adjacent_windows_join _ starts ends]

theorem later_appends_preserve_closed_window (history additional : List Event)
    {first stop : Nat} (captured : stop ≤ history.length) :
    slice (history ++ additional) first stop = slice history first stop := by
  unfold slice
  rw [List.take_append_of_le_length captured]

theorem final_state_and_count_can_lose_event_order :
    ¬ ∃ recover : Nat → Nat → List Nat,
      ∀ events : List Nat, recover (events.foldl (· + ·) 0) events.length = events := by
  rintro ⟨recover, reconstruct⟩
  have earlier : recover 3 2 = [1, 2] := reconstruct [1, 2]
  have later : recover 3 2 = [2, 1] := reconstruct [2, 1]
  exact (show ([1, 2] : List Nat) ≠ [2, 1] by decide) (earlier.symm.trans later)

theorem uncovered_archive_tail_lower_bounds_retained_debt
    {head floor archiveEnd : Nat} (covered : floor ≤ archiveEnd) :
    head - archiveEnd ≤ head - floor := by
  omega

theorem stalled_archive_imposes_finite_admission_ceiling
    {head floor archiveEnd capacity : Nat} (covered : floor ≤ archiveEnd)
    (boundedDebt : head - floor ≤ capacity) :
    head ≤ archiveEnd + capacity := by
  have uncovered : head - archiveEnd ≤ head - floor :=
    uncovered_archive_tail_lower_bounds_retained_debt covered
  omega

#print axioms adjacent_windows_join
#print axioms archived_window_is_exact
#print axioms retained_window_is_exact
#print axioms archive_and_tail_recover_exact_events
#print axioms empty_window
#print axioms exact_window_can_replan_at_current_floor
#print axioms later_appends_preserve_closed_window
#print axioms final_state_and_count_can_lose_event_order
#print axioms uncovered_archive_tail_lower_bounds_retained_debt
#print axioms stalled_archive_imposes_finite_admission_ceiling

end FeedComposition
