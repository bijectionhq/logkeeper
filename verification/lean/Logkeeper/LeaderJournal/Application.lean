import Logkeeper.LeaderJournal.Consensus

namespace Logkeeper.LeaderJournal

set_option warningAsError true

structure Fence where
  epoch : Nat
  writer : Nat
  deriving DecidableEq, Repr

/-- The service binds the writer identity and authorizes administrative requests. -/
inductive Request (Payload : Type) where
  | seal (expectedEpoch writer : Nat)
  | append (fence : Fence) (atLsn : Nat) (payload : Payload)
  | trim (fence : Fence) (through : Nat)
  | delete
  deriving DecidableEq, Repr

inductive Reply where
  | sealed (fence : Fence) (head : Nat)
  | appended (lsn : Nat)
  | trimmed (floor : Nat)
  | deleted
  | fenced (epoch : Nat)
  | conflict (head : Nat)
  | belowFloor (floor : Nat)
  deriving DecidableEq, Repr

structure Journal (Payload : Type) where
  fence : Option Fence
  /-- Logical history for the proof. The physical view keeps only the retained suffix. -/
  history : List Payload
  floor : Nat
  deleted : Bool
  deriving DecidableEq, Repr

def Journal.empty : Journal Payload := ⟨none, [], 1, false⟩

def Journal.epoch (s : Journal Payload) : Nat := (s.fence.map Fence.epoch).getD 0

def Journal.head (s : Journal Payload) : Nat := s.history.length

def Journal.record (s : Journal Payload) (lsn : Nat) : Option Payload :=
  if lsn = 0 then none else s.history[lsn - 1]?

def Journal.retain (s : Journal Payload) : List Payload :=
  if s.deleted then [] else s.history.drop (s.floor - 1)

private def decideSeal (s : Journal Payload) (expectedEpoch writer : Nat) : Journal Payload × Reply :=
  let fence := ⟨expectedEpoch + 1, writer⟩
  if s.epoch = expectedEpoch then
    ({ s with fence := some fence }, .sealed fence s.head)
  else if s.fence = some fence then
    (s, .sealed fence s.head)
  else (s, .fenced s.epoch)

private def decideAppend [DecidableEq Payload] (s : Journal Payload) (fence : Fence)
    (atLsn : Nat) (payload : Payload) : Journal Payload × Reply :=
  if s.fence ≠ some fence then (s, .fenced s.epoch)
  else if atLsn < s.floor then (s, .belowFloor s.floor)
  else if atLsn ≤ s.head then
    if s.record atLsn = some payload then (s, .appended atLsn)
    else (s, .conflict s.head)
  else if atLsn = s.head + 1 then
    ({ s with history := s.history ++ [payload] }, .appended atLsn)
  else (s, .conflict s.head)

private def decideTrim (s : Journal Payload) (fence : Fence)
    (through : Nat) : Journal Payload × Reply :=
  if s.fence ≠ some fence then (s, .fenced s.epoch)
  else if s.head < through then (s, .conflict s.head)
  else
    let floor := max s.floor (through + 1)
    ({ s with floor }, .trimmed floor)

def execute [DecidableEq Payload] (s : Journal Payload) (request : Request Payload) :
    Journal Payload × Reply :=
  if s.deleted then (s, .deleted)
  else
    match request with
    | .seal expectedEpoch writer => decideSeal s expectedEpoch writer
    | .append fence atLsn payload => decideAppend s fence atLsn payload
    | .trim fence through => decideTrim s fence through
    | .delete => ({ s with deleted := true }, .deleted)

def applyEntry [DecidableEq Payload] (s : Journal Payload) (entry : Entry (Request Payload)) :
    Journal Payload :=
  match entry.command with
  | .apply request => (execute s request).1
  | _ => s

def replay [DecidableEq Payload] (log : Log (Request Payload)) : Journal Payload :=
  log.foldl applyEntry Journal.empty

structure Progress (before after : Journal Payload) : Prop where
  history : before.history <+: after.history
  floor : before.floor ≤ after.floor
  epoch : before.epoch ≤ after.epoch
  deleted : before.deleted = true → after.deleted = true

theorem Progress.refl (s : Journal Payload) : Progress s s :=
  ⟨List.prefix_rfl, Nat.le_refl _, Nat.le_refl _, id⟩

theorem Progress.trans {a b c : Journal Payload} (ab : Progress a b) (bc : Progress b c) :
    Progress a c :=
  ⟨ab.history.trans bc.history, Nat.le_trans ab.floor bc.floor,
    Nat.le_trans ab.epoch bc.epoch, fun deleted => bc.deleted (ab.deleted deleted)⟩

def Journal.Valid (s : Journal Payload) : Prop := 0 < s.floor ∧ s.floor ≤ s.head + 1

private theorem installation_progress (s : Journal Payload) (epoch writer : Nat)
    (same : s.epoch = epoch) :
    Progress s { s with fence := some ⟨epoch + 1, writer⟩ } ∧
      ({ s with fence := some ⟨epoch + 1, writer⟩ } : Journal Payload).Valid = s.Valid := by
  refine ⟨⟨List.prefix_rfl, Nat.le_refl _, ?_, id⟩, rfl⟩
  change s.epoch ≤ epoch + 1
  omega

theorem execute_preserves [DecidableEq Payload] (s : Journal Payload) (request : Request Payload)
    (valid : s.Valid) : Progress s (execute s request).1 ∧ (execute s request).1.Valid := by
  by_cases deleted : s.deleted = true
  · simpa only [execute, ite_eq_left deleted] using And.intro (Progress.refl s) valid
  · cases request with
    | «seal» epoch writer =>
        simp only [execute, ite_eq_right deleted]
        unfold decideSeal
        dsimp only
        split
        · rename_i same
          obtain ⟨progress, bounds⟩ := installation_progress s epoch writer same
          exact ⟨progress, bounds.symm ▸ valid⟩
        · split <;> exact ⟨Progress.refl s, valid⟩
    | append fence atLsn payload =>
        simp only [execute, ite_eq_right deleted]
        unfold decideAppend
        split
        · exact ⟨Progress.refl s, valid⟩
        · split
          · exact ⟨Progress.refl s, valid⟩
          · split
            · split <;> exact ⟨Progress.refl s, valid⟩
            · split
              · refine ⟨⟨List.prefix_append _ _, Nat.le_refl _, Nat.le_refl _, id⟩, valid.1, ?_⟩
                have bounds := valid.2
                simp only [Journal.head, List.length_append, List.length_singleton] at bounds ⊢
                omega
              · exact ⟨Progress.refl s, valid⟩
    | trim fence through =>
        simp only [execute, ite_eq_right deleted]
        unfold decideTrim
        split
        · exact ⟨Progress.refl s, valid⟩
        · split
          · exact ⟨Progress.refl s, valid⟩
          · rename_i bounded
            refine ⟨⟨List.prefix_rfl, Nat.le_max_left _ _, Nat.le_refl _, id⟩, ?_⟩
            change 0 < max s.floor (through + 1) ∧ max s.floor (through + 1) ≤ s.head + 1
            have := valid.1
            have := valid.2
            omega
    | delete =>
        simp only [execute, ite_eq_right deleted]
        exact ⟨⟨List.prefix_rfl, Nat.le_refl _, Nat.le_refl _, fun _ => rfl⟩, valid⟩

private theorem applyEntry_preserves [DecidableEq Payload] (s : Journal Payload)
    (entry : Entry (Request Payload)) (valid : s.Valid) :
    Progress s (applyEntry s entry) ∧ (applyEntry s entry).Valid := by
  cases entry with
  | mk term command =>
      cases command with
      | apply request => exact execute_preserves s request valid
      | barrier | configure => exact ⟨Progress.refl s, valid⟩

private theorem fold_preserves [DecidableEq Payload] (s : Journal Payload)
    (log : Log (Request Payload)) (valid : s.Valid) :
    Progress s (log.foldl applyEntry s) ∧ (log.foldl applyEntry s).Valid := by
  induction log generalizing s with
  | nil => exact ⟨Progress.refl s, valid⟩
  | cons entry rest ih =>
      obtain ⟨step, bounds⟩ := applyEntry_preserves s entry valid
      obtain ⟨trace, finalBounds⟩ := ih (applyEntry s entry) bounds
      exact ⟨step.trans trace, finalBounds⟩

theorem replay_valid [DecidableEq Payload] (log : Log (Request Payload)) :
    (replay log).Valid := (fold_preserves Journal.empty log (by simp [Journal.Valid, Journal.empty, Journal.head])).2

theorem replay_progress [DecidableEq Payload] {before after : Log (Request Payload)}
    (logHistory : before <+: after) : Progress (replay before) (replay after) := by
  obtain ⟨suffix, rfl⟩ := logHistory
  simpa only [replay, List.foldl_append] using fold_preserves (replay before) suffix (replay_valid before) |>.1

theorem Progress.record {before after : Journal Payload} (trace : Progress before after)
    {lsn : Nat} {payload : Payload} (record : before.record lsn = some payload) :
    after.record lsn = some payload := by
  have earlier := trace.history
  obtain ⟨suffix, same⟩ := earlier
  unfold Journal.record at record ⊢
  by_cases zero : lsn = 0
  · simp [zero] at record
  · simp only [ite_eq_right zero] at record ⊢
    rw [← same, List.getElem?_append_left (List.getElem?_eq_some_iff.mp record).1, record]

theorem stale_writer_refused [DecidableEq Payload] {s : Journal Payload} {fence : Fence}
    (different : s.fence ≠ some fence) (atLsn : Nat) (payload : Payload) :
    execute s (.append fence atLsn payload) =
      (s, if s.deleted then .deleted else .fenced s.epoch) := by
  cases h : s.deleted <;> simp [execute, h, decideAppend, different]

theorem seal_installs_fence [DecidableEq Payload] {s : Journal Payload}
    {expectedEpoch writer : Nat} (live : s.deleted = false) (expected : s.epoch = expectedEpoch) :
    execute s (.seal expectedEpoch writer) =
      ({ s with fence := some ⟨expectedEpoch + 1, writer⟩ },
        .sealed ⟨expectedEpoch + 1, writer⟩ s.head) := by
  simp [execute, live, decideSeal, expected]

theorem seal_refuses_previous_writer [DecidableEq Payload] {s : Journal Payload} {old : Fence}
    (live : s.deleted = false) (current : s.fence = some old) (writer atLsn : Nat)
    (payload : Payload) :
    let sealed := (execute s (.seal old.epoch writer)).1
    execute sealed (.append old atLsn payload) = (sealed, .fenced (old.epoch + 1)) := by
  have epoch : s.epoch = old.epoch := by simp [Journal.epoch, current]
  simp only [seal_installs_fence live epoch]
  have different : (some ⟨old.epoch + 1, writer⟩ : Option Fence) ≠ some old := by
    intro same
    have impossible := congrArg Fence.epoch (Option.some.inj same)
    simp at impossible
  simp [execute, live, decideAppend, different, Journal.epoch]

theorem retry_retained [DecidableEq Payload] {s : Journal Payload} {fence : Fence}
    {atLsn : Nat} {payload : Payload} (live : s.deleted = false) (current : s.fence = some fence)
    (retained : s.floor ≤ atLsn) (committed : atLsn ≤ s.head)
    (record : s.record atLsn = some payload) :
    execute s (.append fence atLsn payload) = (s, .appended atLsn) := by
  simp [execute, live, decideAppend, current, Nat.not_lt.mpr retained, committed, record]

theorem conflicting_retry_refused [DecidableEq Payload] {s : Journal Payload} {fence : Fence}
    {atLsn : Nat} {payload : Payload} (live : s.deleted = false) (current : s.fence = some fence)
    (retained : s.floor ≤ atLsn) (committed : atLsn ≤ s.head)
    (different : s.record atLsn ≠ some payload) :
    execute s (.append fence atLsn payload) = (s, .conflict s.head) := by
  simp [execute, live, decideAppend, current, Nat.not_lt.mpr retained, committed, different]

theorem deleted_is_terminal [DecidableEq Payload] {s : Journal Payload} (deleted : s.deleted = true)
    (request : Request Payload) : execute s request = (s, .deleted) := by simp [execute, deleted]

theorem successful_append_record [DecidableEq Payload] {s : Journal Payload} {fence : Fence}
    {atLsn : Nat} {payload : Payload} {lsn : Nat}
    (result : (execute s (.append fence atLsn payload)).2 = .appended lsn) :
    lsn = atLsn ∧ s.fence = some fence ∧
      (execute s (.append fence atLsn payload)).1.record lsn = some payload := by
  by_cases deleted : s.deleted = true
  · simp [execute, deleted] at result
  · simp only [execute, ite_eq_right deleted] at result ⊢
    unfold decideAppend at result ⊢
    split at result
    · contradiction
    · rename_i current
      rw [ite_eq_right current]
      split at result
      · contradiction
      · rename_i retained
        rw [ite_eq_right retained]
        split at result
        · rename_i committed
          rw [ite_eq_left committed]
          split at result
          · rename_i record
            rw [ite_eq_left record]
            cases result
            exact ⟨rfl, Classical.byContradiction current, record⟩
          · contradiction
        · rename_i beyond
          rw [ite_eq_right beyond]
          split at result
          · rename_i next
            rw [ite_eq_left next]
            cases result
            refine ⟨rfl, Classical.byContradiction current, ?_⟩
            simp [Journal.head] at next
            simp [Journal.record, next]
          · contradiction

structure Page (Payload : Type) where
  floor : Nat
  head : Nat
  records : List Payload
  deriving DecidableEq, Repr

def readPage (s : Journal Payload) (start limit : Nat) : Except Reply (Page Payload) :=
  if s.deleted then .error .deleted
  else if start < s.floor then .error (.belowFloor s.floor)
  else .ok ⟨s.floor, s.head, (s.history.drop (start - 1)).take limit⟩

theorem page_record_exact {s : Journal Payload} {start limit offset : Nat} {page : Page Payload}
    {payload : Payload} (valid : s.Valid) (reply : readPage s start limit = .ok page)
    (record : page.records[offset]? = some payload) :
    page.floor = s.floor ∧ page.head = s.head ∧
      s.floor ≤ start + offset ∧ start + offset ≤ s.head ∧
      s.record (start + offset) = some payload := by
  unfold readPage at reply
  split at reply
  · contradiction
  · split at reply
    · contradiction
    · rename_i retained
      cases reply
      simp only [List.getElem?_take, List.getElem?_drop] at record
      split at record
      · have inBounds := (List.getElem?_eq_some_iff.mp record).1
        have positive := valid.1
        have index : start + offset - 1 = start - 1 + offset := by omega
        have nonzero : start + offset ≠ 0 := by omega
        exact ⟨rfl, rfl, by omega, by simpa [Journal.head, index] using show start + offset ≤ s.history.length by omega,
          by rw [Journal.record, ite_eq_right nonzero, index, record]⟩
      · contradiction

def observeHead (s : Journal Payload) : Except Reply Nat :=
  if s.deleted then .error .deleted else .ok s.head

end Logkeeper.LeaderJournal
