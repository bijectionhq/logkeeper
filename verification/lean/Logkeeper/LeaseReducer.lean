import Logkeeper.DisposalLease

set_option warningAsError true

namespace DisposalLease

def interval_available (empty : Bool) (floor start through retained : Nat) : Bool :=
  empty || decide (floor ≤ start ∧ start ≤ through ∧ through - floor ≤ retained)

def checkpoint_open (floor cut : Nat) (retained closed : Bool) : Bool :=
  decide (floor ≤ cut) && retained && !closed

/-- The exact hold includes its owner, checkpoint and replay interval. Writer
authority is independent of this admission rule, including during vacancy. -/
def read_lease_end {Owner Hold : Type} [DecidableEq Owner] [DecidableEq Hold]
    (enrolled principal : Option Owner) (owner : Owner)
    (stored : Option Hold) (requested : Hold) (available openRoot : Bool)
    (now duration maxTime : Nat) : Option Nat :=
  if decide (enrolled = some owner ∧ principal = some owner ∧ stored = some requested) &&
      available && openRoot && decide (now + duration ≤ maxTime)
    then some (now + duration) else none

def retained_end (previous : Option Nat) (issued : Nat) : Nat :=
  max (previous.getD 0) issued

def writer_open (erasurePending : Bool) : Bool := !erasurePending

def settlement_fence (floor presented : Nat) (disposition closed : Bool) : Bool :=
  decide (floor = presented) && disposition && closed

theorem read_lease_requires_exact_protected_basis {Owner Hold : Type}
    [DecidableEq Owner] [DecidableEq Hold] {enrolled principal : Option Owner} {owner : Owner}
    {stored : Option Hold} {requested : Hold} {available openRoot : Bool}
    {now duration maxTime endTime : Nat}
    (issued : read_lease_end enrolled principal owner stored requested available openRoot
      now duration maxTime = some endTime) :
    enrolled = some owner ∧ principal = some owner ∧ stored = some requested ∧
      available = true ∧ openRoot = true ∧ endTime = now + duration := by
  unfold read_lease_end at issued
  split at issued <;> simp_all [Bool.and_eq_true]

theorem old_root_cannot_renew {floor cut : Nat} (older : cut < floor) (retained closed : Bool) :
    checkpoint_open floor cut retained closed = false := by
  have blocked : ¬ floor ≤ cut := Nat.not_le_of_lt older
  rw [checkpoint_open, decide_eq_false blocked]
  simp only [Bool.false_and]


theorem pending_erasure_blocks_writer_changes : writer_open true = false := by decide

theorem settlement_must_match_erasure_floor {floor presented : Nat} {disposition closed : Bool}
    (settled : settlement_fence floor presented disposition closed = true) :
    floor = presented := by
  simp [settlement_fence, Bool.and_eq_true] at settled
  exact settled.1.1

theorem read_lease_retains_greatest_end (previous : Option Nat) (issued : Nat) :
    previous.getD 0 ≤ retained_end previous issued ∧ issued ≤ retained_end previous issued :=
  ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩

/-- The proof projects each exact enrollment separately. The hold count is
the cardinality of the fibers of the hold map at that enrollment. Issued
and greatest are ghost history for the chosen prefix. -/
structure OwnerImage where
  issued : Bool := false
  rostered : Bool := false
  holds : Nat := 0
  recorded : Option Nat := none
  greatest : Option Nat := none
  deriving DecidableEq

def OwnerImage.backed (image : OwnerImage) : Bool :=
  image.rostered || decide (0 < image.holds)

def OwnerImage.valid (image : OwnerImage) : Prop :=
  (image.backed = true → image.issued = true) ∧
  (image.issued = false → image.greatest = none) ∧
  image.recorded = (if image.backed then image.greatest else none)

/-- Release and roster changes prune only after the last backing reference. -/
def OwnerImage.prune (image : OwnerImage) : OwnerImage :=
  { image with recorded := if image.backed then image.recorded else none }

def OwnerImage.renew (image : OwnerImage) (endTime : Nat) : OwnerImage :=
  { image with recorded := some (retained_end image.recorded endTime),
               greatest := some (retained_end image.greatest endTime) }

/-- Refusals, retries and commands that leave these fields alone project to
unchanged. Hold admission uses an exact roster entry or the live recovery
hold used by ProtectRoot. Rotation adds a recovery hold. -/
inductive OwnerStep : OwnerImage → OwnerImage → Prop
  | enroll (s : OwnerImage) (fresh : s.issued = false) :
      OwnerStep s { s with issued := true, rostered := true }
  | withdraw (s : OwnerImage) :
      OwnerStep s ({ s with rostered := false }.prune)
  | add (s : OwnerImage) (backed : s.backed = true) :
      OwnerStep s { s with holds := s.holds + 1 }
  | release (s : OwnerImage) :
      OwnerStep s ({ s with holds := s.holds - 1 }.prune)
  | dispose (s : OwnerImage) (withdrawn : s.rostered = false) :
      OwnerStep s ({ s with holds := 0 }.prune)
  | lease (s : OwnerImage) (enrolled : s.rostered = true) (endTime : Nat) :
      OwnerStep s (s.renew endTime)
  | leaseRead (s : OwnerImage) (enrolled : s.rostered = true) (endTime : Nat) :
      OwnerStep s (s.renew endTime)
  | rotate (s : OwnerImage) (enrolled : s.rostered = true) :
      OwnerStep s { s with holds := s.holds + 1 }
  | vacate (s : OwnerImage) (erasurePending : Bool) (ready : writer_open erasurePending = true) :
      OwnerStep s s
  | unchanged (s : OwnerImage) : OwnerStep s s

private theorem prune_valid (s t : OwnerImage) (valid : s.valid)
    (issued : t.issued = s.issued) (greatest : t.greatest = s.greatest)
    (recorded : t.recorded = s.recorded)
    (backing : t.backed = true → s.backed = true) : t.prune.valid := by
  rcases valid with ⟨owned, history, ends⟩
  refine ⟨fun b => issued ▸ owned (backing b), fun h => greatest ▸ history (issued ▸ h), ?_⟩
  change (if t.backed then t.recorded else none) = (if t.backed then t.greatest else none)
  by_cases h : t.backed = true
  · simp [h, recorded, greatest, ends, backing h]
  · simp [h]

private theorem renew_valid (s : OwnerImage) (valid : s.valid)
    (enrolled : s.rostered = true) (endTime : Nat) : (s.renew endTime).valid := by
  have backed : s.backed = true := by simp [OwnerImage.backed, enrolled]
  have issued := valid.1 backed
  have same : s.recorded = s.greatest := by simpa [backed] using valid.2.2
  simp [OwnerImage.valid, OwnerImage.renew, OwnerImage.backed, enrolled, issued, same]

private theorem add_valid (s : OwnerImage) (valid : s.valid)
    (backed : s.backed = true) : ({ s with holds := s.holds + 1 } : OwnerImage).valid := by
  have issued := valid.1 backed
  have same : s.recorded = s.greatest := by simpa [backed] using valid.2.2
  simp [OwnerImage.valid, OwnerImage.backed, issued, same]

theorem reducer_preserves {s t : OwnerImage} (step : OwnerStep s t) (valid : s.valid) :
    t.valid := by
  cases step with
  | enroll fresh =>
    have absent : s.backed = false := by
      cases h : s.backed
      · rfl
      · have h' := valid.1 h
        simp [fresh] at h'
    have recorded : s.recorded = none := by simpa [absent] using valid.2.2
    simp [OwnerImage.valid, OwnerImage.backed, recorded, valid.2.1 fresh]
  | withdraw =>
    apply prune_valid s { s with rostered := false } valid rfl rfl rfl
    simp [OwnerImage.backed]
    exact fun held => Or.inr held
  | add backed => exact add_valid _ valid backed
  | release =>
    apply prune_valid s { s with holds := s.holds - 1 } valid rfl rfl rfl
    simp [OwnerImage.backed]
    intro backed
    rcases backed with enrolled | held
    · exact Or.inl enrolled
    · exact Or.inr (by omega)
  | dispose withdrawn =>
    apply prune_valid s { s with holds := 0 } valid rfl rfl rfl
    simp [OwnerImage.backed, withdrawn]
  | lease enrolled endTime | leaseRead enrolled endTime =>
    exact renew_valid _ valid enrolled endTime
  | rotate enrolled => exact add_valid _ valid (by simp [OwnerImage.backed, enrolled])
  | vacate | unchanged => exact valid

inductive OwnerTrace : OwnerImage → Prop
  | initial : OwnerTrace {}
  | step {s t} : OwnerTrace s → OwnerStep s t → OwnerTrace t

theorem reducer_establishes {s : OwnerImage} (reachable : OwnerTrace s) : s.valid := by
  induction reachable with
  | initial => simp [OwnerImage.valid, OwnerImage.backed]
  | step _ step ih => exact reducer_preserves step ih

theorem held_owner_is_enrolled_or_pending {s : OwnerImage}
    (reachable : OwnerTrace s) (held : 0 < s.holds) :
    s.issued = true ∧ (s.rostered = true ∨ (s.rostered = false ∧ 0 < s.holds)) := by
  refine ⟨(reducer_establishes reachable).1 (by simp [OwnerImage.backed, held]), ?_⟩
  cases s.rostered <;> simp [held]

theorem retained_lease_is_greatest {s : OwnerImage}
    (reachable : OwnerTrace s) (backed : s.backed = true) : s.recorded = s.greatest := by
  simpa [backed] using (reducer_establishes reachable).2.2

theorem release_read_keeps_end_if_backed (s : OwnerImage)
    (stillBacked : ({ s with holds := s.holds - 1 } : OwnerImage).backed = true) :
    ({ s with holds := s.holds - 1 }.prune).recorded = s.recorded := by
  simp only [OwnerImage.prune, stillBacked, ite_true]

theorem expiry_disposal_clears_owner (s : OwnerImage) (withdrawn : s.rostered = false) :
    let t := { s with holds := 0 }.prune
    t.holds = 0 ∧ t.recorded = none := by
  simp [OwnerImage.prune, OwnerImage.backed, withdrawn]

/-- An in-range identity may be absent even from issuance history. Successful
expiry disposal attests that the exact identity has no remaining hold or lease. -/
theorem unissued_disposal_is_noop :
    may_dispose true 1 1 false 0 none 100 100 = true ∧
    ({ ({} : OwnerImage) with holds := 0 }.prune) = {} := by decide

theorem owner_page_after_reducer_step {Worker Owner : Type} [LT Owner]
    (roster : Worker → Option Owner) (holds : List (Owner × Worker))
    (after : Option Owner) (limit : Nat) (page : List Owner)
    (exactPage : owner_page (qualifying_owners holds roster after) limit page) :
    (∀ owner ∈ page, ∃ worker, (owner, worker) ∈ holds ∧ eligible_owner roster owner worker after) ∧
    (∀ owner, qualifying_owners holds roster after owner → owner ∉ page →
      page.length = limit ∧ ∀ listed ∈ page, listed < owner) :=
  ⟨exactPage.2.2.1, exactPage.2.2.2⟩

-- An enrolled reader obtains a lease against an exact empty hold during vacancy.
example :
    read_lease_end (some 2) (some 2) 2 (some 7) 7
      (interval_available true 4 0 0 0) (checkpoint_open 0 0 true false) 10 8 100 = some 18 :=
  by decide

-- After release of one hold, a withdrawn owner can still have a retained lease.
example : OwnerTrace { issued := true, holds := 1, recorded := some 18, greatest := some 18 } := by
  let enrolled : OwnerImage := { issued := true, rostered := true }
  have e : OwnerTrace enrolled := OwnerTrace.step .initial (.enroll {} rfl)
  have h := OwnerTrace.step e (.add enrolled rfl)
  have h' := OwnerTrace.step h (.add { enrolled with holds := 1 } rfl)
  have r := OwnerTrace.step h' (.leaseRead { enrolled with holds := 2 } rfl 18)
  have w := OwnerTrace.step r (.withdraw ({ enrolled with holds := 2 }.renew 18))
  exact OwnerTrace.step w (.release ({ { enrolled with holds := 2 }.renew 18 with rostered := false }.prune))

#print axioms read_lease_requires_exact_protected_basis
#print axioms old_root_cannot_renew
#print axioms pending_erasure_blocks_writer_changes
#print axioms settlement_must_match_erasure_floor
#print axioms read_lease_retains_greatest_end
#print axioms reducer_preserves
#print axioms reducer_establishes
#print axioms held_owner_is_enrolled_or_pending
#print axioms retained_lease_is_greatest
#print axioms release_read_keeps_end_if_backed
#print axioms expiry_disposal_clears_owner
#print axioms unissued_disposal_is_noop
#print axioms owner_page_after_reducer_step

end DisposalLease
