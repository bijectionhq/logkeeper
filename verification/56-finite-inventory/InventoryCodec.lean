import EnvelopeCodec
import FiniteCounters

set_option warningAsError true

namespace InventoryCodec

open EnvelopeCodec (Bytes Field takeField takeField_on_encoded_word wordLimit wordBytes readWord word
  wordBytes_length fixed_width_words_roundtrip)
open PoolIncarnations (Access)

inductive Phase where
  | offline
  | quarantine
  | eligible
  | sealed
  deriving DecidableEq

def code : Phase → UInt8
  | .offline => 0
  | .quarantine => 1
  | .eligible => 2
  | .sealed => 3

def phaseAt (tag : UInt8) : Option Phase :=
  if tag = 0 then some .offline else if tag = 1 then some .quarantine
  else if tag = 2 then some .eligible else if tag = 3 then some .sealed else none

private theorem phaseAt_code (phase : Phase) : phaseAt (code phase) = some phase := by
  cases phase <;> decide

structure Row where
  scope : Nat
  epoch : Nat
  phase : Phase
  deriving DecidableEq

structure Inventory where
  issued : Nat
  rows : List Row
  deriving DecidableEq

def fromAccess (width scope : Nat) (access : Access) : Row :=
  if access.epoch < wordLimit width then
    ⟨scope, access.epoch, match access.phase with
      | .offline => .offline
      | .quarantine => .quarantine
      | .eligible => .eligible⟩
  else ⟨scope, wordLimit width - 1, .sealed⟩

def toAccess (row : Row) : Access :=
  match row.phase with
  | .offline => ⟨.offline, row.epoch⟩
  | .quarantine => ⟨.quarantine, row.epoch⟩
  | .eligible => ⟨.eligible, row.epoch⟩
  | .sealed => ⟨.offline, row.epoch + 1⟩

theorem the_terminal_phase_encodes_the_exhausted_logical_epoch {width scope : Nat} {access : Access}
    (fits : access.epoch ≤ wordLimit width)
    (sealed : wordLimit width ≤ access.epoch → access.phase = .offline) :
    toAccess (fromAccess width scope access) = access := by
  cases access with
  | mk phase epoch =>
      by_cases usable : epoch < wordLimit width
      · cases phase <;> simp [fromAccess, toAccess, usable]
      · have last : epoch = wordLimit width := by
          have upper : epoch ≤ wordLimit width := fits
          omega
        have atLimit : wordLimit width ≤ epoch := by omega
        have offline : phase = .offline := sealed atLimit
        have nonzero : 0 < wordLimit width := Nat.pow_pos (by decide)
        subst phase
        rw [last]
        unfold fromAccess
        rw [ite_eq_right (Nat.lt_irrefl _)]
        change Access.mk .offline (wordLimit width - 1 + 1) = Access.mk .offline (wordLimit width)
        exact congrArg (Access.mk .offline) (Nat.sub_add_cancel nonzero)

def RowFits (width issued : Nat) (row : Row) : Prop :=
  0 < row.scope ∧ row.scope ≤ issued ∧ row.epoch < wordLimit width ∧
    (row.phase = .sealed → row.epoch + 1 = wordLimit width)

def WellFormed (width limit : Nat) (inventory : Inventory) : Prop :=
  inventory.issued < wordLimit width ∧ inventory.rows.length ≤ limit ∧
    inventory.rows.Pairwise (fun earlier later => later.scope < earlier.scope) ∧
    ∀ row ∈ inventory.rows, RowFits width inventory.issued row

def fromState (width : Nat) (state : PoolIncarnations.State Ticket) : Inventory :=
  ⟨state.issued, state.registry.map (fun scope => fromAccess width scope (state.access scope))⟩

private theorem fromAccess_exact_scope (width scope : Nat) (access : Access) :
    (fromAccess width scope access).scope = scope := by
  simp [fromAccess]
  split <;> rfl

theorem a_finite_reference_state_has_a_well_formed_inventory
    {width limit : Nat} {state : PoolIncarnations.State Ticket}
    {layout : SharedExtentAccounting.Layout Nat} {needs : SharedCustody.Dependencies}
    (safe : PoolIncarnations.Sound limit layout needs state)
    (fits : FiniteCounters.Fits (wordLimit width - 1) (wordLimit width - 1) state)
    (ordered : FiniteCounters.Ordered state) :
    WellFormed width limit (fromState width state) := by
  have positiveWidth : 0 < wordLimit width := Nat.pow_pos (by decide)
  refine ⟨?_, by simpa [fromState] using safe.fit, ?_, ?_⟩
  · have issuer := fits.issuer
    change state.issued < wordLimit width
    omega
  · rw [fromState, List.pairwise_map]
    exact ordered.1.imp (fun less => by simpa only [fromAccess_exact_scope] using less)
  · intro row member
    obtain ⟨scope, live, rfl⟩ := List.mem_map.mp member
    have positive := ordered.2 scope live
    have issued := safe.issued scope live
    unfold RowFits fromAccess
    split
    next usable =>
      refine ⟨positive, issued, usable, ?_⟩
      cases (state.access scope).phase <;> simp
    next =>
      refine ⟨positive, issued, ?_, fun _ => Nat.sub_add_cancel positiveWidth⟩
      change wordLimit width - 1 < wordLimit width
      omega

def encodeRow (width : Nat) (row : Row) : Bytes :=
  code row.phase :: (wordBytes width row.scope ++ wordBytes width row.epoch)

def parseRow (width : Nat) (wire : Bytes) : Option (Row × Bytes) :=
  match wire with
  | [] => none
  | phase :: bytes => do
      let phase ← phaseAt phase
      let (scope, rest) ← takeField width bytes
      let (epoch, tail) ← takeField width rest
      pure (⟨readWord scope.val, readWord epoch.val, phase⟩, tail)

def rowsBytes (width : Nat) : List Row → Bytes
  | [] => []
  | row :: tail => encodeRow width row ++ rowsBytes width tail

def parseRows (width : Nat) : Nat → Bytes → Option (List Row)
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => some []
  | limit + 1, byte :: tail => do
      let (row, rest) ← parseRow width (byte :: tail)
      let rows ← parseRows width limit rest
      pure (row :: rows)

private theorem parseRow_on_encoded {width : Nat} {row : Row} (tail : Bytes)
    (scopeFits : row.scope < wordLimit width) (epochFits : row.epoch < wordLimit width) :
    parseRow width (encodeRow width row ++ tail) = some (row, tail) := by
  cases row with
  | mk scope epoch phase =>
      have scopeWord := takeField_on_encoded_word (word width scope) (wordBytes width epoch ++ tail)
      have epochWord := takeField_on_encoded_word (word width epoch) tail
      simp only [word] at scopeWord epochWord
      simp [encodeRow, parseRow, phaseAt_code, List.append_assoc, scopeWord, epochWord,
        fixed_width_words_roundtrip scopeFits, fixed_width_words_roundtrip epochFits]

private theorem parseRows_on_encoded {width limit : Nat} {rows : List Row}
    (fits : rows.length ≤ limit)
    (wordsFit : ∀ row ∈ rows, row.scope < wordLimit width ∧ row.epoch < wordLimit width) :
    parseRows width limit (rowsBytes width rows) = some rows := by
  induction limit generalizing rows with
  | zero =>
      cases rows with
      | nil => rfl
      | cons => simp at fits
  | succ limit prior =>
      cases rows with
      | nil => rfl
      | cons row rest =>
          have rowFits := wordsFit row (by simp)
          have tailFits : rest.length ≤ limit := by simpa using fits
          have tail := prior tailFits (fun item live => wordsFit item (List.mem_cons_of_mem _ live))
          have parsed := parseRow_on_encoded (rowsBytes width rest) rowFits.1 rowFits.2
          rw [rowsBytes]
          change (do
            let (found, remaining) ← parseRow width (encodeRow width row ++ rowsBytes width rest)
            let foundTail ← parseRows width limit remaining
            pure (found :: foundTail)) = some (row :: rest)
          simp [parsed, tail]

def tag : UInt8 := 2

def encode (width : Nat) (inventory : Inventory) : Bytes :=
  tag :: (wordBytes width inventory.issued ++ rowsBytes width inventory.rows)

def parse (width limit : Nat) (wire : Bytes) : Option Inventory :=
  match wire with
  | [] => none
  | marker :: payload =>
      if marker = tag then do
        let (issued, tail) ← takeField width payload
        let rows ← parseRows width limit tail
        pure ⟨readWord issued.val, rows⟩
      else none

noncomputable def decode (width limit : Nat) (wire : Bytes) : Option Inventory := by
  classical
  exact match parse width limit wire with
  | none => none
  | some inventory =>
      if WellFormed width limit inventory ∧ encode width inventory = wire then some inventory else none

theorem a_well_formed_inventory_roundtrips {width limit : Nat} {inventory : Inventory}
    (valid : WellFormed width limit inventory) :
    decode width limit (encode width inventory) = some inventory := by
  have wordsFit : ∀ row ∈ inventory.rows,
      row.scope < wordLimit width ∧ row.epoch < wordLimit width := by
    intro row member
    have rowFits := valid.2.2.2 row member
    exact ⟨Nat.lt_of_le_of_lt rowFits.2.1 valid.1, rowFits.2.2.1⟩
  have rows := parseRows_on_encoded valid.2.1 wordsFit
  have issued := takeField_on_encoded_word (word width inventory.issued) (rowsBytes width inventory.rows)
  simp only [word] at issued
  have parsed : parse width limit (encode width inventory) = some inventory := by
    cases inventory
    simp [parse, encode, issued, rows, fixed_width_words_roundtrip valid.1]
  simp [decode, parsed, valid]

theorem accepted_inventory_bytes_are_canonical {width limit : Nat} {wire : Bytes} {inventory : Inventory}
    (accepted : decode width limit wire = some inventory) :
    WellFormed width limit inventory ∧ encode width inventory = wire := by
  cases parsed : parse width limit wire with
  | none => simp [decode, parsed] at accepted
  | some found =>
      simp only [decode, parsed] at accepted
      split at accepted
      next valid =>
        cases accepted
        exact valid
      next => simp at accepted

theorem authenticated_inventory_rejects_a_different_representation
    {width limit : Nat} {first second : Bytes} {inventory : Inventory}
    (left : decode width limit first = some inventory) (right : decode width limit second = some inventory) :
    first = second := by
  exact (accepted_inventory_bytes_are_canonical left).2.symm.trans (accepted_inventory_bytes_are_canonical right).2

private theorem rowsBytes_length (width : Nat) (rows : List Row) :
    (rowsBytes width rows).length = (2 * width + 1) * rows.length := by
  induction rows with
  | nil => simp [rowsBytes]
  | cons row rest prior =>
      simp [rowsBytes, encodeRow, wordBytes_length, prior, Nat.mul_add]
      omega

theorem encoded_inventory_has_exact_byte_cost (width : Nat) (inventory : Inventory) :
    (encode width inventory).length = 1 + width + (2 * width + 1) * inventory.rows.length := by
  simp only [encode, List.length_cons, List.length_append, wordBytes_length, rowsBytes_length]
  omega

def maximumBytes (width limit : Nat) : Nat := 1 + width + (2 * width + 1) * limit

theorem two_selectable_inventory_sections_fit_the_reserved_bytes {width limit : Nat}
    {stable visible : Inventory}
    (stableFits : WellFormed width limit stable) (visibleFits : WellFormed width limit visible) :
    (encode width stable).length + (encode width visible).length ≤ 2 * maximumBytes width limit := by
  rw [encoded_inventory_has_exact_byte_cost, encoded_inventory_has_exact_byte_cost]
  have first := Nat.mul_le_mul_left (2 * width + 1) stableFits.2.1
  have second := Nat.mul_le_mul_left (2 * width + 1) visibleFits.2.1
  simp only [maximumBytes, Nat.mul_add]
  omega

theorem accepted_inventory_scopes_never_exceed_the_issuer {width limit : Nat}
    {wire : Bytes} {inventory : Inventory} {row : Row}
    (accepted : decode width limit wire = some inventory) (live : row ∈ inventory.rows) :
    row.scope ≤ inventory.issued := by
  exact ((accepted_inventory_bytes_are_canonical accepted).1.2.2.2 row live).2.1

#print axioms fixed_width_words_roundtrip
#print axioms the_terminal_phase_encodes_the_exhausted_logical_epoch
#print axioms a_finite_reference_state_has_a_well_formed_inventory
#print axioms a_well_formed_inventory_roundtrips
#print axioms accepted_inventory_bytes_are_canonical
#print axioms authenticated_inventory_rejects_a_different_representation
#print axioms encoded_inventory_has_exact_byte_cost
#print axioms two_selectable_inventory_sections_fit_the_reserved_bytes
#print axioms accepted_inventory_scopes_never_exceed_the_issuer

end InventoryCodec
