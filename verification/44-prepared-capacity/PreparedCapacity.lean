import Init.Omega

set_option warningAsError true

namespace PreparedCapacity

variable {Pool : Type}

structure Occupancy (Pool : Type) where
  ordinary : Pool → Nat
  prepared : Pool → Nat
  committed : Pool → Nat

def usage (book : Occupancy Pool) (pool : Pool) : Nat :=
  book.ordinary pool + book.prepared pool + book.committed pool

def OrdinaryFits (limit : Pool → Nat) (book : Occupancy Pool) (pool : Pool) (amount : Nat) : Prop :=
  usage book pool + amount ≤ limit pool

def UntalliedOrdinaryFits
    (limit : Pool → Nat) (book : Occupancy Pool) (pool : Pool) (amount : Nat) : Prop :=
  book.ordinary pool + book.committed pool + amount ≤ limit pool

def ExactSealFunds (need held : Pool → Nat) : Prop :=
  ∀ pool, held pool = need pool

def attributeToSeal (book : Occupancy Pool) (held : Pool → Nat) : Occupancy Pool :=
  {book with prepared := fun pool => book.prepared pool - held pool
             committed := fun pool => book.committed pool + held pool}

theorem a_prepared_hold_is_visible_to_ordinary_admission
    {limit : Pool → Nat} {book : Occupancy Pool} {pool : Pool} {amount : Nat}
    (fits : OrdinaryFits limit book pool amount) :
    book.ordinary pool + book.prepared pool + book.committed pool + amount ≤ limit pool := by
  exact fits

theorem moving_owned_credit_to_sealed_accounting_preserves_usage
    {book : Occupancy Pool} {held : Pool → Nat} (owned : ∀ pool, held pool ≤ book.prepared pool) :
    ∀ pool, usage (attributeToSeal book held) pool = usage book pool := by
  intro pool
  have available := owned pool
  simp only [usage, attributeToSeal]
  omega

theorem moving_owned_credit_preserves_ordinary_admission
    {limit : Pool → Nat} {book : Occupancy Pool} {held : Pool → Nat}
    (owned : ∀ pool, held pool ≤ book.prepared pool) (pool : Pool) (amount : Nat) :
    OrdinaryFits limit (attributeToSeal book held) pool amount ↔ OrdinaryFits limit book pool amount := by
  unfold OrdinaryFits
  rw [moving_owned_credit_to_sealed_accounting_preserves_usage owned pool]

theorem an_incomplete_vector_refuses_seal {held need : Pool → Nat} (pool : Pool)
    (missing : held pool < need pool) : ¬ ExactSealFunds need held := by
  intro funds
  rw [funds pool] at missing
  exact Nat.lt_irrefl _ missing

theorem omitting_prepared_capacity_cannot_preserve_maximal_ordinary_admission :
    ∃ (book : Occupancy Bool) (limit need held : Bool → Nat),
      (∀ pool, usage book pool ≤ limit pool) ∧
      (∀ pool, held pool ≤ book.prepared pool) ∧
      ¬ ExactSealFunds need held ∧
      UntalliedOrdinaryFits limit book false 1 ∧ ¬ OrdinaryFits limit book false 1 := by
  let book : Occupancy Bool := ⟨fun pool => if pool then 1 else 0,
    fun pool => if pool then 0 else 1, fun _ => 0⟩
  let limit (_ : Bool) := 1
  let need (_ : Bool) := 1
  let held (pool : Bool) := if pool then 0 else 1
  refine ⟨book, limit, need, held, ?_, ?_, ?_, ?_, ?_⟩
  · intro pool
    cases pool <;> decide
  · intro pool
    cases pool <;> decide
  · exact an_incomplete_vector_refuses_seal true (by decide)
  · simp [UntalliedOrdinaryFits, limit, book]
  · simp [OrdinaryFits, usage, limit, book]

#print axioms a_prepared_hold_is_visible_to_ordinary_admission
#print axioms moving_owned_credit_to_sealed_accounting_preserves_usage
#print axioms moving_owned_credit_preserves_ordinary_admission
#print axioms an_incomplete_vector_refuses_seal
#print axioms omitting_prepared_capacity_cannot_preserve_maximal_ordinary_admission

end PreparedCapacity
