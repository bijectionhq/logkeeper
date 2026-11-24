import Logkeeper.StreamJournal

namespace Logkeeper.StreamAsync

open PrefixAgreement StreamJournal

set_option warningAsError true
set_option autoImplicit false

variable {Payload : Type}

/-- The live voting keeper receives an empty Append under its current promise.
    `at` is the first position after the published head on the Rust writer path. -/
def MayPublish (k : Keeper Payload) (epoch identity head : Nat) : Prop :=
  k.live ∧ k.identity = identity ∧ MayAppend k epoch ∧ k.floor ≤ head + 1 ∧ head ≤ k.tail

def publish (k : Keeper Payload) (head : Nat) : Keeper Payload :=
  { k with head := max k.head head }

/-- Study 119 can increase the head of an existing history only on a retained
    record retry from the current epoch. An empty Append needs no such record. -/
theorem publish_without_current_record_has_no_reference_step
    {writer : Writer Payload} {k : Keeper Payload} {head : Nat}
    (increases : k.head < head)
    (inherited : ∀ lsn payload, k.floor ≤ lsn →
      k.history[lsn - 1]? ≠ some ⟨k.synced, payload⟩) :
    ¬ (Step writer k (publish k head) ∨ k = publish k head) := by
  have published : (publish k head).head = head := Nat.max_eq_right (Nat.le_of_lt increases)
  have different : k ≠ publish k head := fun h =>
    Nat.ne_of_lt increases ((congrArg Keeper.head h).trans published)
  rintro (step | idle)
  · generalize eq : publish k head = next at step
    cases step with
    | sealKeeper _ _ =>
        have same := congrArg Keeper.head eq
        simp only [sealKeeper] at same
        split at same <;> exact (Nat.ne_of_gt increases) (published.symm.trans same)
    | append _ _ _ _ _ _ _ _ =>
        have tails := congrArg Keeper.tail eq
        simp [publish, Keeper.tail, accept, Keeper.history, Keeper.latest,
          DurableAcceptor.acceptVote] at tails
    | retry _ synced _ retained record _ _ =>
        exact inherited _ _ retained (synced.2.symm ▸ record)
    | _ =>
        have same := congrArg Keeper.head eq
        exact (Nat.ne_of_gt increases) (published.symm.trans same)
  · exact different idle

/-- In Study 119 an incomplete Sync changes only staging. A Check or Seal can
    already observe the changed tail of the Rust keeper before Sync completes. -/
theorem incomplete_sync_with_changed_tail_has_no_reference_step
    {writer : Writer Payload} {before after : Keeper Payload}
    (awaitingSync : before.promised ≠ before.synced)
    (sameEpoch : after.synced = before.synced) (changedTail : after.tail ≠ before.tail) :
    ¬ (Step writer before after ∨ before = after) := by
  rintro (step | rfl)
  · cases step with
    | sealKeeper _ _ =>
        unfold sealKeeper at changedTail
        split at changedTail <;> exact changedTail rfl
    | sync _ promised _ _ _ _ _ _ =>
        exact awaitingSync (promised.trans sameEpoch)
    | append _ admitted _ _ _ _ _ _ =>
        exact awaitingSync (admitted.1.trans admitted.2.symm)
    | _ => exact changedTail rfl
  · exact changedTail rfl

private def prior : History Nat := [⟨1, 7⟩]
private def first : Round Nat := ⟨0, 0, 1, by decide, fun _ => empty⟩
private def second : Round Nat := ⟨1, 0, 1, by decide, fun _ => ⟨1, prior⟩⟩

private def writer : Writer Nat where
  round epoch := if epoch = 1 then some first else if epoch = 2 then some second else none
  issued epoch := if epoch = 1 ∨ epoch = 2 then prior else []
  advertised history := history = [] ∨ history = prior

private def created : Keeper Nat := { initial with created := true }
private def sealed : Keeper Nat := sealKeeper created 1 0
private def ready : Keeper Nat := accept sealed 1 []
private def accepted : Keeper Nat := accept ready 1 prior
private def promised : Keeper Nat := sealKeeper accepted 2 1
private def recovered : Keeper Nat := accept promised 2 prior

private theorem reached : Reachable writer recovered := by
  have c : Reachable writer created := .extend .initial (.create rfl)
  have s : Reachable writer sealed := .extend c (.sealKeeper ⟨rfl, rfl⟩ (Or.inl (by decide)))
  have r : Reachable writer ready := .extend s (.sync (epoch := 1) (start := 1)
    (records := []) ⟨rfl, rfl⟩ rfl ⟨first, rfl, rfl⟩ (by decide) rfl
    ⟨by decide, rfl⟩ (fun _ => rfl) (by decide))
  have a : Reachable writer accepted := .extend r (.append (lsn := 1) (head := 0)
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨first, rfl, rfl⟩ rfl (by decide) (by decide) (by decide) (Or.inl rfl))
  have p : Reachable writer promised := .extend a (.sealKeeper ⟨rfl, rfl⟩ (Or.inl (by decide)))
  exact .extend p (.sync (epoch := 2) (start := 2) (records := []) ⟨rfl, rfl⟩ rfl
    ⟨second, rfl, rfl⟩ (by decide) rfl ⟨by decide, rfl⟩ (fun impossible => by contradiction)
    (by decide))

theorem inherited_publication_witness :
    ∃ (w : Writer Nat) (k : Keeper Nat),
      Reachable w k ∧ MayPublish k 2 1 1 ∧ k.head = 0 ∧
        ¬ (Step w k (publish k 1) ∨ k = publish k 1) := by
  refine ⟨writer, recovered, reached, ⟨⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, by decide, by decide⟩,
    rfl, publish_without_current_record_has_no_reference_step (by decide) ?_⟩
  intro lsn payload _ eq
  change prior[lsn - 1]? = some ⟨2, payload⟩ at eq
  generalize lsn - 1 = index at eq
  cases index <;> simp [prior] at eq

theorem current_record_publication_witness :
    MayPublish accepted 1 0 1 ∧ Step writer accepted (publish accepted 1) := by
  exact ⟨⟨⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, by decide, by decide⟩,
    .retry (epoch := 1) (lsn := 1) (payload := 7) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
      ⟨first, rfl, rfl⟩ (by decide) rfl (by decide) (Or.inr rfl)⟩

#print axioms inherited_publication_witness
#print axioms current_record_publication_witness
#print axioms incomplete_sync_with_changed_tail_has_no_reference_step

end Logkeeper.StreamAsync
