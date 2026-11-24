import Logkeeper.StreamJournal

namespace Logkeeper.StreamAsync

open PrefixAgreement StreamJournal

set_option warningAsError true
set_option autoImplicit false

variable {Payload : Type}

/-! The two effects N8 found outside Study 119.

1. An empty Append publishes an inherited head. Seal must return a head that a quorum
   has published, and a new epoch may hold no record of its own, so the publication is
   necessary. Study 119's `publish` step admits it; the retained-record retry it replaced
   does not.
2. An incomplete Sync used to expose its partial history. The keeper now stages the
   history and exposes it only when the Sync completes, so the effect is a `syncPart`
   step. The former visible effect remains impossible. -/

/-- The live voting keeper receives an empty Append under its current promise.
    `at` is the first position after the published head on the Rust writer path. -/
def MayPublish (k : Keeper Payload) (epoch identity head : Nat) : Prop :=
  k.live ∧ k.identity = identity ∧ MayAppend k epoch ∧ k.floor ≤ head + 1 ∧ head ≤ k.tail

def publish (k : Keeper Payload) (head : Nat) : Keeper Payload :=
  { k with head := max k.head head }

/-- The rule Study 119 had before this change: a head rises only on a retained record
    of the current epoch. It is the negative control for publication. -/
def RetainedRetry (k : Keeper Payload) : Prop :=
  ∃ lsn payload, k.floor ≤ lsn ∧ k.history[lsn - 1]? = some ⟨k.synced, payload⟩

/-- Every admitted publication with an advertised head is a reference step. -/
theorem admitted_publication_is_a_step {w : Writer Payload} {k : Keeper Payload}
    {epoch identity head : Nat} (admitted : MayPublish k epoch identity head)
    (owns : w.owns k epoch) (advertised : w.advertised (k.history.take head)) :
    Step w k (publish k head) :=
  .publish admitted.1 admitted.2.2.1 owns admitted.2.2.2.2 advertised

/-- The old visible effect of an incomplete Sync: the tail changes and `synced` does not. -/
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
    | sync _ promised _ _ _ _ _ _ _ _ _ =>
        exact awaitingSync (promised.trans sameEpoch)
    | installFloor _ admitted _ _ _ _ _ _ =>
        exact awaitingSync (admitted.1.trans admitted.2.symm)
    | append _ admitted _ _ _ _ _ _ =>
        exact awaitingSync (admitted.1.trans admitted.2.symm)
    | delete =>
        unfold deleteKeeper at changedTail
        exact changedTail rfl
    | _ => exact changedTail rfl
  · exact changedTail rfl

/-- The shipped incomplete Sync changes only the staged history. -/
theorem staged_sync_keeps_the_view {writer : Writer Payload} {before after : Keeper Payload}
    {epoch floor start : Nat} {records : History Payload}
    (live : before.live) (promised : before.promised = epoch) (owns : writer.owns before epoch)
    (awaiting : before.synced ≠ epoch) (admitted : SyncAdmitted before floor start)
    (staged : after = { before with staging := some (before.syncFloor floor,
      syncImage before (writer.seed epoch) floor start records) }) :
    Step writer before after ∧ after.latest = before.latest ∧ after.head = before.head ∧
      after.floor = before.floor ∧ after.promised = before.promised := by
  subst after
  exact ⟨.syncPart live promised owns awaiting admitted, rfl, rfl, rfl, rfl⟩

private def prior : History Nat := [⟨1, 7⟩]
private def first : Round Nat := ⟨0, 0, 1, by decide, fun _ => empty⟩
private def second : Round Nat := ⟨1, 0, 1, by decide, fun _ => ⟨1, prior⟩⟩

private def writer : Writer Nat where
  round epoch := if epoch = 1 then some first else if epoch = 2 then some second else none
  issued epoch := if epoch = 1 ∨ epoch = 2 then prior else []
  advertised history := history = [] ∨ history = prior

private def created : Keeper Nat := { initial with created := true }
private def sealed : Keeper Nat := sealKeeper created 1 0
private def ready : Keeper Nat :=
  { accept sealed 1 [] with head := 0, floor := max sealed.floor (sealed.syncFloor 1) }
private def accepted : Keeper Nat :=
  { accept ready 1 (ready.history ++ stamp 1 [7]) with head := max ready.head 0 }
private def promised : Keeper Nat := sealKeeper accepted 2 1
private def recovered : Keeper Nat :=
  { accept promised 2 prior with head := 0, floor := max promised.floor (promised.syncFloor 1) }
private def fresh : Keeper Nat := sealKeeper ready 2 1

private theorem reachedReady : Reachable writer ready := by
  have c : Reachable writer created := .extend .initial (.create rfl)
  have s : Reachable writer sealed := .extend c (.sealKeeper ⟨rfl, rfl⟩ (Or.inl (by decide)))
  exact .extend s (.sync (epoch := 1) (floor := 1) (start := 1)
    (records := []) (head := 0) ⟨rfl, rfl⟩ rfl ⟨first, rfl, rfl⟩ (by unfold SyncAdmitted; decide)
    rfl (fun _ => rfl) (by decide) (Nat.le_refl _) (by decide) (by decide)
    (Or.inl rfl))

private theorem reached : Reachable writer recovered := by
  have a : Reachable writer accepted := .extend reachedReady (.append (payloads := [7]) (head := 0)
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨first, rfl, rfl⟩ (List.cons_ne_nil _ _) (by decide) (by decide)
    (by decide) (Or.inl rfl))
  have p : Reachable writer promised := .extend a (.sealKeeper ⟨rfl, rfl⟩ (Or.inl (by decide)))
  exact .extend p (.sync (epoch := 2) (floor := 1) (start := 2) (records := []) (head := 0)
    ⟨rfl, rfl⟩ rfl ⟨second, rfl, rfl⟩ (by unfold SyncAdmitted; decide) (by decide)
    (fun impossible => by contradiction) (by decide) (Nat.le_refl _)
    (by decide) (by decide) (Or.inl rfl))

/-- N8's first witness: after takeover no retained record has the new epoch, and the empty
    Append's publication is a reference step from a reachable state. -/
theorem inherited_publication_witness :
    ∃ (w : Writer Nat) (k : Keeper Nat),
      Reachable w k ∧ MayPublish k 2 1 1 ∧ k.head = 0 ∧ ¬ RetainedRetry k ∧
        Step w k (publish k 1) ∧ Reachable w (publish k 1) := by
  have admitted : MayPublish recovered 2 1 1 :=
    ⟨⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, by decide, by decide⟩
  have step := admitted_publication_is_a_step (w := writer) admitted ⟨second, rfl, rfl⟩ (Or.inr rfl)
  refine ⟨writer, recovered, reached, admitted, rfl, ?_, step, .extend reached step⟩
  rintro ⟨lsn, payload, _, eq⟩
  change prior[lsn - 1]? = some ⟨2, payload⟩ at eq
  generalize lsn - 1 = index at eq
  cases index <;> simp [prior] at eq

/-- A publication over a retained current-epoch record was already a reference step. -/
theorem current_record_publication_witness :
    MayPublish accepted 1 0 1 ∧ RetainedRetry accepted ∧ Step writer accepted (publish accepted 1) :=
  ⟨⟨⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, by decide, by decide⟩, ⟨1, 7, by decide, rfl⟩,
    .publish ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨first, rfl, rfl⟩ (by decide) (Or.inr rfl)⟩

/-- The shipped incomplete Sync from the witness: epoch 2 stages the inherited record
    on a keeper that has none, and the keeper's view stays at its epoch-1 vote. -/
theorem staged_sync_witness :
    ∃ (w : Writer Nat) (before after : Keeper Nat), Reachable w before ∧
      Step w before after ∧ after.tail = before.tail ∧ after.synced = before.synced ∧
      (after.staging.map fun staged => staged.2.length) = some 1 := by
  have reachedFresh : Reachable writer fresh :=
    .extend reachedReady (.sealKeeper ⟨rfl, rfl⟩ (Or.inl (by decide)))
  exact ⟨writer, fresh, _, reachedFresh,
    .syncPart (epoch := 2) (floor := 1) (start := 1) (records := prior) ⟨rfl, rfl⟩ rfl
      ⟨second, rfl, rfl⟩ (by decide) (by unfold SyncAdmitted; decide),
    rfl, rfl, rfl⟩

#print axioms admitted_publication_is_a_step
#print axioms inherited_publication_witness
#print axioms current_record_publication_witness
#print axioms incomplete_sync_with_changed_tail_has_no_reference_step
#print axioms staged_sync_keeps_the_view
#print axioms staged_sync_witness

end Logkeeper.StreamAsync
