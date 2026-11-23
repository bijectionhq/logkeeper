import Logkeeper.Kernel

namespace Logkeeper

set_option warningAsError true

namespace JournalRefinement

open Kernel

def Majority (members : List Replica) (votes : Replica → Bool) : Prop :=
  members.length < 2 * members.countP votes

private theorem disjoint_counts_fit (members : List Replica) (a b : Replica → Bool)
    (disjoint : ∀ replica ∈ members, a replica = true → b replica = false) :
    members.countP a + members.countP b ≤ members.length := by
  induction members with
  | nil => simp
  | cons replica rest prior =>
      have bound := prior (fun other member => disjoint other (List.mem_cons_of_mem _ member))
      have excludes := disjoint replica List.mem_cons_self
      simp only [List.countP_cons, List.length_cons]
      cases leftVote : a replica <;> cases rightVote : b replica <;>
        simp [leftVote, rightVote] at excludes ⊢ <;> omega

theorem majorities_overlap (members : List Replica) (a b : Replica → Bool)
    (first : Majority members a) (second : Majority members b) :
    ∃ replica ∈ members, a replica = true ∧ b replica = true := by
  apply Classical.byContradiction
  intro noOverlap
  have disjoint : ∀ replica ∈ members, a replica = true → b replica = false := by
    intro replica enrolled voted
    cases later : b replica with
    | false => rfl
    | true => exact False.elim (noOverlap ⟨replica, enrolled, voted, later⟩)
  have occupancy := disjoint_counts_fit members a b disjoint
  unfold Majority at first second
  omega

theorem durable_fence_excludes_stale_majority (members : List Replica)
    (promised accepts : Replica → Bool)
    (fenced : Majority members promised)
    (refuses : ∀ replica ∈ members, promised replica = true → accepts replica = false) :
    ¬ Majority members accepts := by
  intro oldQuorum
  obtain ⟨replica, enrolled, promisedHere, acceptedHere⟩ :=
    majorities_overlap members promised accepts fenced oldQuorum
  exact Bool.false_ne_true ((refuses replica enrolled promisedHere).symm.trans acceptedHere)

theorem overlapping_configurations_can_have_disjoint_majorities :
    ∃ oldVotes newVotes : Nat → Bool,
      Majority [1, 2, 3] oldVotes ∧ Majority [2, 3, 4] newVotes ∧
      ∀ voter, oldVotes voter = true → newVotes voter = false := by
  refine ⟨fun voter => voter == 1 || voter == 2, fun voter => voter == 3 || voter == 4,
    by unfold Majority; decide, by unfold Majority; decide, ?_⟩
  intro voter votedOld
  simp at votedOld
  rcases votedOld with rfl | rfl <;> decide

theorem distinct_zone_configuration_has_majority_after_loss
    {Replica Zone : Type} [DecidableEq Zone] (zone : Replica → Zone) (lost : Zone)
    (a b c : Replica) (ab : zone a ≠ zone b) (ac : zone a ≠ zone c) (bc : zone b ≠ zone c) :
    Majority [a, b, c] (fun member => decide (zone member ≠ lost)) := by
  by_cases lostA : zone a = lost
  · have bUp : zone b ≠ lost := fun h => ab (lostA.trans h.symm)
    have cUp : zone c ≠ lost := fun h => ac (lostA.trans h.symm)
    simp [Majority, lostA, bUp, cUp]
  · by_cases lostB : zone b = lost
    · have cUp : zone c ≠ lost := fun h => bc (lostB.trans h.symm)
      simp [Majority, lostA, lostB, cUp]
    · by_cases lostC : zone c = lost
      · simp [Majority, lostA, lostB, lostC]
      · simp [Majority, lostA, lostB, lostC]

abbrev Stores (Replica Payload : Type) := Replica → Nat → Entry Payload → Prop

structure Journal (Replica Payload : Type) where
  logical : State Payload
  members : List Replica
  copies : Stores Replica Payload

def Covered (journal : Journal Replica Payload) (lsn : Nat) (entry : Entry Payload) : Prop :=
  ∃ votes, Majority journal.members votes ∧
    ∀ replica ∈ journal.members, votes replica = true → journal.copies replica lsn entry

def CompleteCut (journal : Journal Replica Payload) : Prop :=
  ∀ lsn entry, journal.logical.firstRetained ≤ lsn →
    journal.logical.history[lsn]? = some entry → Covered journal lsn entry

def Appended (journal : Journal Replica Payload) (writer : Writer) (payload : Payload) :
    Journal Replica Payload :=
  {journal with logical := {journal.logical with
    history := journal.logical.history ++ [⟨writer.epoch, payload⟩]}}

inductive Step (limits : Limits) : Journal Replica Payload → Journal Replica Payload → Prop
  | persist {journal} (copies : Stores Replica Payload)
      (keeps : ∀ replica lsn entry, journal.copies replica lsn entry → copies replica lsn entry) :
      Step limits journal {journal with copies := copies}
  | append {journal writer} (lsn : Nat) (payload : Payload)
      (admitted : AppendAdmissible limits journal.logical writer lsn)
      (persisted : Covered journal journal.logical.history.length ⟨writer.epoch, payload⟩) :
      Step limits journal (Appended journal writer payload)
  | control {journal} (logical : State Payload)
      (decision : Kernel.Step limits journal.logical logical)
      (sameHistory : logical.history = journal.logical.history)
      (forwardFloor : journal.logical.firstRetained ≤ logical.firstRetained) :
      Step limits journal {journal with logical := logical}
  | finalizeMembership {journal} (members : List Replica)
      (certified : CompleteCut {journal with members := members}) :
      Step limits journal {journal with members := members}
  | reclaim {journal} (copies : Stores Replica Payload)
      (keeps : ∀ replica ∈ journal.members, ∀ lsn entry, journal.logical.firstRetained ≤ lsn →
        journal.copies replica lsn entry → copies replica lsn entry) :
      Step limits journal {journal with copies := copies}

theorem step_projects {limits : Limits} {before after : Journal Replica Payload}
    (step : Step limits before after) :
    before.logical = after.logical ∨ Kernel.Step limits before.logical after.logical := by
  cases step with
  | append lsn payload admitted _ => exact Or.inr (.append lsn payload admitted)
  | control _ decision _ _ => exact Or.inr decision
  | _ => exact Or.inl rfl

theorem step_preserves_complete_cut {limits : Limits} {before after : Journal Replica Payload}
    (valid : CompleteCut before) (step : Step limits before after) : CompleteCut after := by
  cases step with
  | persist _ keeps =>
      intro lsn entry retained chosen
      obtain ⟨votes, enough, confirms⟩ := valid lsn entry retained chosen
      exact ⟨votes, enough, fun replica member yes => keeps replica lsn entry (confirms replica member yes)⟩
  | append _ payload _ persisted =>
      intro lsn entry retained chosen
      by_cases older : lsn < before.logical.history.length
      · change (before.logical.history ++ [_])[lsn]? = some entry at chosen
        rw [List.getElem?_append_left older] at chosen
        exact valid lsn entry retained chosen
      · have ⟨inRange, _⟩ := List.getElem?_eq_some_iff.mp chosen
        simp only [Appended, List.length_append, List.length_singleton] at inRange
        have nextLsn : lsn = before.logical.history.length := by omega
        subst lsn
        change (before.logical.history ++ [_])[before.logical.history.length]? = some entry at chosen
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at chosen
        have same := Option.some.inj chosen
        rw [← same]
        exact persisted
  | control _ _ sameHistory forwardFloor =>
      intro lsn entry retained chosen
      rw [sameHistory] at chosen
      exact valid lsn entry (Nat.le_trans forwardFloor retained) chosen
  | finalizeMembership _ certified => exact certified
  | reclaim _ keeps =>
      intro lsn entry retained chosen
      obtain ⟨votes, enough, confirms⟩ := valid lsn entry retained chosen
      refine ⟨votes, enough, ?_⟩
      intro replica member yes
      exact keeps replica member lsn entry retained (confirms replica member yes)

inductive Trace (limits : Limits) : Journal Replica Payload → Journal Replica Payload → Prop
  | same (journal : Journal Replica Payload) : Trace limits journal journal
  | next {first before after} : Trace limits first before → Step limits before after →
      Trace limits first after

theorem trace_refines_and_preserves_cut {limits : Limits} {before after : Journal Replica Payload}
    (valid : CompleteCut before) (trace : Trace limits before after) :
    Kernel.Trace limits before.logical after.logical ∧ CompleteCut after := by
  induction trace with
  | same => exact ⟨.same _, valid⟩
  | next _ step prior =>
      obtain ⟨logical, completeCut⟩ := prior
      refine ⟨?_, step_preserves_complete_cut completeCut step⟩
      rcases step_projects step with same | next
      · rw [← same]
        exact logical
      · exact .next logical next

theorem any_recovery_quorum_can_read_exact_entry {journal : Journal Replica Payload}
    (cut : CompleteCut journal) (available : Replica → Bool)
    (recovering : Majority journal.members available)
    {lsn : Nat} {entry : Entry Payload} (retained : journal.logical.firstRetained ≤ lsn)
    (committed : journal.logical.history[lsn]? = some entry) :
    ∃ replica ∈ journal.members, available replica = true ∧ journal.copies replica lsn entry := by
  obtain ⟨votes, enough, exactCopies⟩ := cut lsn entry retained committed
  obtain ⟨replica, member, canRead, voted⟩ :=
    majorities_overlap journal.members available votes recovering enough
  exact ⟨replica, member, canRead, exactCopies replica member voted⟩

theorem verified_membership_change_program {limits : Limits} (journal : Journal Replica Payload)
    (newMembers : List Replica) (certified : CompleteCut {journal with members := newMembers}) :
    ∃ after, Step limits journal after ∧ after.logical = journal.logical ∧
      after.members = newMembers ∧ CompleteCut after :=
  ⟨_, .finalizeMembership newMembers certified, rfl, rfl, certified⟩

#print axioms majorities_overlap
#print axioms durable_fence_excludes_stale_majority
#print axioms overlapping_configurations_can_have_disjoint_majorities
#print axioms distinct_zone_configuration_has_majority_after_loss
#print axioms step_projects
#print axioms step_preserves_complete_cut
#print axioms trace_refines_and_preserves_cut
#print axioms any_recovery_quorum_can_read_exact_entry
#print axioms verified_membership_change_program

end JournalRefinement

end Logkeeper
