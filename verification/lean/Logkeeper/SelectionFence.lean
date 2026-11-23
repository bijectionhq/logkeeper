import Logkeeper.PrefixAgreement

namespace Logkeeper.SelectionFence

open PrefixAgreement JournalRefinement

set_option warningAsError true

structure Image (Command : Type) where
  promised : Nat
  accepted : Option (Vote Command)

def Image.Dominates (later earlier : Image Command) : Prop :=
  earlier.promised ≤ later.promised ∧
  ∀ vote, earlier.accepted = some vote →
    ∃ current, later.accepted = some current ∧ RankLE vote current

private theorem dominates_refl (image : Image Command) : image.Dominates image := by
  exact ⟨Nat.le_refl _, fun vote exactVote => ⟨vote, exactVote, rank_refl _⟩⟩

private theorem dominates_trans {a b c : Image Command}
    (cb : c.Dominates b) (ba : b.Dominates a) : c.Dominates a := by
  refine ⟨Nat.le_trans ba.1 cb.1, ?_⟩
  intro vote exactVote
  obtain ⟨second, held, rank⟩ := ba.2 vote exactVote
  obtain ⟨third, selected, later⟩ := cb.2 second held
  exact ⟨third, selected, rank_trans rank later⟩

abbrev Media (Command : Type) := Bool → Option (Image Command)

def mirrored (image : Image Command) : Media Command := fun _ => some image

def replace (media : Media Command) (slot : Bool) (image : Option (Image Command)) : Media Command :=
  fun atSlot => if atSlot = slot then image else media atSlot

-- A complete checked replacement dominates the surviving image. A torn write
-- or later detectable tear makes a slot ineligible. Restart can choose either
-- valid slot, so local safety is independent of which generation survived.
inductive Step : Media Command → Media Command → Prop
  | write {media : Media Command} (slot : Bool) {surviving next : Image Command}
      (valid : media (!slot) = some surviving) (advances : next.Dominates surviving) :
      Step media (replace media slot (some next))
  | tear (media : Media Command) (slot : Bool) : Step media (replace media slot none)
  | restart (media : Media Command) : Step media media

inductive Reachable (initial : Media Command) : Media Command → Prop
  | start : Reachable initial initial
  | next {before after} : Reachable initial before → Step before after → Reachable initial after

def Keeps (floor : Image Command) (media : Media Command) : Prop :=
  ∀ slot image, media slot = some image → image.Dominates floor

private theorem step_keeps {floor : Image Command} {before after : Media Command}
    (keeps : Keeps floor before) (step : Step before after) : Keeps floor after := by
  intro slot image selected
  cases step with
  | write other valid advances =>
      by_cases same : slot = other
      · subst slot
        simp [replace] at selected
        subst image
        exact dominates_trans advances (keeps _ _ valid)
      · exact keeps slot image (by simpa [replace, same] using selected)
  | tear torn =>
      by_cases same : slot = torn
      · simp [replace, same] at selected
      · exact keeps slot image (by simpa [replace, same] using selected)
  | restart => exact keeps slot image selected

theorem any_surviving_slot_keeps_the_acknowledged_rank {ack : Image Command} {now : Media Command}
    (trace : Reachable (mirrored ack) now) : Keeps ack now := by
  induction trace with
  | start =>
      intro slot image selected
      have equal : ack = image := by simpa [mirrored] using selected
      exact equal ▸ dominates_refl ack
  | next _ step prior => exact step_keeps prior step

theorem a_torn_slot_cannot_reopen_an_older_ballot {ack current : Image Command}
    {now : Media Command} {slot : Bool} (trace : Reachable (mirrored ack) now)
    (eligible : now slot = some current) {ballot : Nat} (stale : ballot < ack.promised) :
    ballot < current.promised :=
  Nat.lt_of_lt_of_le stale ((any_surviving_slot_keeps_the_acknowledged_rank trace) _ _ eligible).1

def DurableReports (ledger : Ledger Voter Command) : Prop :=
  ∀ ballot voter, voter ∈ ledger.members → ledger.prepared ballot voter = true →
    ∀ vote, ledger.voted voter vote → vote.ballot < ballot →
      ∃ ack now slot observed,
        ack.accepted = some vote ∧ Reachable (mirrored ack) now ∧
        now slot = some observed ∧ observed.accepted = ledger.report ballot voter

theorem any_later_ranked_recovery_selects_the_fence {ledger : Ledger Voter Command}
    (rules : BallotRules ledger) (durable : DurableReports ledger)
    {fenceBallot recoverBallot : Nat} {fence : List Command}
    (chosen : Chosen ledger fenceBallot fence) (later : fenceBallot < recoverBallot)
    (recovery : ledger.active recoverBallot) : fence <+: seed ledger recoverBallot := by
  have coverage : ReplyCoverage ledger := by
    intro ballot voter member prepared vote voted earlier
    obtain ⟨ack, now, slot, observed, held, trace, selected, report⟩ :=
      durable ballot voter member prepared vote voted earlier
    obtain ⟨current, exactVote, rank⟩ :=
      ((any_surviving_slot_keeps_the_acknowledged_rank trace) slot observed selected).2 vote held
    exact ⟨current, report.symm.trans exactVote, rank⟩
  exact later_ballot_inherits_chosen_prefix ⟨rules, coverage⟩ chosen recoverBallot later recovery

-- Study 106's installed-basis rule applies to every authenticated vote of
-- the installed cohort. A ranked selection uses one of the reported votes.
structure CohortRecovery (Voter : Type) (installed recovered : List Command) where
  members : List Voter
  eligible : Voter → Bool
  majority : Majority members eligible
  report : Voter → Vote Command
  seeded : ∀ voter ∈ members, eligible voter = true → installed <+: (report voter).history
  winner : Voter
  member : winner ∈ members
  answered : eligible winner = true
  greatest : ∀ voter ∈ members, eligible voter = true → RankLE (report voter) (report winner)
  selection : recovered = (report winner).history

theorem recovered_prefix_extends_the_installed_basis {installed recovered : List Command}
    (recovery : CohortRecovery Voter installed recovered) : installed <+: recovered := by
  rw [recovery.selection]
  exact recovery.seeded recovery.winner recovery.member recovery.answered

inductive InstalledAfter (Voter : Type) (basis : List Command) : List Command → Prop
  | first : InstalledAfter Voter basis basis
  | repair {before after} : InstalledAfter Voter basis before →
      CohortRecovery Voter before after → InstalledAfter Voter basis after

private theorem repair_keeps_basis {basis installed : List Command}
    (repairs : InstalledAfter Voter basis installed) : basis <+: installed := by
  induction repairs with
  | first => exact List.prefix_rfl
  | repair _ recovery prior =>
    exact prior.trans (recovered_prefix_extends_the_installed_basis recovery)

theorem a_repaired_ranked_majority_keeps_the_original_fence {ledger : Ledger Voter Command}
    (rules : BallotRules ledger) (durable : DurableReports ledger)
    {fenceBallot sealBallot : Nat} {fence : List Command}
    (chosen : Chosen ledger fenceBallot fence) (sealLater : fenceBallot < sealBallot)
    (sealing : ledger.active sealBallot) {installed recovered : List Command}
    (repairs : InstalledAfter Voter (seed ledger sealBallot) installed)
    (currentRecovery : CohortRecovery Voter installed recovered) : fence <+: recovered := by
  have sealBasis := any_later_ranked_recovery_selects_the_fence rules durable chosen sealLater sealing
  exact sealBasis.trans
    ((repair_keeps_basis repairs).trans (recovered_prefix_extends_the_installed_basis currentRecovery))

def beforeFence : Image Nat := ⟨1, some ⟨1, [0]⟩⟩

def atFence : Image Nat := ⟨6, some ⟨6, [0, 1]⟩⟩

theorem changed_majority_and_selected_slot_tear_are_reachable :
    Majority [0, 1, 2] (fun voter : Nat => voter != 1) ∧
    Majority [0, 1, 2] (fun voter : Nat => voter != 0) ∧
    ∃ pair now, Reachable (mirrored beforeFence) pair ∧ pair = mirrored atFence ∧
      Step pair now ∧ now true = none ∧ now false = some atFence := by
  let first := replace (mirrored beforeFence) true (some atFence)
  let pair := replace first false (some atFence)
  have advances : atFence.Dominates beforeFence := by
    refine ⟨by decide, ?_⟩
    intro vote held
    simp [beforeFence] at held
    subst vote
    exact ⟨⟨6, [0, 1]⟩, rfl, ⟨by decide, by decide⟩⟩
  have paired : Reachable (mirrored beforeFence) pair :=
    .next (.next .start (.write true rfl advances)) (.write false rfl (dominates_refl _))
  refine ⟨by unfold Majority; decide, by unfold Majority; decide, pair, replace pair true none,
    paired, ?_, .tear _ _, rfl, rfl⟩
  funext slot
  cases slot <;> rfl

#print axioms any_surviving_slot_keeps_the_acknowledged_rank
#print axioms a_torn_slot_cannot_reopen_an_older_ballot
#print axioms any_later_ranked_recovery_selects_the_fence
#print axioms recovered_prefix_extends_the_installed_basis
#print axioms a_repaired_ranked_majority_keeps_the_original_fence
#print axioms changed_majority_and_selected_slot_tear_are_reachable

end Logkeeper.SelectionFence
