import JournalRotation
import ConfigurationClosure
import ScopeProtection

set_option warningAsError true

namespace OrderedFaultInterval

structure Cut where
  lineage : Nat
  frontier : Nat
  voters : Nat
  custody : Nat
  deriving DecidableEq

structure Interval (Zone : Type) where
  start : Nat
  loss : Option Zone
  deriving DecidableEq

structure Image (Zone : Type) where
  cut : Cut
  interval : Interval Zone
  deriving DecidableEq

structure Confirmation (Zone : Type) where
  lineage : Nat
  start : Nat
  lost : Zone

structure Renewal where
  expected : Cut
  start : Nat

structure Rules (Zone Proof : Type) where
  confirms : Confirmation Zone → Proof → Prop
  qualifies : Renewal → Proof → Prop

inductive Frame (Zone Proof : Type) where
  | confirm (ticket : Confirmation Zone) (proof : Proof)
  | renew (ticket : Renewal) (proof : Proof)
  | voters (revision : Nat)
  | custody (revision : Nat)
  | committed

variable {Zone Proof Voter : Type} [DecidableEq Zone]

def nextCut (before : Image Zone) : Cut :=
  { before.cut with frontier := before.cut.frontier + 1 }

def SameInterval (before : Image Zone) (ticket : Confirmation Zone) : Prop :=
  ticket.lineage = before.cut.lineage ∧ ticket.start = before.interval.start

def SameRenewalBasis (before : Image Zone) (ticket : Renewal) : Prop :=
  ticket.expected = before.cut ∧ ticket.start = before.interval.start

def Credible (interval : Interval Zone) (lost : Zone) : Prop :=
  ∀ prior, interval.loss = some prior → lost = prior

-- The proof relations verify the inline evidence under its historical rules.
-- The voters and custody frames project already authorized changes, not requests to make them.
noncomputable def apply (rules : Rules Zone Proof) (before : Image Zone) :
    Frame Zone Proof → Option (Image Zone) := by
  classical
  let cut := nextCut before
  exact fun frame => match frame with
  | .confirm ticket proof =>
    if SameInterval before ticket ∧ (before.interval.loss = none ∨ before.interval.loss = some ticket.lost) ∧
        rules.confirms ticket proof then
      some ⟨cut, { before.interval with loss := some ticket.lost }⟩
    else none
  | .renew ticket proof =>
    if SameRenewalBasis before ticket ∧ before.interval.loss.isSome = true ∧ rules.qualifies ticket proof then
      some ⟨cut, ⟨cut.frontier, none⟩⟩
    else none
  | .voters revision =>
    if before.cut.voters < revision then some ⟨{ cut with voters := revision }, before.interval⟩
    else none
  | .custody revision =>
    if before.cut.custody < revision then some ⟨{ cut with custody := revision }, before.interval⟩
    else none
  | .committed => some ⟨cut, before.interval⟩

theorem a_confirmation_matches_the_live_interval (rules : Rules Zone Proof) (before after : Image Zone)
    (ticket : Confirmation Zone) (proof : Proof)
    (accepted : apply rules before (.confirm ticket proof) = some after) :
    ticket.lineage = before.cut.lineage ∧ ticket.start = before.interval.start ∧
    (before.interval.loss = none ∨ before.interval.loss = some ticket.lost) ∧
    rules.confirms ticket proof ∧ after.interval = ⟨before.interval.start, some ticket.lost⟩ := by
  simp only [apply] at accepted
  split at accepted
  · next verified =>
    cases accepted
    exact ⟨verified.1.1, verified.1.2, verified.2.1, verified.2.2, rfl⟩
  · cases accepted

theorem a_renewal_uses_the_exact_current_basis (rules : Rules Zone Proof) (before after : Image Zone)
    (ticket : Renewal) (proof : Proof)
    (accepted : apply rules before (.renew ticket proof) = some after) :
    ticket.expected = before.cut ∧ ticket.start = before.interval.start ∧
    before.interval.loss.isSome = true ∧ rules.qualifies ticket proof ∧
    after.interval = ⟨before.cut.frontier + 1, none⟩ := by
  simp only [apply] at accepted
  split at accepted
  · next verified =>
    cases accepted
    exact ⟨verified.1.1, verified.1.2, verified.2.1, verified.2.2, rfl⟩
  · cases accepted

theorem a_renewal_rejects_any_changed_frontier_voters_or_custody
    (rules : Rules Zone Proof) (before : Image Zone) (ticket : Renewal) (proof : Proof)
    (stale : ticket.expected ≠ before.cut) :
    apply rules before (.renew ticket proof) = none := by
  simp only [apply]
  split
  · next verified => exact False.elim (stale verified.1.1)
  · rfl

theorem changing_voters_alone_keeps_the_interval
    (rules : Rules Zone Proof) (before : Image Zone) (revision : Nat) (newer : before.cut.voters < revision) :
    apply rules before (.voters revision) = some ⟨{ nextCut before with voters := revision }, before.interval⟩ := by
  simp [apply, newer]

theorem a_replacement_can_use_the_original_incident_ticket (rules : Rules Zone Proof)
    (before : Image Zone) (revision : Nat) (ticket : Confirmation Zone) (proof : Proof)
    (replaced : before.cut.voters < revision)
    (same : SameInterval before ticket)
    (compatible : before.interval.loss = none ∨ before.interval.loss = some ticket.lost)
    (authentic : rules.confirms ticket proof) :
    ∃ next after, apply rules before (.voters revision) = some next ∧
      apply rules next (.confirm ticket proof) = some after ∧
      after.interval = ⟨before.interval.start, some ticket.lost⟩ := by
  let next : Image Zone := ⟨{ nextCut before with voters := revision }, before.interval⟩
  have stillMatches : SameInterval next ticket := same
  refine ⟨next, ⟨nextCut next, ⟨before.interval.start, some ticket.lost⟩⟩, ?_, ?_, rfl⟩
  · exact changing_voters_alone_keeps_the_interval rules before revision replaced
  · simp [apply, next, stillMatches, compatible, authentic]

theorem renewal_never_reopens_an_old_incident_ticket
    (rules : Rules Zone Proof) (before after : Image Zone)
    (ticket : Renewal) (old : Confirmation Zone) (proof oldProof : Proof)
    (wasCurrent : old.start = before.interval.start) (ordered : before.interval.start ≤ before.cut.frontier)
    (accepted : apply rules before (.renew ticket proof) = some after) :
    apply rules after (.confirm old oldProof) = none := by
  have advanced := (a_renewal_uses_the_exact_current_basis rules before after ticket proof accepted).2.2.2.2
  cases result : apply rules after (.confirm old oldProof) with
  | none => rfl
  | some state =>
    have exactStart := (a_confirmation_matches_the_live_interval rules after state old oldProof result).2.1
    have impossible := exactStart.trans (congrArg Interval.start advanced)
    change old.start = before.cut.frontier + 1 at impossible
    omega

theorem chosen_renewal_lifts_to_full_coverage {Input : Type}
    (rules : Rules Zone Proof) (before after : Image Zone) (ticket : Renewal) (proof : Proof)
    (owed : Input → Prop) (copies : Input → Zone → Prop) (eligible : Zone → Prop)
    (verify : ticket.expected = before.cut → rules.qualifies ticket proof →
      ScopeProtection.CanRenew eligible owed copies)
    (accepted : apply rules before (.renew ticket proof) = some after)
    (zone : Zone) :
    Credible after.interval zone ∧ eligible zone ∧
      (∀ input, owed input → ScopeProtection.Coverage copies input zone) := by
  obtain ⟨sameCut, _, _, valid, advanced⟩ :=
    a_renewal_uses_the_exact_current_basis rules before after ticket proof accepted
  refine ⟨?_, ScopeProtection.renewal_restores_both_readiness_and_protection (verify sameCut valid) zone⟩
  rw [advanced]
  simp [Credible]

noncomputable def replay (rules : Rules Zone Proof) (origin : Image Zone) (frames : List (Frame Zone Proof)) :
    Option (Image Zone) :=
  frames.foldlM (apply rules) origin

private theorem each_frame_preserves_interval_order
    (rules : Rules Zone Proof) (before after : Image Zone) (frame : Frame Zone Proof)
    (ordered : before.interval.start ≤ before.cut.frontier)
    (accepted : apply rules before frame = some after) :
    before.interval.start ≤ after.interval.start ∧ after.interval.start ≤ after.cut.frontier := by
  cases frame <;> simp only [apply] at accepted
  all_goals
    first
    | split at accepted <;> first
      | cases accepted
        simp only [nextCut, Nat.le_refl, true_and, and_true]
        omega
      | contradiction
    | cases accepted
      simp only [nextCut, Nat.le_refl, true_and]
      omega

theorem replay_never_reuses_an_older_interval
    (rules : Rules Zone Proof) (origin after : Image Zone) (frames : List (Frame Zone Proof))
    (ordered : origin.interval.start ≤ origin.cut.frontier)
    (applied : replay rules origin frames = some after) :
    origin.interval.start ≤ after.interval.start ∧ after.interval.start ≤ after.cut.frontier := by
  induction frames generalizing origin with
  | nil =>
    change some origin = some after at applied
    cases applied
    exact ⟨Nat.le_refl _, ordered⟩
  | cons frame suffix ih =>
    simp only [replay, List.foldlM_cons] at applied
    cases firstStep : apply rules origin frame with
    | none => simp [firstStep] at applied
    | some next =>
      obtain ⟨monotone, inside⟩ :=
        each_frame_preserves_interval_order rules origin next frame ordered firstStep
      have rest : replay rules next suffix = some after := by simpa [replay, firstStep] using applied
      obtain ⟨later, stillInside⟩ := ih next inside rest
      exact ⟨Nat.le_trans monotone later, stillInside⟩

theorem proceed_after_exact_prefix (rules : Rules Zone Proof) (origin checkpoint : Image Zone)
    (prefixFrames suffix : List (Frame Zone Proof)) (exactBase : replay rules origin prefixFrames = some checkpoint) :
    replay rules origin (prefixFrames ++ suffix) = replay rules checkpoint suffix := by
  simp only [replay] at exactBase
  simp only [replay, List.foldlM_append, exactBase]
  rfl

theorem each_crash_selector_recovers_the_exact_interval
    (rules : Rules Zone Proof) (origin checkpoint applied : Image Zone)
    (current : JournalRotation.State (Frame Zone Proof)) (view : JournalRotation.View)
    (safe : JournalRotation.Safe current) (tracked : JournalRotation.TracksNamespace current)
    (selected : current.namespaceChoices view)
    (certified : replay rules origin (current.history.take view.cut) = some checkpoint)
    (chosen : replay rules origin current.history = some applied) :
    ∃ suffix, replay rules checkpoint suffix = some applied ∧
      ∀ offset frame, suffix[offset]? = some frame →
        current.media (.tail (view.cut + offset)) = some [frame] := by
  obtain ⟨_, _, storedTail⟩ :=
    JournalRotation.selectable_has_exact_cut safe ((tracked view).mp selected)
  refine ⟨current.history.drop view.cut, ?_, ?_⟩
  · rwa [← proceed_after_exact_prefix rules origin checkpoint _ _ certified, List.take_append_drop]
  · intro offset frame atTail
    rw [List.getElem?_drop] at atTail
    exact storedTail _ _ (Nat.le_add_right _ _) atTail

theorem every_later_recovery_quorum_has_the_chosen_incident_prefix
    {before next current : ConfigurationClosure.Generation Voter (Frame Zone Proof)}
    (handoff : ConfigurationClosure.Handoff before next)
    (later : ConfigurationClosure.Changes next current)
    (installed : ConfigurationClosure.InstalledOnQuorum current)
    (available : Voter → Bool) (quorum : JournalRefinement.Majority current.ledger.members available)
    {ballot : Nat} {prefixFrames : List (Frame Zone Proof)}
    (chosen : PrefixAgreement.Chosen before.ledger ballot prefixFrames)
    (rules : Rules Zone Proof) (origin afterPrefix after : Image Zone)
    (applied : replay rules origin prefixFrames = some afterPrefix)
    (currentApplied : replay rules origin current.basis = some after) :
    ∃ voter ∈ current.ledger.members, available voter = true ∧ current.installed voter current.basis ∧
      ∃ suffix, current.basis = prefixFrames ++ suffix ∧ replay rules afterPrefix suffix = some after := by
  obtain ⟨voter, member, online, holds, reaches⟩ :=
    ConfigurationClosure.earlier_choice_reaches_any_later_recovery_majority handoff later
      installed available quorum chosen
  obtain ⟨suffix, splitBasis⟩ := reaches
  refine ⟨voter, member, online, holds, suffix, splitBasis.symm, ?_⟩
  rw [← splitBasis, proceed_after_exact_prefix rules origin afterPrefix _ _ applied] at currentApplied
  exact currentApplied

theorem a_current_majority_and_its_crash_selector_recover_the_chosen_interval
    {before next current : ConfigurationClosure.Generation Voter (Frame Zone Proof)}
    (handoff : ConfigurationClosure.Handoff before next) (later : ConfigurationClosure.Changes next current)
    (installed : ConfigurationClosure.InstalledOnQuorum current)
    (available : Voter → Bool) (quorum : JournalRefinement.Majority current.ledger.members available)
    {ballot : Nat} {prefixFrames : List (Frame Zone Proof)}
    (chosen : PrefixAgreement.Chosen before.ledger ballot prefixFrames)
    (rules : Rules Zone Proof) (origin afterPrefix after : Image Zone)
    (applied : replay rules origin prefixFrames = some afterPrefix)
    (currentApplied : replay rules origin current.basis = some after)
    (media : Voter → JournalRotation.State (Frame Zone Proof))
    (covers : ∀ voter ∈ current.ledger.members, available voter = true →
      current.installed voter current.basis →
      (media voter).history = current.basis ∧
      JournalRotation.Safe (media voter) ∧ JournalRotation.TracksNamespace (media voter)) :
    ∃ voter ∈ current.ledger.members, available voter = true ∧ current.installed voter current.basis ∧
      (∀ view checkpoint, (media voter).namespaceChoices view →
        replay rules origin (current.basis.take view.cut) = some checkpoint →
        ∃ suffix, replay rules checkpoint suffix = some after ∧
          ∀ offset frame, suffix[offset]? = some frame →
            (media voter).media (.tail (view.cut + offset)) = some [frame]) := by
  obtain ⟨voter, member, online, holds, _, _, _⟩ :=
    every_later_recovery_quorum_has_the_chosen_incident_prefix handoff later installed available
      quorum chosen rules origin afterPrefix after applied currentApplied
  obtain ⟨exact, safe, tracked⟩ := covers voter member online holds
  refine ⟨voter, member, online, holds, ?_⟩
  intro view checkpoint selected certified
  exact each_crash_selector_recovers_the_exact_interval rules origin checkpoint after (media voter)
    view safe tracked selected (by rwa [exact]) (by rwa [exact])

#print axioms a_confirmation_matches_the_live_interval
#print axioms a_renewal_uses_the_exact_current_basis
#print axioms a_renewal_rejects_any_changed_frontier_voters_or_custody
#print axioms changing_voters_alone_keeps_the_interval
#print axioms a_replacement_can_use_the_original_incident_ticket
#print axioms renewal_never_reopens_an_old_incident_ticket
#print axioms chosen_renewal_lifts_to_full_coverage
#print axioms replay_never_reuses_an_older_interval
#print axioms proceed_after_exact_prefix
#print axioms each_crash_selector_recovers_the_exact_interval
#print axioms every_later_recovery_quorum_has_the_chosen_incident_prefix

#print axioms a_current_majority_and_its_crash_selector_recover_the_chosen_interval

end OrderedFaultInterval
