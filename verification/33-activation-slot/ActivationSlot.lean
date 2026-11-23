import ConfigurationClosure

set_option warningAsError true

namespace ActivationSlot

open PrefixAgreement JournalRefinement

variable {Voter Seed : Type}

def Decided (ledger : Ledger Voter Seed) (ballot : Nat) (seed : Seed) : Prop :=
  Chosen ledger ballot [seed]

theorem seed_certificates_agree {ledger : Ledger Voter Seed} (rules : Rules ledger)
    {first second : Nat} {left right : Seed}
    (firstProof : Decided ledger first left) (secondProof : Decided ledger second right) :
    left = right :=
  any_two_certificates_agree_at_position rules firstProof secondProof
    (position := 0) rfl rfl

theorem no_hidden_earlier_choice_when_all_prepare_reports_are_empty
    {ledger : Ledger Voter Seed} (rules : Rules ledger) {earlier next : Nat}
    (ordered : earlier < next) (opened : ledger.active next)
    (empty : ∀ v ∈ ledger.members, ledger.prepared next v = true → ledger.report next v = none)
    (seed : Seed) : ¬ Decided ledger earlier seed := by
  intro choice
  obtain ⟨yes, written, evidence⟩ := choice
  obtain ⟨voter, member, voted, prepared⟩ := majorities_overlap ledger.members yes
    (ledger.prepared next) written (rules.prepares next opened)
  obtain ⟨actual, accepted, sameBallot, _⟩ := evidence voter member voted
  obtain ⟨report, reported, _⟩ :=
    rules.replyCoverage next voter member prepared actual accepted (sameBallot.symm ▸ ordered)
  rw [empty voter member prepared] at reported
  cases reported

theorem every_later_acceptance_of_the_slot_uses_its_chosen_seed
    {ledger : Ledger Voter Seed} (rules : Rules ledger)
    {chosenAt : Nat} {chosenSeed laterSeed : Seed} (choice : Decided ledger chosenAt chosenSeed)
    {voter : Voter} {vote : Vote Seed} (accepted : ledger.voted voter vote)
    (ordered : chosenAt ≤ vote.ballot) (exactSeed : vote.history = [laterSeed]) :
    chosenSeed = laterSeed := by
  have includes : [chosenSeed] <+: vote.history := by
    by_cases same : chosenAt = vote.ballot
    · have issued := chosen_is_prefix_of_issued rules choice
      exact List.prefix_of_prefix_length_le
        (same ▸ issued) (rules.chain voter vote accepted).2.2 (by simp [exactSeed])
    · have later : chosenAt < vote.ballot := by omega
      have held := rules.chain voter vote accepted
      exact (later_ballot_inherits_chosen_prefix rules choice vote.ballot later held.1).trans held.2.1
  rw [exactSeed] at includes
  simpa using includes.eq_of_length (by rfl)

structure Device (Seed : Type) where
  acceptor : DurableAcceptor.State Seed
  resident : Seed → Prop

def emptyDevice : Device Seed := ⟨DurableAcceptor.initial, fun _ => False⟩
def LatestBinds (state : Device Seed) (seed : Seed) : Prop :=
  ∃ vote, state.acceptor.latest = some vote ∧ vote.history = [seed]
def MayAccept (state : Device Seed) (seed : Seed) : Prop := state.resident seed
def MayCollect (state : Device Seed) (seed : Seed) : Prop := ¬ LatestBinds state seed

def slotVote (ballot : Nat) (seed : Seed) : Vote Seed := ⟨ballot, [seed]⟩

inductive Step : Device Seed → Device Seed → Prop
  | stage {state} (seed : Seed) :
      Step state {state with resident := fun item => state.resident item ∨ item = seed}
  | prepare {state} (ballot : Nat) (newer : state.acceptor.promised < ballot) :
      Step state {state with acceptor := DurableAcceptor.promise state.acceptor ballot}
  | accept {state} (ballot : Nat) (seed : Seed) (promised : state.acceptor.promised ≤ ballot)
      (keepsRank : ∀ old, state.acceptor.latest = some old → RankLE old (slotVote ballot seed))
      (backed : MayAccept state seed) :
      Step state {state with acceptor := DurableAcceptor.acceptVote state.acceptor (slotVote ballot seed)}
  | collect {state} (seed : Seed) (allowed : MayCollect state seed) :
      Step state {state with resident := fun item => state.resident item ∧ item ≠ seed}
  | restart {state} : Step state state

inductive Reachable : Device Seed → Prop
  | initial : Reachable emptyDevice
  | next {first last} : Reachable first → Step first last → Reachable last

structure Sound (state : Device Seed) : Prop where
  ranks : DurableAcceptor.Sound state.acceptor
  exact : ∀ vote, state.acceptor.latest = some vote → ∃ seed, vote.history = [seed]
  backing : ∀ seed, LatestBinds state seed → state.resident seed

theorem device_steps_preserve_exact_backing {before after : Device Seed}
    (sound : Sound before) (step : Step before after) : Sound after := by
  cases step with
  | stage staged =>
      exact ⟨sound.ranks, sound.exact, fun seed bound => Or.inl (sound.backing seed bound)⟩
  | prepare ballot permitted =>
      exact ⟨DurableAcceptor.every_step_preserves_durable_replies sound.ranks (.prepare ballot permitted),
        sound.exact, sound.backing⟩
  | accept ballot seed promised rank backed =>
      refine ⟨DurableAcceptor.every_step_preserves_durable_replies sound.ranks
        (.accept (slotVote ballot seed) promised rank), ?_, ?_⟩
      · intro vote selected
        change some (slotVote ballot seed) = some vote at selected
        obtain rfl := Option.some.inj selected
        exact ⟨seed, rfl⟩
      · intro item bound
        obtain ⟨vote, selected, image⟩ := bound
        change some (slotVote ballot seed) = some vote at selected
        obtain rfl := Option.some.inj selected
        have same : seed = item := by simpa [slotVote] using image
        subst item
        exact backed
  | collect obsolete allowed =>
      refine ⟨sound.ranks, sound.exact, fun seed bound => ⟨sound.backing seed bound, ?_⟩⟩
      intro aliases
      have unbound : ¬ LatestBinds before obsolete := by
        exact allowed
      exact unbound (aliases ▸ bound)
  | restart => exact sound

theorem requests_cannot_destroy_a_required_exact_image {state : Device Seed}
    (history : Reachable state) : Sound state := by
  induction history with
  | initial =>
      refine ⟨DurableAcceptor.initial_sound, ?_, ?_⟩
      · simp [emptyDevice, DurableAcceptor.initial]
      · simp [LatestBinds, emptyDevice, DurableAcceptor.initial]
  | next _ step prior => exact device_steps_preserve_exact_backing prior step

theorem higher_promise_keeps_the_accepted_image {before : Device Seed} {seed : Seed}
    (reachable : Reachable before) (bound : LatestBinds before seed)
    (ballot : Nat) (mayPrepare : before.acceptor.promised < ballot) :
    ∃ after, Step before after ∧ LatestBinds after seed ∧ ¬ MayCollect after seed ∧ after.resident seed := by
  refine ⟨{before with acceptor := DurableAcceptor.promise before.acceptor ballot},
    .prepare ballot mayPrepare, bound, ?_, (requests_cannot_destroy_a_required_exact_image reachable).backing seed bound⟩
  exact fun allowed => allowed bound

theorem every_recovery_majority_can_read_a_previously_chosen_seed
    {ledger : Ledger Voter Seed} (rules : Rules ledger)
    (devices : Voter → Device Seed)
    (reached : ∀ v ∈ ledger.members, Reachable (devices v))
    (recorded : ∀ v ∈ ledger.members, ∀ vote, ledger.voted v vote → (devices v).acceptor.votes vote)
    (certified : ∀ v ∈ ledger.members, ∀ vote, (devices v).acceptor.latest = some vote → ledger.voted v vote)
    (reachable : Voter → Bool) (recovery : Majority ledger.members reachable)
    {chosenAt : Nat} {seed : Seed} (choice : Decided ledger chosenAt seed) :
    ∃ v ∈ ledger.members, reachable v = true ∧ LatestBinds (devices v) seed ∧ (devices v).resident seed := by
  obtain ⟨writes, written, evidence⟩ := choice
  obtain ⟨v, member, canRead, wrote⟩ :=
    majorities_overlap ledger.members reachable writes recovery written
  obtain ⟨past, accepted, oldBallot, _⟩ := evidence v member wrote
  have sound := requests_cannot_destroy_a_required_exact_image (reached v member)
  obtain ⟨latest, selected, dominates⟩ := sound.ranks.dominates past (recorded v member past accepted)
  obtain ⟨value, exactValue⟩ := sound.exact latest selected
  have same := every_later_acceptance_of_the_slot_uses_its_chosen_seed rules
    ⟨writes, written, evidence⟩ (certified v member latest selected) (oldBallot ▸ dominates.1) exactValue
  subst value
  have bound : LatestBinds (devices v) seed := ⟨latest, selected, exactValue⟩
  exact ⟨v, member, canRead, bound, sound.backing seed bound⟩

def CanPublish (ledger : Ledger Voter Seed) (ballot : Nat) (seed : Seed) : Prop :=
  Decided ledger ballot seed

inductive Publication (ledger : Ledger Voter Seed) : Option Seed → Option Seed → Prop
  | initial : Publication ledger none none
  | lostReply {state : Option Seed} (history : Publication ledger none state) :
      Publication ledger none none
  | publish {state : Option Seed} (history : Publication ledger none state) (ballot : Nat) (seed : Seed)
      (certificate : CanPublish ledger ballot seed) :
      Publication ledger none (some seed)

theorem published_seed_requires_exact_choice {ledger : Ledger Voter Seed} {seed : Seed}
    (history : Publication ledger none (some seed)) : ∃ ballot, Decided ledger ballot seed := by
  cases history
  rename_i ballot accepted
  have valid : Decided ledger ballot seed := by
    exact accepted
  exact ⟨ballot, valid⟩

theorem recovery_after_a_lost_reply_cannot_publish_a_different_seed
    {ledger : Ledger Voter Seed} (rules : Rules ledger) {first second : Seed}
    (before : Publication ledger none (some first)) (after : Publication ledger none (some second)) :
    first = second := by
  obtain ⟨_, originally⟩ := published_seed_requires_exact_choice before
  obtain ⟨_, reconciled⟩ := published_seed_requires_exact_choice after
  exact seed_certificates_agree rules originally reconciled

def ReplaysRecovered (decoded recovered : List Command) : Prop := decoded = recovered

theorem published_activation_preserves_old_choices_at_every_recovery_majority
    {Command : Type} (source : ConfigurationClosure.Generation Voter Command)
    (cut : ConfigurationClosure.Certificate Voter Command)
    (ranked : ConfigurationClosure.Ranked source.ledger cut)
    (covers : ConfigurationClosure.CoversEveryVote source.ledger cut)
    {target : Ledger Voter Seed} (rules : Rules target)
    (devices : Voter → Device Seed)
    (reached : ∀ v ∈ target.members, Reachable (devices v))
    (recorded : ∀ v ∈ target.members, ∀ vote, target.voted v vote → (devices v).acceptor.votes vote)
    (certified : ∀ v ∈ target.members, ∀ vote, (devices v).acceptor.latest = some vote → target.voted v vote)
    (available : Voter → Bool) (recovery : Majority target.members available)
    {seed : Seed} (published : Publication target none (some seed))
    (decode : Seed → List Command)
    (exactImage : ReplaysRecovered (decode seed) (ConfigurationClosure.Recovered source.basis cut))
    {earlier : Nat} {history : List Command} (oldChoice : Chosen source.ledger earlier history) :
    ∃ v ∈ target.members, available v = true ∧ (devices v).resident seed ∧ history <+: decode seed := by
  obtain ⟨_, chosen⟩ := published_seed_requires_exact_choice published
  obtain ⟨v, member, online, _, image⟩ :=
    every_recovery_majority_can_read_a_previously_chosen_seed rules devices reached recorded certified
      available recovery chosen
  refine ⟨v, member, online, image, ?_⟩
  have sameImage : decode seed = ConfigurationClosure.Recovered source.basis cut := by
    exact exactImage
  rw [sameImage]
  exact ConfigurationClosure.ranked_cut_covers_every_old_quorum_even_if_learned_late
    source.rules ranked covers source.basis oldChoice

#print axioms seed_certificates_agree
#print axioms no_hidden_earlier_choice_when_all_prepare_reports_are_empty
#print axioms every_later_acceptance_of_the_slot_uses_its_chosen_seed
#print axioms device_steps_preserve_exact_backing
#print axioms requests_cannot_destroy_a_required_exact_image
#print axioms higher_promise_keeps_the_accepted_image
#print axioms every_recovery_majority_can_read_a_previously_chosen_seed
#print axioms published_seed_requires_exact_choice
#print axioms recovery_after_a_lost_reply_cannot_publish_a_different_seed
#print axioms published_activation_preserves_old_choices_at_every_recovery_majority

end ActivationSlot
