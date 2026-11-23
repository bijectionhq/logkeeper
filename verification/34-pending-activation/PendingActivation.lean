import ConfigurationClosure

set_option warningAsError true

namespace PendingActivation

open PrefixAgreement JournalRefinement

structure Ticket (Image : Type) where
  attempt : Nat
  intent : Nat
  revision : Nat
  image : Image
  deriving DecidableEq

inductive Holding (Image : Type) where
  | absent
  | ready (ticket : Ticket Image)
  | spent
  deriving DecidableEq

structure State (Image : Type) where
  revision : Nat
  intent : Nat
  attempts : Nat → Holding Image
  installed : Option (Ticket Image)

inductive Command (Image : Type) where
  | register (ticket : Ticket Image)
  | activate (ticket : Ticket Image)
  | discard (ticket : Ticket Image)
  | replace (revision : Nat)

inductive Outcome (Image : Type) where
  | registered
  | activated (ticket : Ticket Image)
  | discarded
  | replaced
  | refused

variable {Image Voter : Type}

def InOrderedScope (state : State Image) (ticket : Ticket Image) : Prop :=
  ticket.intent = state.intent ∧ ticket.revision = state.revision

def CurrentGrant (state : State Image) (ticket : Ticket Image) : Prop :=
  state.attempts ticket.attempt = .ready ticket

def MayActivate (state : State Image) (ticket : Ticket Image) : Prop :=
  InOrderedScope state ticket ∧ CurrentGrant state ticket ∧ state.installed = none

def put (table : Nat → Holding Image) (id : Nat) (holding : Holding Image) : Nat → Holding Image :=
  fun queried => if queried = id then holding else table queried

noncomputable def apply (state : State Image) (command : Command Image) : State Image × Outcome Image := by
  classical
  exact match command with
  | .register ticket =>
      if InOrderedScope state ticket ∧ state.installed = none ∧ state.attempts ticket.attempt = .absent
      then ({state with attempts := put state.attempts ticket.attempt (.ready ticket)}, .registered)
      else (state, .refused)
  | .activate ticket =>
      if MayActivate state ticket then ({state with installed := some ticket}, .activated ticket)
      else (state, .refused)
  | .discard ticket =>
      if CurrentGrant state ticket ∧ state.installed ≠ some ticket
      then ({state with attempts := put state.attempts ticket.attempt .spent}, .discarded)
      else (state, .refused)
  | .replace revision =>
      if state.revision < revision then ({state with revision := revision}, .replaced)
      else (state, .refused)

theorem activation_checks_the_ordered_scope_and_exact_live_grant
    {state : State Image} {ticket accepted : Ticket Image}
    (success : (apply state (.activate ticket)).2 = .activated accepted) :
    accepted = ticket ∧ ticket.intent = state.intent ∧ ticket.revision = state.revision ∧
    state.attempts ticket.attempt = .ready ticket ∧ state.installed = none := by
  classical
  by_cases allowed : MayActivate state ticket
  · have scope : ticket.intent = state.intent ∧ ticket.revision = state.revision := by
      exact allowed.1
    have live : state.attempts ticket.attempt = .ready ticket := by
      exact allowed.2.1
    have same : ticket = accepted := by simpa [apply, allowed] using success
    exact ⟨same.symm, scope.1, scope.2, live, allowed.2.2⟩
  · simp [apply, allowed] at success

private theorem refused_activation_preserves_state (state : State Image) (ticket : Ticket Image)
    (denied : ¬ MayActivate state ticket) :
    apply state (.activate ticket) = (state, .refused) := by
  simp [apply, denied]

theorem a_delayed_packet_for_an_earlier_revision_is_refused
    {state : State Image} {ticket : Ticket Image} (stale : ticket.revision ≠ state.revision) :
    apply state (.activate ticket) = (state, .refused) := by
  have required : ¬ MayActivate state ticket := by
    intro possible
    have success : (apply state (.activate ticket)).2 = .activated ticket := by
      simp [apply, possible]
    exact stale (activation_checks_the_ordered_scope_and_exact_live_grant success).2.2.1
  exact refused_activation_preserves_state state ticket required

inductive SlotStep : Option (Ticket Image) → Option (Ticket Image) → Prop
  | stayed (current) : SlotStep current current
  | chose (ticket) : SlotStep none (some ticket)

theorem ordered_reducer_refines_a_single_assignment_slot (state : State Image) (command : Command Image) :
    SlotStep state.installed (apply state command).1.installed := by
  classical
  cases command with
  | register ticket =>
      simp only [apply]
      split <;> exact .stayed _
  | activate ticket =>
      by_cases permits : MayActivate state ticket
      · simp only [apply, ite_eq_left permits]
        change SlotStep state.installed (some ticket)
        rw [permits.2.2]
        exact .chose ticket
      · simpa [apply, permits] using SlotStep.stayed state.installed
  | discard ticket =>
      simp only [apply]
      split <;> exact .stayed _
  | replace revision =>
      simp only [apply]
      split <;> exact .stayed state.installed

theorem an_exact_live_candidate_can_be_installed {state : State Image} {ticket : Ticket Image}
    (eligible : MayActivate state ticket) :
    (apply state (.activate ticket)).1.installed = some ticket ∧
      (apply state (.activate ticket)).2 = .activated ticket := by
  simp [apply, eligible]

theorem a_discarded_grant_cannot_authorize_a_later_activation
    {state : State Image} {ticket : Ticket Image}
    (grant : CurrentGrant state ticket) (unused : state.installed ≠ some ticket) :
    let after := (apply state (.discard ticket)).1
    after.attempts ticket.attempt = .spent ∧ apply after (.activate ticket) = (after, .refused) := by
  classical
  have discarded : (apply state (.discard ticket)).1.attempts ticket.attempt = .spent := by
    simp [apply, grant, unused, put]
  refine ⟨discarded, ?_⟩
  have noActivation : ¬ MayActivate (apply state (.discard ticket)).1 ticket := by
    intro proof
    have success := (an_exact_live_candidate_can_be_installed proof).2
    have held := (activation_checks_the_ordered_scope_and_exact_live_grant success).2.2.2.1
    rw [discarded] at held
    cases held
  exact refused_activation_preserves_state _ _ noActivation

theorem spent_attempt_survives_all_ordered_commands {state : State Image} {id : Nat}
    (spent : state.attempts id = .spent) (command : Command Image) :
    (apply state command).1.attempts id = .spent := by
  classical
  cases command with
  | register ticket =>
      simp only [apply]
      split
      · rename_i allowed
        have other : id ≠ ticket.attempt := by
          intro same
          have absent := allowed.2.2
          rw [← same, spent] at absent
          cases absent
        simp [put, spent, other]
      · exact spent
  | activate ticket =>
      simp only [apply]
      split <;> exact spent
  | discard ticket =>
      simp only [apply]
      split
      · simp [put, spent]
      · exact spent
  | replace revision =>
      simp only [apply]
      split <;> exact (show state.attempts id = .spent from spent)

noncomputable def replay (state : State Image) : List (Command Image) → State Image × List (Outcome Image)
  | [] => (state, [])
  | command :: commands =>
      let first := apply state command
      let rest := replay first.1 commands
      (rest.1, first.2 :: rest.2)

theorem replay_append (state : State Image) (first later : List (Command Image)) :
    replay state (first ++ later) =
      let earlier := replay state first
      let newer := replay earlier.1 later
      (newer.1, earlier.2 ++ newer.2) := by
  induction first generalizing state with
  | nil => simp [replay]
  | cons command rest prior =>
      simp only [List.cons_append, replay]
      rw [prior]

theorem replay_cannot_resurrect_a_spent_attempt {initial : State Image} {id : Nat}
    (spent : initial.attempts id = .spent) (history : List (Command Image)) :
    (replay initial history).1.attempts id = .spent := by
  induction history generalizing initial with
  | nil => exact spent
  | cons command rest prior => exact prior (spent_attempt_survives_all_ordered_commands spent command)

private theorem fixed_slot_stays_fixed {ticket : Ticket Image} {next : Option (Ticket Image)}
    (step : SlotStep (some ticket) next) : next = some ticket := by
  cases step
  rfl

theorem replay_keeps_an_installed_ticket {initial : State Image} {ticket : Ticket Image}
    (installed : initial.installed = some ticket) (history : List (Command Image)) :
    (replay initial history).1.installed = some ticket := by
  induction history generalizing initial with
  | nil => exact installed
  | cons command rest prior =>
      have step := ordered_reducer_refines_a_single_assignment_slot initial command
      have current : (apply initial command).1.installed = some ticket := by
        rw [installed] at step
        exact fixed_slot_stays_fixed step
      exact prior current

theorem replay_extension_preserves_every_result_and_installation
    (initial : State Image) {first later : List (Command Image)} (prior : first <+: later) :
    (replay initial first).2 <+: (replay initial later).2 ∧
      ∀ ticket, (replay initial first).1.installed = some ticket →
        (replay initial later).1.installed = some ticket := by
  obtain ⟨suffix, rfl⟩ := prior
  rw [replay_append]
  exact ⟨List.prefix_append _ _, fun _ installed => replay_keeps_an_installed_ticket installed suffix⟩

theorem current_target_quorum_replays_every_prior_chosen_installation
    {source : ConfigurationClosure.Generation Voter (Command Image)}
    {cut : ConfigurationClosure.Certificate Voter (Command Image)}
    (ranked : ConfigurationClosure.Ranked source.ledger cut)
    (reports : ConfigurationClosure.CoversEveryVote source.ledger cut)
    (initial : State Image) {ballot : Nat} {prior later : List (Command Image)}
    (chosen : Chosen source.ledger ballot prior)
    (adopts : ConfigurationClosure.Recovered source.basis cut <+: later)
    (members : List Voter) (stored available : Voter → Bool)
    (target : Majority members stored) (recovering : Majority members available)
    (media : Voter → List (Command Image) → Prop)
    (exactCopy : ∀ v ∈ members, stored v = true → media v later) :
    ∃ v ∈ members, available v = true ∧ media v later ∧
      (replay initial prior).2 <+: (replay initial later).2 ∧
      ∀ ticket, (replay initial prior).1.installed = some ticket →
        (replay initial later).1.installed = some ticket := by
  have inherited := ConfigurationClosure.ranked_cut_covers_every_old_quorum_even_if_learned_late
    source.rules ranked reports source.basis chosen
  obtain ⟨v, member, online, hasCopy⟩ := majorities_overlap members available stored recovering target
  exact ⟨v, member, online, exactCopy v member hasCopy,
    replay_extension_preserves_every_result_and_installation initial (inherited.trans adopts)⟩

#print axioms activation_checks_the_ordered_scope_and_exact_live_grant
#print axioms a_delayed_packet_for_an_earlier_revision_is_refused
#print axioms ordered_reducer_refines_a_single_assignment_slot
#print axioms an_exact_live_candidate_can_be_installed
#print axioms a_discarded_grant_cannot_authorize_a_later_activation
#print axioms spent_attempt_survives_all_ordered_commands
#print axioms replay_append
#print axioms replay_cannot_resurrect_a_spent_attempt
#print axioms replay_keeps_an_installed_ticket
#print axioms replay_extension_preserves_every_result_and_installation
#print axioms current_target_quorum_replays_every_prior_chosen_installation

end PendingActivation
