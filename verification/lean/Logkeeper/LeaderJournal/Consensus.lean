import Logkeeper.JournalRefinement

namespace Logkeeper.LeaderJournal

open JournalRefinement (Majority majorities_overlap)

set_option warningAsError true

abbrev KeeperId := Nat

inductive Configuration where
  | stable (members : List KeeperId)
  | joint (oldMembers newMembers : List KeeperId)
  deriving DecidableEq, Repr

def Configuration.contains : Configuration → KeeperId → Bool
  | .stable members, keeper => members.contains keeper
  | .joint oldMembers newMembers, keeper => oldMembers.contains keeper || newMembers.contains keeper

def Configuration.quorum : Configuration → (KeeperId → Bool) → Prop
  | .stable members, votes => Majority members votes
  | .joint oldMembers newMembers, votes => Majority oldMembers votes ∧ Majority newMembers votes

instance (configuration : Configuration) (votes : KeeperId → Bool) :
    Decidable (configuration.quorum votes) :=
  match configuration with
  | .stable members => inferInstanceAs (Decidable (Majority members votes))
  | .joint oldMembers newMembers =>
      inferInstanceAs (Decidable (Majority oldMembers votes ∧ Majority newMembers votes))

inductive Configuration.Change : Configuration → Configuration → Prop
  | enter {oldMembers newMembers} : newMembers.Nodup → newMembers ≠ [] →
      Change (.stable oldMembers) (.joint oldMembers newMembers)
  | finish {oldMembers newMembers} : Change (.joint oldMembers newMembers) (.stable newMembers)

theorem Configuration.quorums_intersect {current next : Configuration} {a b : KeeperId → Bool}
    (transition : current = next ∨ current.Change next)
    (first : current.quorum a) (second : next.quorum b) :
    ∃ keeper, a keeper = true ∧ b keeper = true := by
  have overlap (members : List KeeperId) (left : Majority members a) (right : Majority members b) :
      ∃ keeper, a keeper = true ∧ b keeper = true := by
    obtain ⟨keeper, _, av, bv⟩ := majorities_overlap members a b left right
    exact ⟨keeper, av, bv⟩
  rcases transition with rfl | change
  · cases current with
    | stable members => exact overlap members first second
    | joint oldMembers newMembers => exact overlap oldMembers first.1 second.1
  · cases change with
    | enter => exact overlap _ first second.1
    | finish => exact overlap _ first.2 second

inductive Command (Application : Type) where
  | apply (request : Application)
  | barrier
  | configure (configuration : Configuration)
  deriving DecidableEq, Repr

structure Entry (Application : Type) where
  term : Nat
  command : Command Application
  deriving DecidableEq, Repr

abbrev Log (Application : Type) := List (Entry Application)

def lastTerm (log : Log Application) : Nat :=
  (log.getLast?.map Entry.term).getD 0

def configurationAt (genesis : Configuration) (log : Log Application) : Configuration :=
  log.foldl (fun configuration entry =>
    match entry.command with
    | .configure next => next
    | _ => configuration) genesis

def AtLeast (required candidate : Log Application) : Prop :=
  lastTerm required < lastTerm candidate ∨
    (lastTerm required = lastTerm candidate ∧ required.length ≤ candidate.length)

def Ordered (log : Log Application) : Prop :=
  ∀ ⦃a b : Log Application⦄, a <+: b → b <+: log → lastTerm a ≤ lastTerm b

private theorem lastTerm_push (log : Log Application) (entry : Entry Application) :
    lastTerm (log ++ [entry]) = entry.term := by
  simp [lastTerm, List.getLast?_append]

theorem Ordered.ofPrefix {short long : Log Application} (ordered : Ordered long)
    (history : short <+: long) : Ordered short := by
  intro a b first second
  exact ordered first (second.trans history)

private theorem ordered_push {log : Log Application} (ordered : Ordered log) (entry : Entry Application)
    (term : lastTerm log ≤ entry.term) : Ordered (log ++ [entry]) := by
  intro a b ab bLog
  by_cases short : b.length ≤ log.length
  · exact ordered ab (List.prefix_of_prefix_length_le bLog (List.prefix_append _ _) short)
  · have equal := bLog.eq_of_length_le (by simp; omega)
    subst b
    rw [lastTerm_push]
    by_cases shortA : a.length ≤ log.length
    · have ap : a <+: log :=
        List.prefix_of_prefix_length_le ab (List.prefix_append _ _) shortA
      exact Nat.le_trans (ordered ap List.prefix_rfl) term
    · rw [ab.eq_of_length_le (by simp; omega), lastTerm_push]
      exact Nat.le_refl _

private theorem prefix_of_rank {a b issued : Log Application} (ordered : Ordered issued)
    (aIssued : a <+: issued) (bIssued : b <+: issued) (rank : AtLeast a b) : a <+: b := by
  by_cases lengths : a.length ≤ b.length
  · exact List.prefix_of_prefix_length_le aIssued bIssued lengths
  · have ba := List.prefix_of_prefix_length_le bIssued aIssued (by omega)
    have terms := ordered ba aIssued
    rcases rank with newer | ⟨_, ns⟩ <;> omega

private def merge [DecidableEq Application] (previous incoming : Log Application) :=
  if incoming <+: previous then previous else incoming

def update (f : KeeperId → α) (key : KeeperId) (value : α) : KeeperId → α :=
  fun keeper => if keeper = key then value else f keeper

@[simp] theorem update_same (f : KeeperId → α) (key : KeeperId) (value : α) :
    update f key value key = value := by simp [update]

structure State (Application : Type) where
  genesis : Configuration
  term : Nat
  leader : Option KeeperId
  issued : Log Application
  durable : KeeperId → Log Application
  committed : Log Application
  /-- Last applied cut exposed locally by each keeper. -/
  applied : KeeperId → Log Application
  online : KeeperId → Bool

def initial (members : List KeeperId) : State Application :=
  ⟨.stable members, 0, none, [], fun _ => [], [], fun _ => [], fun _ => true⟩

def State.configuration (s : State Application) : Configuration :=
  configurationAt s.genesis s.committed

def State.candidateConfiguration (s : State Application) (keeper : KeeperId) : Configuration :=
  configurationAt s.genesis (s.durable keeper)

def State.effectiveConfiguration (s : State Application) : Configuration :=
  configurationAt s.genesis s.issued

def State.active (s : State Application) : Prop :=
  ∃ keeper, s.leader = some keeper ∧ s.online keeper = true

def State.supports (s : State Application) (votes : KeeperId → Bool) (history : Log Application) : Prop :=
  ∀ keeper, votes keeper = true → history <+: s.durable keeper

def State.responds (s : State Application) (votes : KeeperId → Bool) : Prop :=
  ∀ keeper, votes keeper = true → s.online keeper = true

def State.learnersReady (s : State Application) : Configuration → Prop
  | .joint oldMembers newMembers =>
      ∀ keeper ∈ newMembers, keeper ∉ oldMembers → s.issued <+: s.durable keeper
  | .stable _ => True

def State.admits (s : State Application) : Command Application → Prop
  | .configure next => s.effectiveConfiguration = s.configuration ∧
      s.configuration.Change next ∧ s.learnersReady next
  | _ => True

def State.issue (s : State Application) (command : Command Application) : State Application :=
  { s with issued := s.issued ++ [⟨s.term, command⟩] }

def State.replicate [DecidableEq Application] (s : State Application) (keeper : KeeperId)
    (history : Log Application) : State Application :=
  { s with durable := update s.durable keeper (merge (s.durable keeper) history) }

def State.replicateTo [DecidableEq Application] (s : State Application) (keepers : List KeeperId)
    (history : Log Application) : State Application :=
  { s with durable := fun keeper =>
      if keeper ∈ keepers then merge (s.durable keeper) history else s.durable keeper }

def State.restrict (s : State Application) (available : KeeperId → Bool) : State Application :=
  { s with
    online := fun keeper => s.online keeper && available keeper
    leader := s.leader.filter available }

/-- The consensus model boundary is durable history replication and a completed election.
    A vote within the completed election samples the voter's durable log.
    Each issue is unique within the active term. An old term can make no further
    authoritative transition after the election. -/
inductive Step [DecidableEq Application] : State Application → State Application → Prop
  | elect {s} (candidate : KeeperId) (term : Nat) (votes : KeeperId → Bool)
      (newTerm : s.term < term) (online : s.online candidate = true)
      (permitted : s.configuration = s.candidateConfiguration candidate ∨
        s.configuration.Change (s.candidateConfiguration candidate))
      (member : (s.candidateConfiguration candidate).contains candidate = true)
      (quorum : (s.candidateConfiguration candidate).quorum votes)
      (responds : s.responds votes)
      (rank : ∀ keeper, votes keeper = true → AtLeast (s.durable keeper) (s.durable candidate)) :
      Step s { s with term, leader := some candidate, issued := s.durable candidate }
  | issue {s} (command : Command Application) (active : s.active)
      (admitted : s.admits command) :
      Step s (s.issue command)
  | replicate {s} (keeper : KeeperId) (term : Nat) (history : Log Application)
      (active : s.active) (sameTerm : term = s.term) (online : s.online keeper = true)
      (fromLeader : history <+: s.issued) :
      Step s (s.replicate keeper history)
  | commit {s} (cut : Log Application) (votes : KeeperId → Bool)
      (active : s.active) (forward : s.committed.length ≤ cut.length) (issued : cut <+: s.issued)
      (currentTerm : lastTerm cut = s.term)
      (configuration : configurationAt s.genesis cut = s.effectiveConfiguration)
      (quorum : (configurationAt s.genesis cut).quorum votes)
      (durable : s.supports votes cut) :
      Step s { s with
        committed := cut
        leader := s.leader.filter ((configurationAt s.genesis cut).contains) }
  | apply {s} (keeper : KeeperId) (cut : Log Application)
      (online : s.online keeper = true) (forward : s.applied keeper <+: cut)
      (learned : cut <+: s.committed) (durable : cut <+: s.durable keeper) :
      Step s { s with applied := update s.applied keeper cut }
  | fail {s} (keeper : KeeperId) :
      Step s { s with
        online := update s.online keeper false
        leader := if s.leader = some keeper then none else s.leader }
  | restrict {s} (available : KeeperId → Bool) : Step s (s.restrict available)
  | restart {s} (keeper : KeeperId) :
      Step s { s with online := update s.online keeper true }
  | idle {s} : Step s s

inductive Trace [DecidableEq Application] : State Application → State Application → Prop
  | nil (state : State Application) : Trace state state
  | snoc {first before after} : Trace first before → Step before after → Trace first after

def Reachable [DecidableEq Application] (members : List KeeperId) (s : State Application) : Prop :=
  members.Nodup ∧ members ≠ [] ∧ Trace (initial members) s

structure Sound (s : State Application) : Prop where
  issuedOrdered : Ordered s.issued
  issuedTerm : lastTerm s.issued ≤ s.term
  allTerms : ∀ keeper, lastTerm (s.durable keeper) ≤ s.term
  allOrdered : ∀ keeper, Ordered (s.durable keeper)
  currentLog : ∀ keeper, lastTerm (s.durable keeper) = s.term → s.durable keeper <+: s.issued
  leaderContains : s.committed <+: s.issued
  rankedContains : ∀ keeper, AtLeast s.committed (s.durable keeper) →
    s.committed <+: s.durable keeper
  supported : ∃ votes, s.configuration.quorum votes ∧ s.supports votes s.committed
  configurationChange : s.configuration = s.effectiveConfiguration ∨
    s.configuration.Change s.effectiveConfiguration
  applied : ∀ keeper, s.applied keeper <+: s.committed ∧ s.applied keeper <+: s.durable keeper

private theorem all_present_majority (members : List KeeperId) (nonempty : members ≠ []) :
    Majority members (fun _ => true) := by
  have positive : 0 < members.length := List.length_pos_iff.mpr nonempty
  have exactCount : members.countP (fun _ => true) = members.length := by simp
  unfold Majority
  rw [exactCount]
  omega

private theorem ordered_empty : Ordered ([] : Log Application) := by
  intro a b ab bn
  simp at bn
  subst b
  simp at ab
  subst a
  exact Nat.le_refl _

theorem initial_sound (members : List KeeperId) (nonempty : members ≠ []) :
    Sound (initial members : State Application) where
  issuedOrdered := ordered_empty
  issuedTerm := Nat.zero_le _
  allTerms := fun _ => Nat.zero_le _
  allOrdered := fun _ => ordered_empty
  currentLog := fun _ _ => List.prefix_rfl
  leaderContains := List.prefix_rfl
  rankedContains := fun _ _ => List.prefix_rfl
  supported := ⟨fun _ => true, all_present_majority members nonempty, fun _ _ => List.prefix_rfl⟩
  configurationChange := Or.inl rfl
  applied := fun _ => ⟨List.prefix_rfl, List.prefix_rfl⟩

theorem AtLeast.trans {a b c : Log Application} (ab : AtLeast a b) (bc : AtLeast b c) :
    AtLeast a c := by
  rcases ab with less | ⟨same, len⟩ <;> rcases bc with newer | ⟨equal, length⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨same.trans equal, Nat.le_trans len length⟩

theorem elected_log_contains_committed {s : State Application} (sound : Sound s)
    {candidate : KeeperId} {votes : KeeperId → Bool}
    (permitted : s.configuration = s.candidateConfiguration candidate ∨
      s.configuration.Change (s.candidateConfiguration candidate))
    (quorum : (s.candidateConfiguration candidate).quorum votes)
    (rank : ∀ keeper, votes keeper = true → AtLeast (s.durable keeper) (s.durable candidate)) :
    s.committed <+: s.durable candidate := by
  obtain ⟨durable, durableQuorum, witnessed⟩ := sound.supported
  obtain ⟨keeper, stored, voted⟩ := Configuration.quorums_intersect permitted durableQuorum quorum
  have history := witnessed keeper stored
  have terms := sound.allOrdered keeper history List.prefix_rfl
  have committedRank : AtLeast s.committed (s.durable keeper) := by
    unfold AtLeast
    by_cases same : lastTerm s.committed = lastTerm (s.durable keeper)
    · exact Or.inr ⟨same, history.length_le⟩
    · exact Or.inl (by omega)
  exact sound.rankedContains candidate (committedRank.trans (rank keeper voted))

private theorem merge_keeps_applied [DecidableEq Application] {previous incoming known committed issued :
    Log Application} (storedLocally : known <+: previous) (chosen : known <+: committed)
    (inLeader : committed <+: issued) (new : incoming <+: issued) :
    known <+: merge previous incoming := by
  unfold merge
  split
  · exact storedLocally
  · rename_i different
    rcases List.prefix_or_prefix_of_prefix new (chosen.trans inLeader) with short | long
    · exact (different (short.trans storedLocally)).elim
    · exact long

private theorem replication_preserves [DecidableEq Application] (s : State Application)
    (keeper : KeeperId) (incoming : Log Application) (property : KeeperId → Log Application → Prop)
    (before : ∀ node, property node (s.durable node)) (written : property keeper incoming) :
    ∀ node, property node ((s.replicate keeper incoming).durable node) := by
  intro node
  by_cases same : node = keeper
  · subst node
    simp only [State.replicate, update_same, merge]
    split
    · exact before keeper
    · exact written
  · simpa [State.replicate, update, same] using before node

theorem step_preserves_sound [DecidableEq Application] {s next : State Application}
    (sound : Sound s) (step : Step s next) : Sound next := by
  cases step with
  | elect candidate term votes newer online allowed member quorum responds rank =>
      exact { sound with
        issuedOrdered := sound.allOrdered candidate
        issuedTerm := Nat.le_trans (sound.allTerms candidate) (Nat.le_of_lt newer)
        allTerms := fun keeper => Nat.le_trans (sound.allTerms keeper) (Nat.le_of_lt newer)
        currentLog := fun keeper same => False.elim (by have := sound.allTerms keeper; dsimp at same; omega)
        leaderContains := elected_log_contains_committed sound allowed quorum rank
        configurationChange := allowed }
  | issue command active admitted =>
      have history : s.issued <+: (s.issue command).issued := List.prefix_append _ _
      exact { sound with
        issuedOrdered := ordered_push sound.issuedOrdered _ sound.issuedTerm
        issuedTerm := by simp [State.issue, lastTerm_push]
        currentLog := fun keeper current => (sound.currentLog keeper current).trans history
        leaderContains := sound.leaderContains.trans history
        configurationChange := by
          cases command with
          | apply request =>
              simpa [State.effectiveConfiguration, State.configuration, State.issue,
                configurationAt, List.foldl_append] using sound.configurationChange
          | barrier =>
              simpa [State.effectiveConfiguration, State.configuration, State.issue,
                configurationAt, List.foldl_append] using sound.configurationChange
          | configure next =>
              exact Or.inr (by
                simpa [State.effectiveConfiguration, State.configuration, State.issue,
                  configurationAt, List.foldl_append] using (show s.configuration.Change next from admitted.2.1)) }
  | replicate keeper term history active sameTerm online issued =>
      have ordered := sound.issuedOrdered.ofPrefix issued
      have termBound := Nat.le_trans (sound.issuedOrdered issued List.prefix_rfl) sound.issuedTerm
      have carry (node : KeeperId) (log : Log Application) (committed : log <+: s.committed)
          (stored : log <+: s.durable node) :
          log <+: (s.replicate keeper history).durable node := by
        by_cases same : node = keeper
        · subst node
          simpa only [State.replicate, update_same] using
            merge_keeps_applied stored committed sound.leaderContains issued
        · simpa [State.replicate, update, same] using stored
      refine { sound with
        allTerms := replication_preserves s keeper history (fun _ log => lastTerm log ≤ s.term)
          sound.allTerms termBound
        allOrdered := replication_preserves s keeper history (fun _ log => Ordered log)
          sound.allOrdered ordered
        currentLog := replication_preserves s keeper history
          (fun _ log => lastTerm log = s.term → log <+: s.issued) sound.currentLog (fun _ => issued)
        rankedContains := replication_preserves s keeper history
          (fun _ log => AtLeast s.committed log → s.committed <+: log) sound.rankedContains
          (prefix_of_rank sound.issuedOrdered sound.leaderContains issued)
        supported := ?_
        applied := fun node => ⟨(sound.applied node).1, carry node _ (sound.applied node).1 (sound.applied node).2⟩ }
      obtain ⟨votes, quorum, holds⟩ := sound.supported
      exact ⟨votes, quorum, fun node voted => carry node _ List.prefix_rfl (holds node voted)⟩
  | commit cut votes active forward issued current configuration quorum durable =>
      have carries := List.prefix_of_prefix_length_le sound.leaderContains issued forward
      refine { sound with
        leaderContains := issued
        supported := ⟨votes, quorum, durable⟩
        configurationChange := Or.inl configuration
        rankedContains := ?_
        applied := fun keeper => ⟨(sound.applied keeper).1.trans carries, (sound.applied keeper).2⟩ }
      intro keeper rank
      have termBound := sound.allTerms keeper
      change AtLeast cut (s.durable keeper) at rank
      unfold AtLeast at rank
      rcases rank with newer | ⟨same, lengths⟩
      · omega
      · exact List.prefix_of_prefix_length_le issued (sound.currentLog keeper (same.symm.trans current)) lengths
  | apply keeper cut online forward learned durable =>
      refine { sound with applied := ?_ }
      intro node
      by_cases same : node = keeper
      · subst node
        simpa only [update_same] using And.intro learned durable
      · simpa [update, same] using sound.applied node
  | fail => exact { sound with }
  | restrict => exact { sound with }
  | restart => exact { sound with }
  | idle => exact sound

theorem reachable_sound [DecidableEq Application] {members : List KeeperId} {s : State Application}
    (reached : Reachable members s) : Sound s := by
  obtain ⟨_, nonempty, trace⟩ := reached
  induction trace with
  | nil => exact initial_sound members nonempty
  | snoc _ step prior => exact step_preserves_sound prior step

theorem step_changes_configuration [DecidableEq Application] {before after : State Application}
    (sound : Sound before) (step : Step before after) :
    before.configuration = after.configuration ∨ before.configuration.Change after.configuration := by
  cases step with
  | commit cut _ _ _ _ _ configuration _ _ =>
      change before.configuration = configurationAt before.genesis cut ∨
        before.configuration.Change (configurationAt before.genesis cut)
      exact configuration.symm ▸ sound.configurationChange
  | _ => exact Or.inl rfl

theorem stable_route_cannot_skip_joint {oldMembers newMembers : List KeeperId}
    (different : oldMembers ≠ newMembers) :
    ¬ ((.stable oldMembers : Configuration) = .stable newMembers ∨
      (.stable oldMembers : Configuration).Change (.stable newMembers)) := by
  intro route
  rcases route with equal | changed
  · exact different (Configuration.stable.inj equal)
  · cases changed

theorem Trace.sound [DecidableEq Application] {before after : State Application}
    (trace : Trace before after) (sound : Sound before) : Sound after := by
  induction trace with
  | nil => exact sound
  | snoc _ step prior => exact step_preserves_sound prior step

theorem Step.committed_prefix [DecidableEq Application] {before after : State Application}
    (step : Step before after) (sound : Sound before) : before.committed <+: after.committed := by
  cases step with
  | commit _ _ _ forward issued _ _ _ _ =>
      exact List.prefix_of_prefix_length_le sound.leaderContains issued forward
  | _ => exact List.prefix_rfl

theorem trace_committed_prefix [DecidableEq Application] {before after : State Application}
    (trace : Trace before after) (sound : Sound before) : before.committed <+: after.committed := by
  induction trace with
  | nil => exact List.prefix_rfl
  | snoc earlier step ih => exact ih.trans (step.committed_prefix (earlier.sound sound))

theorem trace_term_monotone [DecidableEq Application] {before after : State Application}
    (trace : Trace before after) : before.term ≤ after.term := by
  induction trace with
  | nil => exact Nat.le_refl _
  | snoc _ step ih =>
      cases step with
      | elect _ _ _ newer _ _ _ _ _ _ => exact Nat.le_trans ih (Nat.le_of_lt newer)
      | _ => exact ih

theorem trace_applied_prefix [DecidableEq Application] {before after : State Application}
    (trace : Trace before after) (keeper : KeeperId) : before.applied keeper <+: after.applied keeper := by
  induction trace with
  | nil => exact List.prefix_rfl
  | snoc _ step ih =>
      cases step with
      | apply node cut _ forward _ _ =>
          by_cases same : keeper = node
          · subst node
            simpa only [update_same] using ih.trans forward
          · simpa [update, same] using ih
      | _ => exact ih

theorem Trace.trans [DecidableEq Application] {first middle last : State Application}
    (firstTrace : Trace first middle) (lastTrace : Trace middle last) : Trace first last := by
  induction lastTrace with
  | nil => exact firstTrace
  | snoc _ step ih => exact .snoc ih step

theorem Step.trace [DecidableEq Application] {before after : State Application}
    (step : Step before after) : Trace before after := .snoc (.nil _) step

theorem replicate_to_covers [DecidableEq Application] (s : State Application)
    (keepers : List KeeperId) (history : Log Application) {keeper : KeeperId}
    (member : keeper ∈ keepers) : history <+: (s.replicateTo keepers history).durable keeper := by
  simp only [State.replicateTo, ite_eq_left member]
  unfold merge
  split
  · assumption
  · exact List.prefix_rfl

theorem replicate_to_trace [DecidableEq Application] (s : State Application)
    (keepers : List KeeperId) (history : Log Application) (leader : s.active)
    (online : ∀ keeper ∈ keepers, s.online keeper = true) (issued : history <+: s.issued) :
    Trace s (s.replicateTo keepers history) := by
  induction keepers generalizing s with
  | nil =>
      simpa [State.replicateTo] using Trace.nil s
  | cons keeper rest ih =>
      let written := s.replicate keeper history
      have head : Step s written :=
        .replicate keeper s.term history leader rfl (online keeper List.mem_cons_self) issued
      have tail := ih written leader (fun node mem => online node (List.mem_cons_of_mem _ mem)) issued
      have same : written.replicateTo rest history = s.replicateTo (keeper :: rest) history := by
        have media : (written.replicateTo rest history).durable =
            (s.replicateTo (keeper :: rest) history).durable := by
          funext node
          by_cases equal : node = keeper
          · subst node
            by_cases member : keeper ∈ rest
            · have already : history <+: merge (s.durable keeper) history := by
                unfold merge
                split
                · assumption
                · exact List.prefix_rfl
              simp only [written, State.replicate, State.replicateTo, update_same,
                ite_eq_left member, ite_eq_left List.mem_cons_self]
              exact ite_eq_left already
            · simp [written, State.replicate, State.replicateTo, member]
          · simp [written, State.replicate, State.replicateTo, update, equal]
        exact congrArg (fun durable => { s with durable }) media
      rw [← same]
      exact head.trace.trans tail

theorem trace_genesis [DecidableEq Application] {before after : State Application}
    (trace : Trace before after) : before.genesis = after.genesis := by
  induction trace with
  | nil => rfl
  | snoc _ step ih => cases step <;> exact ih

end Logkeeper.LeaderJournal
