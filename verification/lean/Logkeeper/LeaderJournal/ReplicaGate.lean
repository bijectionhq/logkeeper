import Logkeeper.LeaderJournal.Installation
import Logkeeper.LeaderJournal.Bootstrap

namespace Logkeeper.LeaderJournal.Installation

set_option warningAsError true

abbrev Fleet (Application : Type) := KeeperId → Keeper Application

/-- Bind the core's online mask and exact durable prefix to the enrolled
    replica. Contacts can make a healthy replica unreachable. -/
def Coupled (fleet : Fleet Application) (stream : StreamId) (core : State Application) : Prop :=
  ∀ keeper, core.online keeper = true →
    ∃ basis, (fleet keeper).ready stream = some basis ∧ basis.log = core.durable keeper

/-- A deployed stream begins with a closed admission mask, then enables
    individual contacts through the checked media connect bridge. -/
theorem checked_genesis_starts_closed [DecidableEq Application] {registry : Placement.Registry}
    {members : List KeeperId} (roster : Placement.Roster registry members)
    (fleet : Fleet Application) (stream : StreamId) :
    let boot := (LeaderJournal.initial members : State Application).restrict (fun _ => false)
    Placement.Trace registry members boot ∧ Coupled fleet stream boot := by
  refine ⟨.next (.initial roster) (.restrict _) roster, ?_⟩
  intro keeper online
  simp [State.restrict] at online

def CanRespond (fleet : Fleet Application) (stream : StreamId) (core : State Application)
    (keeper : KeeperId) : Prop :=
  core.online keeper = true ∧ ∃ basis, (fleet keeper).ready stream = some basis

def CanVote (fleet : Fleet Application) (stream : StreamId) (core : State Application)
    (configuration : Configuration) (keeper candidate : KeeperId) (term : Nat) : Prop :=
  core.online keeper = true ∧ configuration.contains keeper = true ∧
    ∃ basis, (fleet keeper).ready stream = some basis ∧
      basis.log = core.durable keeper ∧ basis.hard.term = term ∧ basis.hard.vote = some candidate

def CanAcknowledge (fleet : Fleet Application) (stream : StreamId) (core : State Application)
    (configuration : Configuration) (keeper : KeeperId) (cut : Log Application) : Prop :=
  core.online keeper = true ∧ configuration.contains keeper = true ∧
    ∃ basis, (fleet keeper).ready stream = some basis ∧ cut <+: basis.log

theorem checked_response {fleet : Fleet Application} {stream : StreamId} {core : State Application}
    (coupled : Coupled fleet stream core) {votes : KeeperId → Bool}
    (responds : core.responds votes) {keeper : KeeperId} (voted : votes keeper = true) :
    CanRespond fleet stream core keeper := by
  have online := responds keeper voted
  obtain ⟨basis, ready, _⟩ := coupled keeper online
  exact ⟨online, basis, ready⟩

theorem head_confirmation_uses_healthy_replicas [DecidableEq Payload]
    {fleet : Fleet (Request Payload)} {stream : StreamId} {invoked returned : Cluster Payload}
    (call : HeadRead invoked returned) (coupled : Coupled fleet stream call.confirmed)
    {keeper : KeeperId} (confirmed : call.voters keeper = true) :
    CanRespond fleet stream call.confirmed keeper :=
  checked_response coupled call.responds confirmed

theorem same_term_vote_reply_unique {authority : Authority} {keeper first second : KeeperId}
    {before after : Fleet Application} {stream : StreamId} {prior next : State Application}
    {configuration earlierConfig : Configuration} {term : Nat}
    (lifecycle : Trace authority keeper (before keeper) (after keeper))
    (oldVote : CanVote before stream prior configuration keeper first term)
    (newVote : CanVote after stream next earlierConfig keeper second term) : first = second := by
  obtain ⟨_, _, old, ready, _, oldTerm, voted⟩ := oldVote
  obtain ⟨_, _, new, nowReady, _, newTerm, later⟩ := newVote
  have held := same_term_vote_survives_media_events lifecycle
    (Keeper.ready_basis ready) (Keeper.ready_basis nowReady) voted (oldTerm.trans newTerm.symm)
  exact Option.some.inj (held.symm.trans later)

theorem checked_commit_ack {fleet : Fleet Application} {stream : StreamId} {core : State Application}
    {configuration : Configuration} {cut : Log Application} {votes : KeeperId → Bool}
    (coupled : Coupled fleet stream core) (ack : core.supports votes cut)
    (responds : core.responds votes) {keeper : KeeperId} (voted : votes keeper = true)
    (member : configuration.contains keeper = true) :
    CanAcknowledge fleet stream core configuration keeper cut := by
  have online := responds keeper voted
  obtain ⟨basis, ready, exactLog⟩ := coupled keeper online
  exact ⟨online, member, basis, ready, exactLog.symm ▸ ack keeper voted⟩

theorem healthy_acknowledgements_refine_commit [DecidableEq Application]
    {fleet : Fleet Application} {stream : StreamId} {core : State Application}
    {cut : Log Application} {votes : KeeperId → Bool}
    (coupled : Coupled fleet stream core) (active : core.active)
    (forward : core.committed.length ≤ cut.length) (issued : cut <+: core.issued)
    (currentTerm : lastTerm cut = core.term)
    (configuration : configurationAt core.genesis cut = core.effectiveConfiguration)
    (quorum : (configurationAt core.genesis cut).quorum votes)
    (replies : ∀ keeper, votes keeper = true →
      CanAcknowledge fleet stream core (configurationAt core.genesis cut) keeper cut) :
    LeaderJournal.Step core { core with
      committed := cut
      leader := core.leader.filter ((configurationAt core.genesis cut).contains) } := by
  refine .commit cut votes active forward issued currentTerm configuration quorum ?_
  intro keeper voted
  obtain ⟨online, _, basis, ready, accepted⟩ := replies keeper voted
  obtain ⟨known, reported, exactLog⟩ := coupled keeper online
  have same : known = basis := Option.some.inj (reported.symm.trans ready)
  rw [← same, exactLog] at accepted
  exact accepted

theorem healthy_votes_refine_election [DecidableEq Application]
    {fleet : Fleet Application} {stream : StreamId} {core : State Application}
    {term : Nat} {candidate : KeeperId} {votes : KeeperId → Bool}
    (newer : core.term < term) (online : CanRespond fleet stream core candidate)
    (permitted : core.configuration = core.candidateConfiguration candidate ∨
      core.configuration.Change (core.candidateConfiguration candidate))
    (member : (core.candidateConfiguration candidate).contains candidate = true)
    (quorum : (core.candidateConfiguration candidate).quorum votes)
    (replies : ∀ keeper, votes keeper = true →
      CanVote fleet stream core (core.candidateConfiguration candidate) keeper candidate term)
    (rank : ∀ keeper, votes keeper = true → AtLeast (core.durable keeper) (core.durable candidate)) :
    LeaderJournal.Step core
      { core with term, leader := some candidate, issued := core.durable candidate } :=
  .elect candidate term votes newer online.1 permitted member quorum
    (fun keeper voted => (replies keeper voted).1) rank

theorem learner_cannot_ack_as_voter {fleet : Fleet Application} {stream : StreamId}
    {core : State Application} {configuration : Configuration} {keeper : KeeperId}
    {cut : Log Application} (learner : configuration.contains keeper = false) :
    ¬ CanAcknowledge fleet stream core configuration keeper cut := by
  intro ack
  have member := ack.2.1
  rw [learner] at member
  contradiction

/-- A checked joint issue carries the leader's exact issued cut on each
    newcomer. The bytes are already durable while the keeper is a learner. -/
theorem joint_issue_requires_exact_learner_cut {fleet : Fleet Application} {stream : StreamId}
    {core : State Application} {oldMembers newMembers : List KeeperId} {keeper : KeeperId}
    (coupled : Coupled fleet stream core)
    (admitted : core.admits (.configure (.joint oldMembers newMembers)))
    (newMember : keeper ∈ newMembers) (newcomer : keeper ∉ oldMembers)
    (reachable : core.online keeper = true) :
    ∃ basis, (fleet keeper).ready stream = some basis ∧ core.issued <+: basis.log := by
  obtain ⟨basis, ready, exactLog⟩ := coupled keeper reachable
  exact ⟨basis, ready, exactLog.symm ▸ admitted.2.2 keeper newMember newcomer⟩

private theorem joint_source {current : Configuration} {oldMembers newMembers : List KeeperId}
    (change : current.Change (.joint oldMembers newMembers)) : current = .stable oldMembers := by
  cases change
  rfl

/-- Deployment path for the joint issue. It combines an authorized staged
    route, the proposed roster check and exact checked learner cuts. -/
theorem checked_joint_issue_refines [DecidableEq Application]
    {registry : Placement.Registry} {genesis oldMembers newMembers : List KeeperId}
    {d : Bootstrap.Directory} {stream : StreamId} {core : State Application} {fleet : Fleet Application}
    (deployment : Placement.Trace registry genesis core) (catalog : Bootstrap.CatalogReachable registry d)
    (coupled : Coupled fleet stream core) (leader : core.active)
    (target : Placement.Roster registry newMembers)
    (admitted : core.admits (.configure (.joint oldMembers newMembers)))
    (staged : d.allowsIssue stream core (.configure (.joint oldMembers newMembers)))
    (checkedLearners : ∀ keeper ∈ newMembers, keeper ∉ oldMembers → core.online keeper = true) :
    Placement.Trace registry genesis (core.issue (.configure (.joint oldMembers newMembers))) ∧
      d.staged stream = some ⟨configurationVersion core.committed, oldMembers, newMembers⟩ ∧
      ∀ keeper ∈ newMembers, keeper ∉ oldMembers →
        ∃ basis, (fleet keeper).ready stream = some basis ∧ core.issued <+: basis.log := by
  have previous := deployment.configuration_valid.1
  rw [joint_source admitted.2.1] at previous
  have next : Placement.Valid registry
      (core.issue (.configure (.joint oldMembers newMembers))).effectiveConfiguration := by
    simpa [State.effectiveConfiguration, State.issue, configurationAt, List.foldl_append]
      using (show Placement.Valid registry (.joint oldMembers newMembers) from ⟨previous, target⟩)
  exact ⟨.next deployment (Bootstrap.checked_issue_refines leader admitted staged) next,
    Bootstrap.joint_issue_requires_staged_contacts registry catalog staged,
    fun keeper member newcomer => joint_issue_requires_exact_learner_cut coupled admitted member newcomer
      (checkedLearners keeper member newcomer)⟩

def disconnect (core : State Application) (keeper : KeeperId) : State Application :=
  { core with
    online := update core.online keeper false
    leader := if core.leader = some keeper then none else core.leader }

def connect (core : State Application) (keeper : KeeperId) : State Application :=
  { core with online := update core.online keeper true }

private theorem disconnect_refines [DecidableEq Application]
    {fleet : Fleet Application} {stream : StreamId} {core : State Application}
    (coupled : Coupled fleet stream core) (keeper : KeeperId) (replacement : Keeper Application) :
    LeaderJournal.Step core (disconnect core keeper) ∧
      Coupled (update fleet keeper replacement) stream (disconnect core keeper) := by
  refine ⟨.fail keeper, ?_⟩
  intro node online
  by_cases same : node = keeper
  · subst node
    simp [disconnect] at online
  · obtain ⟨basis, ready, history⟩ := coupled node (by simpa [disconnect, update, same] using online)
    exact ⟨basis, by simpa [update, same] using ready, history⟩

private theorem connect_refines [DecidableEq Application] {fleet : Fleet Application}
    {stream : StreamId} {core : State Application} {keeper : KeeperId}
    (coupled : Coupled fleet stream core) (replacement : Keeper Application)
    {basis : Basis Application} (ready : replacement.ready stream = some basis)
    (history : basis.log = core.durable keeper) :
    LeaderJournal.Step core (connect core keeper) ∧
      Coupled (update fleet keeper replacement) stream (connect core keeper) := by
  refine ⟨.restart keeper, ?_⟩
  intro node online
  by_cases same : node = keeper
  · subst node
    exact ⟨basis, by simpa only [update_same] using ready, history⟩
  · obtain ⟨old, healthy, exactLog⟩ := coupled node (by simpa [connect, update, same] using online)
    exact ⟨old, by simpa [update, same] using healthy, exactLog⟩

/-- The same-incarnation restart is the core stutter on durable state, with
    readiness enabled only for the checked image. -/
theorem trusted_restart_refines [DecidableEq Application] {authority : Authority}
    {fleet : Fleet Application} {stream : StreamId} {core : State Application} {keeper : KeeperId}
    {basis : Basis Application} {inspection : Inspection (StreamId × Basis Application)}
    (coupled : Coupled fleet stream core)
    (allowed : (fleet keeper).replicaRestartAllowed keeper stream basis inspection)
    (exactLog : basis.log = core.durable keeper) :
    let restarted := (fleet keeper).replace stream (.ready basis)
    Step authority keeper (fleet keeper) restarted ∧
      LeaderJournal.Step core (connect core keeper) ∧
      Coupled (update fleet keeper restarted) stream (connect core keeper) := by
  dsimp only
  exact ⟨.restartReplica stream basis inspection allowed,
    connect_refines coupled _ (by simp [Keeper.ready, Keeper.replace, allowed.1]) exactLog⟩

theorem exact_repair_refines [DecidableEq Application] {authority : Authority}
    {fleet : Fleet Application} {stream : StreamId} {core : State Application} {keeper : KeeperId}
    {basis : Basis Application} {inspection : Inspection (StreamId × Basis Application)}
    (coupled : Coupled fleet stream core)
    (allowed : (fleet keeper).repairAllowed keeper stream basis inspection)
    (exactLog : basis.log = core.durable keeper) :
    let repaired := (fleet keeper).replace stream (.ready basis)
    Step authority keeper (fleet keeper) repaired ∧
      LeaderJournal.Step core (connect core keeper) ∧
      Coupled (update fleet keeper repaired) stream (connect core keeper) := by
  dsimp only
  exact ⟨.repairReplica stream basis inspection allowed,
    connect_refines coupled _ (by simp [Keeper.ready, Keeper.replace, allowed.1]) exactLog⟩

/-- Normal replication updates online media to the exact resulting log.
    The learner may use this step because membership gates voting and acks. -/
theorem checked_durable_copy [DecidableEq Application] {authority : Authority}
    {fleet : Fleet Application} {stream : StreamId} {core : State Application} {keeper : KeeperId}
    (coupled : Coupled fleet stream core) (active : core.active) (online : core.online keeper = true)
    {incoming : Log Application} (issued : incoming <+: core.issued) :
    ∃ written,
      Step authority keeper (fleet keeper) written ∧
      LeaderJournal.Step core (core.replicate keeper incoming) ∧
      Coupled (update fleet keeper written) stream (core.replicate keeper incoming) := by
  obtain ⟨before, ready, _⟩ := coupled keeper online
  let after := { before with log := (core.replicate keeper incoming).durable keeper }
  let written := (fleet keeper).replace stream (.ready after)
  refine ⟨written, .save stream before after ready (before.hard.carriesRefl),
    .replicate keeper core.term incoming active rfl online issued, ?_⟩
  intro node reachable
  by_cases same : node = keeper
  · subst node
    have shared : (fleet keeper).shared = .serving := by
      unfold Keeper.ready at ready
      split at ready <;> simp_all
    exact ⟨after, by simp [written, Keeper.ready, Keeper.replace, shared], rfl⟩
  · obtain ⟨basis, present, history⟩ := coupled node reachable
    exact ⟨basis, by simpa [update, same] using present,
      by simpa [State.replicate, update, same] using history⟩

/-- Healthy reads use the unchanged applied-prefix proof. The service
    boundary learns a response only from an available, checked replica. -/
def HealthyPage [DecidableEq Payload] (fleet : Fleet (Request Payload)) (stream : StreamId)
    (core : Cluster Payload) (keeper : KeeperId) (start limit : Nat) (page : Page Payload) : Prop :=
  CanRespond fleet stream core keeper ∧ readPage (appliedView core keeper) start limit = .ok page

theorem checked_page_returns_committed_bytes [DecidableEq Payload] {members : List KeeperId}
    {fleet : Fleet (Request Payload)} {stream : StreamId} {core : Cluster Payload}
    {keeper start limit offset : Nat} {page : Page Payload} {payload : Payload}
    (reached : Reachable members core)
    (read : HealthyPage fleet stream core keeper start limit page)
    (item : page.records[offset]? = some payload) :
    page.floor ≤ start + offset ∧ start + offset ≤ page.head ∧
      (committedView core).record (start + offset) = some payload :=
  local_page_returns_committed_bytes reached read.2 item

theorem quarantine_refines [DecidableEq Application] {authority : Authority}
    {fleet : Fleet Application} {stream : StreamId} {core : State Application} {keeper : KeeperId}
    {basis : Basis Application} (coupled : Coupled fleet stream core)
    (known : ((fleet keeper).replicas stream).basis = some basis) :
    let quarantined := (fleet keeper).quarantine stream basis
    Step authority keeper (fleet keeper) quarantined ∧
      LeaderJournal.Step core (disconnect core keeper) ∧
      Coupled (update fleet keeper quarantined) stream (disconnect core keeper) ∧
      ¬ CanRespond (update fleet keeper quarantined) stream core keeper := by
  dsimp only
  obtain ⟨fail, safe⟩ := disconnect_refines coupled keeper ((fleet keeper).quarantine stream basis)
  refine ⟨.corruptReplica stream basis known, fail, safe, ?_⟩
  intro response
  obtain ⟨other, ready⟩ := response.2
  have unavailable := quarantine_unready (fleet keeper) stream basis
  simp only [update_same, unavailable] at ready
  contradiction

theorem quarantine_preserves_other_group {fleet : Fleet Application}
    {stream other : StreamId} {core : State Application} {keeper : KeeperId}
    (coupled : Coupled fleet other core) (different : other ≠ stream) (basis : Basis Application) :
    Coupled (update fleet keeper ((fleet keeper).quarantine stream basis)) other core := by
  intro node online
  obtain ⟨saved, ready, history⟩ := coupled node online
  by_cases same : node = keeper
  · subst node
    have stays := (corrupt_replica_isolated (fleet keeper) stream other basis different).2
    exact ⟨saved, by simpa only [update_same, stays] using ready, history⟩
  · exact ⟨saved, by simpa [update, same] using ready, history⟩

theorem corrupt_shared_refines [DecidableEq Application] {authority : Authority}
    {fleet : Fleet Application} {keeper : KeeperId} (groups : StreamId → State Application)
    (coupled : ∀ stream, Coupled fleet stream (groups stream))
    (used : (fleet keeper).shared ≠ .unused) :
    Step authority keeper (fleet keeper) (fleet keeper).disable ∧
      ∀ stream, LeaderJournal.Step (groups stream) (disconnect (groups stream) keeper) ∧
        Coupled (update fleet keeper (fleet keeper).disable) stream (disconnect (groups stream) keeper) ∧
        ¬ CanRespond (update fleet keeper (fleet keeper).disable) stream (groups stream) keeper := by
  refine ⟨.corruptShared used, ?_⟩
  intro stream
  obtain ⟨fail, safe⟩ := disconnect_refines (coupled stream) keeper (fleet keeper).disable
  refine ⟨fail, safe, ?_⟩
  intro response
  obtain ⟨basis, ready⟩ := response.2
  simp only [update_same, corrupt_shared_disables_all] at ready
  contradiction

theorem cannot_vote_or_ack_without_response {fleet : Fleet Application} {core : State Application}
    {stream : StreamId} {configuration : Configuration} {keeper candidate : KeeperId}
    {term : Nat} {cut : Log Application}
    (unavailable : ¬ CanRespond fleet stream core keeper) :
    ¬ CanVote fleet stream core configuration keeper candidate term ∧
      ¬ CanAcknowledge fleet stream core configuration keeper cut := by
  constructor
  · rintro ⟨online, _, basis, ready, _⟩
    exact unavailable ⟨online, basis, ready⟩
  · rintro ⟨online, _, basis, ready, _⟩
    exact unavailable ⟨online, basis, ready⟩

#print axioms checked_genesis_starts_closed
#print axioms checked_joint_issue_refines
#print axioms head_confirmation_uses_healthy_replicas
#print axioms same_term_vote_reply_unique
#print axioms checked_commit_ack
#print axioms healthy_acknowledgements_refine_commit
#print axioms healthy_votes_refine_election
#print axioms checked_page_returns_committed_bytes
#print axioms joint_issue_requires_exact_learner_cut
#print axioms trusted_restart_refines
#print axioms exact_repair_refines
#print axioms checked_durable_copy
#print axioms quarantine_refines
#print axioms quarantine_preserves_other_group
#print axioms corrupt_shared_refines
#print axioms cannot_vote_or_ack_without_response

end Logkeeper.LeaderJournal.Installation
