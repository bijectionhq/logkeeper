import Logkeeper.LeaderJournal.Placement
import Logkeeper.LeaderJournal.Recovery

namespace Logkeeper.LeaderJournal.Bootstrap

set_option warningAsError true

structure Genesis where
  incarnation : Nat
  members : List KeeperId
  deriving DecidableEq

abbrev Catalog := Nat → Option Genesis

/-- An atomic put-if-absent at the bootstrap boundary. Later routing hints
    have their own lifetime and leave this binding intact. -/
def bind (catalog : Catalog) (stream : Nat) (genesis : Genesis) : Catalog :=
  match catalog stream with
  | some _ => catalog
  | none => update catalog stream (some genesis)

theorem absent_gets_exact_genesis {catalog : Catalog} {stream : Nat}
    (absent : catalog stream = none) (genesis : Genesis) :
    bind catalog stream genesis stream = some genesis := by
  simp [bind, absent]

theorem binding_survives {catalog : Catalog} {stream changed : Nat} {chosen : Genesis}
    (installed : catalog stream = some chosen) (proposal : Genesis) :
    bind catalog changed proposal stream = some chosen := by
  by_cases same : changed = stream
  · subst changed
    simp [bind, installed]
  · cases target : catalog changed <;> simp [bind, target, update, Ne.symm same, installed]

theorem competing_create_cannot_install_another_genesis {catalog : Catalog} {stream : Nat}
    (absent : catalog stream = none) (first second : Genesis) :
    bind (bind catalog stream first) stream second stream = some first :=
  binding_survives (absent_gets_exact_genesis absent first) second

abbrev StreamId := Nat

inductive CatalogHealth where
  | trusted
  | unavailable
  | lost
  deriving DecidableEq

inductive Lookup where
  | unknown
  | known (genesis : Option Genesis)
  deriving DecidableEq

structure StagedRoute where
  version : Nat
  oldMembers : List KeeperId
  newMembers : List KeeperId
  deriving DecidableEq

structure Directory where
  health : CatalogHealth
  /-- Ghost record of immutable bindings. Lost media cannot supply evidence of
      absence or replace this authority with a new empty catalog. -/
  bindings : Catalog
  hints : StreamId → List KeeperId
  staged : StreamId → Option StagedRoute
  /-- Evidence retained by the mover after a trusted staging transaction. -/
  cachedStage : StreamId → Option StagedRoute

def Directory.empty : Directory :=
  ⟨.trusted, fun _ => none, fun _ => [], fun _ => none, fun _ => none⟩

def Directory.lookup (directory : Directory) (stream : StreamId) : Lookup :=
  if directory.health = .trusted then .known (directory.bindings stream) else .unknown

def Directory.create (directory : Directory) (stream : StreamId) (proposal : Genesis) : Directory :=
  { directory with bindings := bind directory.bindings stream proposal }

def Directory.canCreate (directory : Directory) (registry : Placement.Registry)
    (stream : StreamId) (proposal : Genesis) : Prop :=
  Placement.Roster registry proposal.members ∧
    (directory.lookup stream = .known none ∨ directory.lookup stream = .known (some proposal))

def Directory.canStage (directory : Directory) (registry : Placement.Registry)
    (stream : StreamId) (core : State Application) (route : StagedRoute) : Prop :=
  (∃ genesis, directory.lookup stream = .known (some genesis) ∧
    core.genesis = .stable genesis.members) ∧
  core.configuration = .stable route.oldMembers ∧
  route.version = configurationVersion core.committed ∧ Placement.Roster registry route.newMembers

def Directory.stage (directory : Directory) (stream : StreamId) (route : StagedRoute) :
    Directory :=
  { directory with
    hints := update directory.hints stream (route.oldMembers ++ route.newMembers)
    staged := update directory.staged stream (some route)
    cachedStage := update directory.cachedStage stream (some route) }

/-- A lost catalog can be marked trusted only by restoring its exact
    authoritative binding and staged discovery state. -/
inductive CatalogStep (registry : Placement.Registry) : Directory → Directory → Prop
  | disconnect {d} : CatalogStep registry d { d with health := .unavailable }
  | lose {d} : CatalogStep registry d { d with health := .lost }
  | restore {d} (bindings : Catalog) (staged : StreamId → Option StagedRoute)
      (exactBindings : bindings = d.bindings) (exactStaging : staged = d.staged) :
    CatalogStep registry d { d with health := .trusted }
  | create {d} (stream : StreamId) (proposal : Genesis)
      (allowed : d.canCreate registry stream proposal) :
    CatalogStep registry d (d.create stream proposal)
  | stage {d} {Application : Type} (stream : StreamId) (core : State Application)
      (route : StagedRoute) (allowed : d.canStage registry stream core route) :
    CatalogStep registry d (d.stage stream route)
  | forgetStage {d} (stream : StreamId) :
    CatalogStep registry d { d with cachedStage := update d.cachedStage stream none }
  | readStage {d} (stream : StreamId) (trusted : d.health = .trusted) :
    CatalogStep registry d { d with cachedStage := update d.cachedStage stream (d.staged stream) }

inductive CatalogReachable (registry : Placement.Registry) : Directory → Prop
  | empty : CatalogReachable registry Directory.empty
  | step {d next} : CatalogReachable registry d → CatalogStep registry d next →
    CatalogReachable registry next

theorem cached_staging_was_published {registry : Placement.Registry} {d : Directory}
    (trace : CatalogReachable registry d) {stream : StreamId} {route : StagedRoute}
    (known : d.cachedStage stream = some route) : d.staged stream = some route := by
  induction trace with
  | empty => contradiction
  | step _ step prior =>
    cases step with
    | stage stagedStream _ _ _ =>
      by_cases same : stream = stagedStream
      · subst stagedStream
        simpa only [Directory.stage, update_same] using known
      · have previous := prior (by simpa [Directory.stage, update, same] using known)
        simpa [Directory.stage, update, same] using previous
    | forgetStage discarded =>
      by_cases same : stream = discarded
      · subst discarded
        simp only [update_same] at known
        contradiction
      · exact prior (by simpa [update, same] using known)
    | readStage fetched _ =>
      by_cases same : stream = fetched
      · subst fetched
        simpa only [update_same] using known
      · exact prior (by simpa [update, same] using known)
    | _ => exact prior known

/-- A stage can survive later catalog unavailability. The receipt is bound to
    the exact source configuration revision and prospective joint roster. -/
def Directory.allowsIssue (directory : Directory) (stream : StreamId)
    (core : State Application) : Command Application → Prop
  | .configure (.joint oldMembers newMembers) =>
      directory.cachedStage stream = some ⟨configurationVersion core.committed, oldMembers, newMembers⟩
  | _ => True

/-- Only issuing a joint entry borrows catalog staging evidence. The
    remaining consensus steps operate on the journal and eligible peers. -/
theorem checked_issue_refines [DecidableEq Application] {d : Directory} {stream : StreamId}
    {s : State Application} {command : Command Application}
    (active : s.active) (admitted : s.admits command)
    (_allowed : d.allowsIssue stream s command) : LeaderJournal.Step s (s.issue command) :=
  .issue command active admitted

theorem unavailable_is_unknown {d : Directory} (unavailable : d.health ≠ .trusted)
    (stream : StreamId) : d.lookup stream = .unknown := by
  simp [Directory.lookup, unavailable]

theorem unavailable_rejects_create_and_staging {d : Directory}
    (unavailable : d.health ≠ .trusted) (registry : Placement.Registry) (stream : StreamId)
    (proposal : Genesis) (core : State Application) (route : StagedRoute) :
    ¬ d.canCreate registry stream proposal ∧ ¬ d.canStage registry stream core route := by
  simp [Directory.canCreate, Directory.canStage, unavailable_is_unknown unavailable stream]

theorem catalog_step_preserves_genesis {registry : Placement.Registry} {d next : Directory}
    (step : CatalogStep registry d next) {stream : StreamId} {genesis : Genesis}
    (existing : d.bindings stream = some genesis) : next.bindings stream = some genesis := by
  cases step with
  | create _ proposal _ => exact binding_survives existing proposal
  | _ => exact existing

theorem lost_catalog_cannot_restore_empty_over_binding {d : Directory} {stream : StreamId}
    {genesis : Genesis} (existing : d.bindings stream = some genesis) :
    (fun _ => (none : Option Genesis)) ≠ d.bindings := by
  intro empty
  have atStream := congrFun empty stream
  change none = d.bindings stream at atStream
  rw [existing] at atStream
  contradiction

theorem stage_publishes_target_contacts (d : Directory) (stream : StreamId) (route : StagedRoute)
    {keeper : KeeperId} (target : keeper ∈ route.newMembers) :
    keeper ∈ (d.stage stream route).hints stream ∧
      (d.stage stream route).staged stream = some route := by
  simp only [Directory.stage, update_same, List.mem_append]
  exact ⟨Or.inr target, trivial⟩

theorem joint_issue_requires_staged_contacts {d : Directory}
    {stream : StreamId} {s : State Application} {oldMembers newMembers : List KeeperId}
    (registry : Placement.Registry) (trace : CatalogReachable registry d)
    (allowed : d.allowsIssue stream s (.configure (.joint oldMembers newMembers))) :
    d.staged stream = some ⟨configurationVersion s.committed, oldMembers, newMembers⟩ :=
  cached_staging_was_published trace allowed

theorem stale_staging_cannot_authorize_joint {d : Directory}
    {stream : StreamId} {s : State Application} {staged : StagedRoute}
    {oldMembers newMembers : List KeeperId}
    (receipt : d.cachedStage stream = some staged)
    (stale : staged.version ≠ configurationVersion s.committed) :
    ¬ d.allowsIssue stream s (.configure (.joint oldMembers newMembers)) := by
  intro allowed
  exact stale (congrArg StagedRoute.version (Option.some.inj
    (receipt.symm.trans (show d.cachedStage stream = some _ from allowed))))

theorem app_issue_needs_no_catalog (d : Directory) (stream : StreamId)
    (core : State Application) (request : Application) :
    d.allowsIssue stream core (.apply request) := trivial

def Directory.contacts (d : Directory) (stream : StreamId) (known : List KeeperId) : List KeeperId :=
  known ++ if d.health = .trusted then d.hints stream else []

def Directory.eligibleContact (d : Directory) (stream : StreamId) (known : List KeeperId)
    (configuration : Configuration) (keeper : KeeperId) : Prop :=
  keeper ∈ d.contacts stream known ∧ configuration.contains keeper = true

theorem contact_hints_do_not_authorize_votes (d : Directory) (stream : StreamId)
    (known : List KeeperId) (configuration : Configuration) (keeper : KeeperId)
    (excluded : configuration.contains keeper = false) :
    ¬ d.eligibleContact stream known configuration keeper := by
  intro reached
  have member := reached.2
  rw [excluded] at member
  contradiction

/-- Once initialized, a sufficiently reachable authenticated local contact set
    can recover a fresh response without consulting a catalog or its hints. -/
theorem initialized_stream_recovers_without_catalog [DecidableEq Payload] {core : Cluster Payload}
    (sound : Sound core) (d : Directory) (down : d.health ≠ .trusted) (stream : StreamId)
    (known : List KeeperId) (nonempty : known ≠ [])
    (registry : Placement.Registry) (valid : Placement.Valid registry core.configuration)
    (members : ∀ keeper ∈ known, core.configuration.contains keeper = true)
    (settled : ∀ keeper ∈ known, core.candidateConfiguration keeper = core.configuration)
    (majority : core.configuration.quorum known.contains) (online : core.responds known.contains) :
    d.contacts stream known = known ∧
      (∀ keeper ∈ known, registry.authenticated keeper = true) ∧
      ∃ recovered : Cluster Payload, ∃ call : HeadRead core recovered,
        core.committed <+: recovered.committed ∧ call.captured = recovered := by
  refine ⟨by simp [Directory.contacts, down], ?_, ?_⟩
  · intro keeper present
    have counted := members keeper present
    cases current : core.configuration with
    | stable roster =>
      rw [current] at valid counted
      exact valid.authenticated keeper (List.contains_iff_mem.mp counted)
    | joint oldMembers newMembers =>
      rw [current] at valid counted
      have enrolled : keeper ∈ oldMembers ∨ keeper ∈ newMembers := by
        simpa [Configuration.contains] using counted
      rcases enrolled with inOld | inNew
      · exact valid.1.authenticated keeper inOld
      · exact valid.2.authenticated keeper inNew
  · obtain ⟨election⟩ := settled_election_available known nonempty members settled majority online
    obtain ⟨recovered, call, preserved, _, capture, _⟩ := recover_and_serve sound election
    exact ⟨recovered, call, preserved, capture⟩

private theorem final_configuration (genesis : Configuration) (history : Log Application)
    (term : Nat) (members : List KeeperId) :
    configurationAt genesis (history ++ [⟨term, .configure (.stable members)⟩]) =
      .stable members := by simp [configurationAt, List.foldl_append]

/-- A committed joint entry contains the target roster. Finishing it uses
    local consensus evidence, even if the original proposer and catalog are
    gone. A reachable eligible leader and a new-roster quorum are required. -/
theorem committed_joint_finishes_without_catalog [DecidableEq Application]
    {s : State Application} {oldMembers newMembers : List KeeperId}
    (sound : Sound s) (d : Directory) (stream : StreamId)
    (joint : s.configuration = .joint oldMembers newMembers)
    (settled : s.effectiveConfiguration = s.configuration) (active : s.active)
    (voters : List KeeperId) (quorum : (.stable newMembers : Configuration).quorum voters.contains)
    (online : s.responds voters.contains) :
    ∃ issued final : State Application,
      d.allowsIssue stream s (.configure (.stable newMembers)) ∧
      LeaderJournal.Step s issued ∧ LeaderJournal.Trace issued final ∧
      final.configuration = .stable newMembers ∧ s.committed <+: final.committed := by
  have admitted : s.admits (.configure (.stable newMembers)) := ⟨settled, joint.symm ▸ .finish, trivial⟩
  let issued := s.issue (.configure (.stable newMembers))
  let cut := issued.issued
  let replicated := issued.replicateTo voters cut
  have copy : LeaderJournal.Trace issued replicated :=
    replicate_to_trace issued voters cut active
      (fun keeper member => online keeper (List.contains_iff_mem.mpr member)) List.prefix_rfl
  have target : configurationAt replicated.genesis cut = .stable newMembers :=
    final_configuration s.genesis s.issued s.term newMembers
  have durable : replicated.supports voters.contains cut := by
    intro keeper voted
    exact replicate_to_covers issued voters cut (List.contains_iff_mem.mp voted)
  have carry : s.committed <+: cut := sound.leaderContains.trans (List.prefix_append _ _)
  have current : lastTerm cut = s.term := by
    simp [cut, issued, State.issue, lastTerm, List.getLast?_append]
  let final : State Application :=
    { replicated with
      committed := cut
      leader := replicated.leader.filter ((configurationAt replicated.genesis cut).contains) }
  have commit : LeaderJournal.Step replicated final :=
    .commit cut voters.contains active carry.length_le List.prefix_rfl current rfl
      (target.symm ▸ quorum) durable
  exact ⟨issued, final, trivial, checked_issue_refines active admitted (d := d) (stream := stream) trivial,
    copy.trans commit.trace, target, carry⟩

/-- If a leader died after issuing the final entry, a qualified new-term
    election can carry and commit it with the normal barrier. -/
theorem pending_final_recovers_without_catalog [DecidableEq Payload]
    {core : Cluster Payload} {oldMembers newMembers : List KeeperId} (sound : Sound core)
    (_joint : core.configuration = .joint oldMembers newMembers)
    (election : Election core)
    (target : core.candidateConfiguration election.candidate = .stable newMembers) :
    ∃ recovered : Cluster Payload, ∃ call : HeadRead core recovered,
      core.committed <+: recovered.committed ∧
      recovered.configuration = .stable newMembers ∧ call.captured = recovered := by
  obtain ⟨recovered, call, carry, history, capture, _, _⟩ := recover_and_serve sound election
  refine ⟨recovered, call, carry, ?_, capture⟩
  have genesis := trace_genesis call.invokedBeforeCapture
  rw [capture] at genesis
  unfold State.configuration
  rw [history, ← genesis]
  change configurationAt core.genesis (core.durable election.candidate ++
    [⟨election.term, .barrier⟩]) = _
  have same : configurationAt core.genesis (core.durable election.candidate ++
      [⟨election.term, .barrier⟩]) = core.candidateConfiguration election.candidate := by
    simp [State.candidateConfiguration, configurationAt, List.foldl_append]
  exact same.trans target

#print axioms cached_staging_was_published
#print axioms unavailable_rejects_create_and_staging
#print axioms catalog_step_preserves_genesis
#print axioms lost_catalog_cannot_restore_empty_over_binding
#print axioms stage_publishes_target_contacts
#print axioms joint_issue_requires_staged_contacts
#print axioms stale_staging_cannot_authorize_joint
#print axioms contact_hints_do_not_authorize_votes
#print axioms initialized_stream_recovers_without_catalog
#print axioms committed_joint_finishes_without_catalog
#print axioms pending_final_recovers_without_catalog

#print axioms competing_create_cannot_install_another_genesis

end Logkeeper.LeaderJournal.Bootstrap
