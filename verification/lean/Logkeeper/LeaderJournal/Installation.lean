import Logkeeper.LeaderJournal
import Logkeeper.LeaderJournal.Placement

namespace Logkeeper.LeaderJournal.Installation

set_option warningAsError true

abbrev StreamId := Nat

structure HardState where
  term : Nat
  vote : Option KeeperId
  deriving DecidableEq

def HardState.carries (before after : HardState) : Prop :=
  before.term ≤ after.term ∧
    (before.term = after.term → ∀ voter, before.vote = some voter → after.vote = some voter)

theorem HardState.carriesRefl (hard : HardState) : hard.carries hard :=
  ⟨Nat.le_refl _, fun _ _ selected => selected⟩

theorem HardState.carriesTrans {a b c : HardState} (ab : a.carries b) (bc : b.carries c) :
    a.carries c := by
  refine ⟨Nat.le_trans ab.1 bc.1, ?_⟩
  intro same voter selected
  have first := ab.1
  have second := bc.1
  exact bc.2 (by omega) voter (ab.2 (by omega) voter selected)

structure Basis (Application : Type) where
  hard : HardState
  log : Log Application

def Basis.empty : Basis Application := ⟨⟨0, none⟩, []⟩

/-- 'Verified' denotes the output of identity, integrity and scope checks on
    durable media. Uncertain or partial data has no verified constructor. -/
inductive Inspection (Content : Type) where
  | missing
  | incomplete
  | untrusted
  | verified (owner : KeeperId) (content : Content)

inductive Shared where
  | unused
  | installed
  | serving
  | disabled
  deriving DecidableEq

inductive Replica (Application : Type) where
  | absent
  | stopped (basis : Basis Application)
  | ready (basis : Basis Application)
  | quarantined (basis : Basis Application)

/-- The basis in a quarantined replica is the last trusted logical state.
    It is a proof witness and grants no permission to serve its bytes. -/
def Replica.basis : Replica Application → Option (Basis Application)
  | .absent => none
  | .stopped basis | .ready basis | .quarantined basis => some basis

def Replica.stop : Replica Application → Replica Application
  | .ready basis => .stopped basis
  | other => other

structure Keeper (Application : Type) where
  shared : Shared
  replicas : StreamId → Replica Application

def Keeper.fresh : Keeper Application := ⟨.unused, fun _ => .absent⟩

def Keeper.ready (keeper : Keeper Application) (stream : StreamId) : Option (Basis Application) :=
  match keeper.shared, keeper.replicas stream with
  | .serving, .ready b => some b
  | _, _ => none

def Keeper.restartAllowed (state : Keeper Application) (keeper : KeeperId)
    (inspection : Inspection Unit) : Prop :=
  state.shared = .installed ∧ inspection = .verified keeper ()

def Keeper.replicaRestartAllowed (state : Keeper Application) (keeper : KeeperId) (stream : StreamId)
    (basis : Basis Application) (inspection : Inspection (StreamId × Basis Application)) : Prop :=
  state.shared = .serving ∧ state.replicas stream = .stopped basis ∧
    inspection = .verified keeper (stream, basis)

def Keeper.repairAllowed (state : Keeper Application) (keeper : KeeperId) (stream : StreamId)
    (basis : Basis Application) (inspection : Inspection (StreamId × Basis Application)) : Prop :=
  state.shared = .serving ∧ state.replicas stream = .quarantined basis ∧
    inspection = .verified keeper (stream, basis)

def Keeper.replace (state : Keeper Application) (stream : StreamId) (replica : Replica Application) :
    Keeper Application :=
  { state with replicas := update state.replicas stream replica }

def Keeper.quarantine (state : Keeper Application) (stream : StreamId) (basis : Basis Application) :
    Keeper Application :=
  state.replace stream (.quarantined basis)

def Keeper.disable (state : Keeper Application) : Keeper Application :=
  { state with shared := .disabled }

/-- The registry's enrollment authority survives directory loss. It supplies
    one immutable state machine per authenticated keeper incarnation and
    authorizes stream installation separately from process restart. -/
structure Authority where
  registry : Placement.Registry
  enroll : KeeperId → StreamId → Prop

inductive Step (authority : Authority) (keeper : KeeperId) :
    Keeper Application → Keeper Application → Prop
  | installMedia {s} (fresh : s.shared = .unused)
      (authorized : authority.registry.authenticated keeper = true) :
      Step authority keeper s { s with shared := .installed }
  | restartMedia {s} (inspection : Inspection Unit)
      (allowed : s.restartAllowed keeper inspection) :
      Step authority keeper s { s with shared := .serving }
  | stopMedia {s} (online : s.shared = .serving) :
      Step authority keeper s { s with shared := .installed, replicas := fun stream => (s.replicas stream).stop }
  | installReplica {s} (stream : StreamId) (run : s.shared = .serving)
      (unused : s.replicas stream = .absent) (authorized : authority.enroll keeper stream) :
      Step authority keeper s (s.replace stream (.stopped Basis.empty))
  | restartReplica {s} (stream : StreamId) (basis : Basis Application)
      (inspection : Inspection (StreamId × Basis Application))
      (allowed : s.replicaRestartAllowed keeper stream basis inspection) :
      Step authority keeper s (s.replace stream (.ready basis))
  | stopReplica {s} (stream : StreamId) (basis : Basis Application)
      (ready : s.replicas stream = .ready basis) :
      Step authority keeper s (s.replace stream (.stopped basis))
  | save {s} (stream : StreamId) (before after : Basis Application)
      (ready : s.ready stream = some before) (hard : before.hard.carries after.hard) :
      Step authority keeper s (s.replace stream (.ready after))
  | corruptReplica {s} (stream : StreamId) (basis : Basis Application)
      (known : (s.replicas stream).basis = some basis) :
      Step authority keeper s (s.quarantine stream basis)
  | repairReplica {s} (stream : StreamId) (basis : Basis Application)
      (inspection : Inspection (StreamId × Basis Application))
      (allowed : s.repairAllowed keeper stream basis inspection) :
      Step authority keeper s (s.replace stream (.ready basis))
  | corruptShared {s} (installed : s.shared ≠ .unused) :
      Step authority keeper s s.disable

inductive Trace (authority : Authority) (keeper : KeeperId) :
    Keeper Application → Keeper Application → Prop
  | nil {s} : Trace authority keeper s s
  | next {first before after} : Trace authority keeper first before →
      Step authority keeper before after → Trace authority keeper first after

theorem untrusted_restart_refused {s : Keeper Application} {keeper : KeeperId}
    {inspection : Inspection Unit} (unverified : inspection ≠ .verified keeper ()) :
    ¬ s.restartAllowed keeper inspection :=
  fun allowed => unverified allowed.2

theorem untrusted_replica_restart_refused {s : Keeper Application} {keeper : KeeperId}
    {stream : StreamId} {basis : Basis Application} {inspection : Inspection (StreamId × Basis Application)}
    (unverified : inspection ≠ .verified keeper (stream, basis)) :
    ¬ s.replicaRestartAllowed keeper stream basis inspection :=
  fun allowed => unverified allowed.2.2

theorem installed_identity_is_authenticated {authority : Authority} {keeper : KeeperId}
    {s : Keeper Application} (trace : Trace authority keeper Keeper.fresh s)
    (used : s.shared ≠ .unused) : authority.registry.authenticated keeper = true := by
  induction trace with
  | nil => exact (used rfl).elim
  | next _ step prior =>
    cases step with
    | installMedia _ registered => exact registered
    | restartMedia _ allowed => exact prior (by simp [allowed.1])
    | stopMedia serving => exact prior (by simp [serving])
    | corruptShared enrolled => exact prior enrolled
    | _ => exact prior used

theorem installed_identity_never_unused {authority : Authority} {keeper : KeeperId}
    {before after : Keeper Application} (trace : Trace authority keeper before after)
    (used : before.shared ≠ .unused) : after.shared ≠ .unused := by
  induction trace with
  | nil => exact used
  | next _ step prior =>
    cases step <;> first | exact prior | exact fun equal => Shared.noConfusion equal

theorem disabled_identity_stays_disabled {authority : Authority} {keeper : KeeperId}
    {before after : Keeper Application} (trace : Trace authority keeper before after)
    (disabled : before.shared = .disabled) : after.shared = .disabled := by
  induction trace with
  | nil => exact disabled
  | next _ step prior =>
    cases step with
    | installMedia fresh _ => exact False.elim (by rw [prior] at fresh; contradiction)
    | restartMedia _ allowed => exact False.elim (by have := allowed.1; rw [prior] at this; contradiction)
    | stopMedia online => exact False.elim (by rw [prior] at online; contradiction)
    | corruptShared => rfl
    | _ => exact prior

private theorem Replica.stop_basis (replica : Replica Application) :
    replica.stop.basis = replica.basis := by
  cases replica <;> rfl

theorem step_keeps_hard_state {authority : Authority} {keeper : KeeperId}
    {before after : Keeper Application} (step : Step authority keeper before after)
    {stream : StreamId} {basis : Basis Application}
    (held : (before.replicas stream).basis = some basis) :
    ∃ next, (after.replicas stream).basis = some next ∧ basis.hard.carries next.hard := by
  have unchanged (same : (after.replicas stream).basis = (before.replicas stream).basis) :
      ∃ next, (after.replicas stream).basis = some next ∧ basis.hard.carries next.hard :=
    ⟨basis, same.trans held, basis.hard.carriesRefl⟩
  cases step with
  | stopMedia => exact unchanged (Replica.stop_basis _)
  | installReplica target _ absent _ =>
    by_cases same : stream = target
    · subst target
      rw [absent] at held
      contradiction
    · exact unchanged (by simp [Keeper.replace, update, same])
  | restartReplica target old _ allowed =>
    by_cases same : stream = target
    · subst target
      exact unchanged (by simp [Keeper.replace, allowed.2.1, Replica.basis])
    · exact unchanged (by simp [Keeper.replace, update, same])
  | stopReplica target old ready =>
    by_cases same : stream = target
    · subst target
      exact unchanged (by simp [Keeper.replace, ready, Replica.basis])
    · exact unchanged (by simp [Keeper.replace, update, same])
  | save target old next ready carries =>
    by_cases same : stream = target
    · subst target
      have wasReady : (before.replicas stream).basis = some old := by
        unfold Keeper.ready at ready
        split at ready <;> simp_all [Replica.basis]
      have exactBasis := Option.some.inj (held.symm.trans wasReady)
      exact ⟨next, by simp [Keeper.replace, Replica.basis], exactBasis.symm ▸ carries⟩
    · exact unchanged (by simp [Keeper.replace, update, same])
  | corruptReplica target old known =>
    by_cases same : stream = target
    · subst target
      apply unchanged
      simp only [Keeper.quarantine, Keeper.replace, update_same, Replica.basis]
      exact known.symm
    · exact unchanged (by simp [Keeper.quarantine, Keeper.replace, update, same])
  | repairReplica target old _ allowed =>
    by_cases same : stream = target
    · subst target
      exact unchanged (by simp [Keeper.replace, allowed.2.1, Replica.basis])
    · exact unchanged (by simp [Keeper.replace, update, same])
  | _ => exact unchanged rfl

theorem trace_keeps_hard_state {authority : Authority} {keeper : KeeperId}
    {before after : Keeper Application} (trace : Trace authority keeper before after)
    {stream : StreamId} {basis : Basis Application}
    (held : (before.replicas stream).basis = some basis) :
    ∃ next, (after.replicas stream).basis = some next ∧ basis.hard.carries next.hard := by
  induction trace with
  | nil => exact ⟨basis, held, basis.hard.carriesRefl⟩
  | next _ step prior =>
    obtain ⟨middle, present, first⟩ := prior
    obtain ⟨last, final, second⟩ := step_keeps_hard_state step present
    exact ⟨last, final, HardState.carriesTrans first second⟩

theorem same_term_vote_survives_media_events {authority : Authority} {keeper voter : KeeperId}
    {before after : Keeper Application} (trace : Trace authority keeper before after)
    {stream : StreamId} {old next : Basis Application}
    (beforeBasis : (before.replicas stream).basis = some old)
    (afterBasis : (after.replicas stream).basis = some next)
    (voted : old.hard.vote = some voter) (sameTerm : old.hard.term = next.hard.term) :
    next.hard.vote = some voter := by
  obtain ⟨kept, present, carries⟩ := trace_keeps_hard_state trace beforeBasis
  have same : kept = next := Option.some.inj (present.symm.trans afterBasis)
  subst kept
  exact carries.2 sameTerm voter voted

theorem quarantine_unready (s : Keeper Application) (stream : StreamId)
    (basis : Basis Application) : (s.quarantine stream basis).ready stream = none := by
  cases shared : s.shared <;> simp [Keeper.ready, Keeper.quarantine, Keeper.replace, shared]

theorem Keeper.ready_basis {s : Keeper Application} {stream : StreamId} {basis : Basis Application}
    (ready : s.ready stream = some basis) : (s.replicas stream).basis = some basis := by
  unfold Keeper.ready at ready
  split at ready <;> simp_all [Replica.basis]

theorem corrupt_replica_isolated (s : Keeper Application) (stream other : StreamId)
    (basis : Basis Application) (different : other ≠ stream) :
    (s.quarantine stream basis).ready stream = none ∧
      (s.quarantine stream basis).ready other = s.ready other := by
  constructor
  · exact quarantine_unready s stream basis
  · simp [Keeper.ready, Keeper.quarantine, Keeper.replace, update, different]

theorem corrupt_shared_disables_all (s : Keeper Application) :
    ∀ stream, s.disable.ready stream = none := fun _ => rfl

theorem repair_requires_exact_basis {s : Keeper Application} {keeper : KeeperId}
    {stream : StreamId} {basis next : Basis Application}
    (allowed : s.repairAllowed keeper stream basis (.verified keeper (stream, next))) :
    next.log = basis.log ∧ next.hard = basis.hard := by
  have same := Inspection.verified.inj allowed.2.2
  have equal : next = basis := congrArg Prod.snd same.2
  subst next
  exact ⟨rfl, rfl⟩

#print axioms installed_identity_is_authenticated
#print axioms installed_identity_never_unused
#print axioms disabled_identity_stays_disabled
#print axioms same_term_vote_survives_media_events
#print axioms corrupt_replica_isolated
#print axioms corrupt_shared_disables_all
#print axioms repair_requires_exact_basis

end Logkeeper.LeaderJournal.Installation
