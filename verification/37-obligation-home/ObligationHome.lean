import Init.Omega

set_option warningAsError true

namespace ObligationHome

variable {Key Binding : Type} [DecidableEq Key]

inductive Obligation (Binding : Type) where
  | absent
  | pending (binding : Binding)
  | discharged (binding : Binding)

structure Home (Key Binding : Type) where
  owner : Nat
  locator : Nat
  stopped : Nat → Prop
  sealed : Bool
  book : Key → Obligation Binding

def initial (book : Key → Obligation Binding) : Home Key Binding :=
  ⟨0, 0, fun _ => False, false, book⟩

def publish (state : Home Key Binding) (candidate : Nat) : Home Key Binding :=
  {state with locator := candidate}

def stop (state : Home Key Binding) (site : Nat) : Home Key Binding :=
  {state with stopped := fun observed => observed = site ∨ state.stopped observed}

def install (state : Home Key Binding) (image : Key → Obligation Binding) : Home Key Binding :=
  {state with owner := state.owner + 1, sealed := false, book := image}

def discharge (state : Home Key Binding) (key : Key) (binding : Binding) : Home Key Binding :=
  {state with book := fun observed => if observed = key then .discharged binding else state.book observed}

def CanPublish (state : Home Key Binding) (candidate : Nat) : Prop :=
  state.locator ≤ candidate ∧ candidate ≤ state.owner

def CanStop (state : Home Key Binding) (site : Nat) : Prop :=
  site < state.owner ∧ site < state.locator

def ExactImage (state : Home Key Binding) (image : Key → Obligation Binding) : Prop :=
  image = state.book

def ValidSettlement (settled : Key → Binding → Prop) (key : Key) (binding : Binding) : Prop :=
  settled key binding

inductive Step (settled : Key → Binding → Prop) : Home Key Binding → Home Key Binding → Prop
  | seal {state} (openBook : state.sealed = false) (currentRoute : state.locator = state.owner) :
      Step settled state {state with sealed := true}
  | install {state} (image : Key → Obligation Binding) (sealed : state.sealed = true)
      (certified : ExactImage state image) :
      Step settled state (install state image)
  | publish {state} (candidate : Nat) (installed : CanPublish state candidate) :
      Step settled state (publish state candidate)
  | stop {state} (site : Nat) (covered : CanStop state site) :
      Step settled state (stop state site)
  | discharge {state} (key : Key) (binding : Binding) (openBook : state.sealed = false)
      (pending : state.book key = .pending binding) (proof : ValidSettlement settled key binding) :
      Step settled state (discharge state key binding)

inductive Trace (settled : Key → Binding → Prop) : Home Key Binding → Home Key Binding → Prop
  | same (state) : Trace settled state state
  | next {first before after} : Trace settled first before → Step settled before after →
      Trace settled first after

structure RouteSound (state : Home Key Binding) : Prop where
  installed : state.locator ≤ state.owner
  liveRoute : ∀ site, state.stopped site → site < state.locator

omit [DecidableEq Key] in
theorem initial_route_is_sound (book : Key → Obligation Binding) : RouteSound (initial book) :=
  ⟨Nat.le_refl _, fun _ impossible => False.elim impossible⟩

theorem step_preserves_route_soundness
    {settled : Key → Binding → Prop} {before after : Home Key Binding}
    (sound : RouteSound before) (step : Step settled before after) : RouteSound after := by
  cases step with
  | install _ _ _ =>
      exact ⟨Nat.le_trans sound.installed (Nat.le_succ _), sound.liveRoute⟩
  | publish _ installed =>
      exact ⟨installed.2, fun site stopped => Nat.lt_of_lt_of_le (sound.liveRoute site stopped) installed.1⟩
  | stop site covered =>
      refine ⟨sound.installed, ?_⟩
      intro observed stopped
      change observed = site ∨ before.stopped observed at stopped
      rcases stopped with same | old
      · exact same ▸ covered.2
      · exact sound.liveRoute observed old
  | _ => exact ⟨sound.installed, sound.liveRoute⟩

theorem trace_preserves_route_soundness
    {settled : Key → Binding → Prop} {first last : Home Key Binding}
    (sound : RouteSound first) (trace : Trace settled first last) : RouteSound last := by
  induction trace with
  | same => exact sound
  | next _ step prior => exact step_preserves_route_soundness prior step

theorem locator_versions_do_not_go_back
    {settled : Key → Binding → Prop} {first last : Home Key Binding}
    (trace : Trace settled first last) : first.locator ≤ last.locator := by
  induction trace with
  | same => exact Nat.le_refl _
  | next _ step prior =>
      cases step with
      | publish _ installed => exact Nat.le_trans prior installed.1
      | _ => exact prior

omit [DecidableEq Key] in
theorem exact_install_leaves_original_keys_and_bindings
    {state : Home Key Binding} {image : Key → Obligation Binding}
    (exactImage : ExactImage state image) : (install state image).book = state.book := by
  exact exactImage

def Protected (settled : Key → Binding → Prop) (state : Home Key Binding) (key : Key)
    (binding : Binding) : Prop :=
  state.book key = .pending binding ∨ (state.book key = .discharged binding ∧ settled key binding)

theorem step_preserves_exact_debt_or_settlement
    {settled : Key → Binding → Prop} {before after : Home Key Binding} {key : Key} {binding : Binding}
    (retained : Protected settled before key binding) (step : Step settled before after) :
    Protected settled after key binding := by
  cases step with
  | install _ _ certified =>
      simpa only [Protected, exact_install_leaves_original_keys_and_bindings certified] using retained
  | discharge address expected _ pending proof =>
      by_cases same : key = address
      · subst address
        rcases retained with awaiting | ⟨already, _⟩
        · have equal := Obligation.pending.inj (pending.symm.trans awaiting)
          subst expected
          have exactProof : settled key binding := by
            exact proof
          exact Or.inr ⟨by simp [discharge], exactProof⟩
        · rw [pending] at already
          cases already
      · simpa [Protected, discharge, same] using retained
  | _ => exact retained

theorem trace_preserves_exact_debt_or_settlement
    {settled : Key → Binding → Prop} {first last : Home Key Binding} {key : Key} {binding : Binding}
    (pending : first.book key = .pending binding) (trace : Trace settled first last) :
    Protected settled last key binding := by
  induction trace with
  | same => exact Or.inl pending
  | next _ step prior => exact step_preserves_exact_debt_or_settlement prior step

def ResolvesCurrent (reachable : Nat → Prop) (state : Home Key Binding) : Prop :=
  state.locator = state.owner ∧ reachable state.locator ∧ ¬ state.stopped state.locator

omit [DecidableEq Key] in
theorem current_resolution_needs_no_retired_owner_records
    {reachable : Nat → Prop} {state : Home Key Binding} (sound : RouteSound state) :
    ResolvesCurrent reachable state ↔ state.locator = state.owner ∧ reachable state.locator := by
  constructor
  · rintro ⟨published, online, _⟩
    exact ⟨published, online⟩
  · rintro ⟨published, online⟩
    refine ⟨published, online, ?_⟩
    intro stopped
    exact Nat.lt_irrefl _ (sound.liveRoute _ stopped)

theorem can_recover_exact_unsettled_debt_after_old_endpoints_stop
    {settled : Key → Binding → Prop} {first last : Home Key Binding}
    {reachable : Nat → Prop} {key : Key} {binding : Binding}
    (sound : RouteSound first) (pending : first.book key = .pending binding)
    (trace : Trace settled first last) (published : last.locator = last.owner)
    (ownerReachable : reachable last.owner) (stillOwed : ¬ settled key binding) :
    ResolvesCurrent reachable last ∧ last.book key = .pending binding := by
  have route := trace_preserves_route_soundness sound trace
  have exactDebt := trace_preserves_exact_debt_or_settlement pending trace
  exact ⟨(current_resolution_needs_no_retired_owner_records route).mpr
    ⟨published, published.symm ▸ ownerReachable⟩,
    exactDebt.resolve_right (fun closed => stillOwed closed.2)⟩

theorem can_move_and_stop_without_discharging
    (settled : Key → Binding → Prop) (state : Home Key Binding)
    (active : state.sealed = false) (currentRoute : state.locator = state.owner) :
    ∃ after, Trace settled state after ∧ after.stopped state.owner ∧
      after.locator = state.owner + 1 ∧ after.book = state.book := by
  let sealed := {state with sealed := true}
  let installed := install sealed sealed.book
  let published := publish installed installed.owner
  let stopped := stop published state.owner
  have publishable : CanPublish installed installed.owner := by
    constructor
    · change state.locator ≤ state.owner + 1
      omega
    · exact Nat.le_refl _
  have stoppable : CanStop published state.owner := by
    exact ⟨Nat.lt_succ_self _, Nat.lt_succ_self _⟩
  have certified : ExactImage sealed sealed.book := by
    simp [ExactImage]
  refine ⟨stopped, ?_, Or.inl rfl, rfl, rfl⟩
  exact .next (.next (.next (.next (.same state) (.seal active currentRoute))
    (.install sealed.book rfl certified)) (.publish installed.owner publishable)) (.stop state.owner stoppable)

def ForwardChain (reachable : Nat → Prop) (origin current : Nat) : Prop :=
  ∀ site, origin ≤ site → site ≤ current → reachable site

theorem pure_forwarding_needs_the_original_endpoint
    {reachable : Nat → Prop} {origin current : Nat}
    (moved : origin ≤ current) (offline : ¬ reachable origin) :
    ¬ ForwardChain reachable origin current := by
  intro path
  exact offline (path origin (Nat.le_refl _) moved)

def RecoveryObservation (result : Binding) (resolved : Bool) : Option Binding :=
  if resolved then some result else none

theorem indistinguishable_outage_worlds_cannot_both_recover_exactly
    {first second : Binding} (different : first ≠ second) :
    ¬ ∃ recover : Option Binding → Option Binding,
      recover (RecoveryObservation first false) = some first ∧
      recover (RecoveryObservation second false) = some second := by
  rintro ⟨recover, left, right⟩
  have noEvidence (result : Binding) : RecoveryObservation result false = none := by
    rfl
  rw [noEvidence] at left right
  exact different (Option.some.inj (left.symm.trans right))

def OvertakenRetries (resolve deliver : Nat → Nat) : Prop :=
  (∀ attempt, resolve attempt < deliver attempt) ∧
  (∀ attempt, deliver attempt = resolve (attempt + 1))

theorem arbitrarily_many_fresh_lookups_can_be_overtaken :
    ∃ resolve deliver, OvertakenRetries resolve deliver := by
  exact ⟨id, (· + 1), fun _ => Nat.lt_succ_self _, fun _ => rfl⟩

#print axioms initial_route_is_sound
#print axioms step_preserves_route_soundness
#print axioms trace_preserves_route_soundness
#print axioms locator_versions_do_not_go_back
#print axioms exact_install_leaves_original_keys_and_bindings
#print axioms step_preserves_exact_debt_or_settlement
#print axioms trace_preserves_exact_debt_or_settlement
#print axioms current_resolution_needs_no_retired_owner_records
#print axioms can_recover_exact_unsettled_debt_after_old_endpoints_stop
#print axioms can_move_and_stop_without_discharging
#print axioms pure_forwarding_needs_the_original_endpoint
#print axioms indistinguishable_outage_worlds_cannot_both_recover_exactly
#print axioms arbitrarily_many_fresh_lookups_can_be_overtaken

end ObligationHome
