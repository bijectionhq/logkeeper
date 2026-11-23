import CopyFence
import ProviderIOClosure

set_option warningAsError true

namespace PoolState

open ChannelLifecycle (Key Authority Store)
open RegistrationRecovery (Binding)

variable {Ticket : Type}

structure Identity where
  pool : Nat
  serial : Nat
  deriving DecidableEq

structure Row (Ticket : Type) where
  serial : Nat
  key : Key
  binding : Binding
  provider : ProviderIOClosure.State Ticket

def Row.identity (row : Row Ticket) : Identity :=
  ⟨row.key.handle.custodian, row.serial⟩

structure Rules (Ticket : Type) where
  authority : Authority
  limit : Nat
  cost : Binding → Nat
  positive : ∀ binding, 0 < cost binding
  reserve : ProviderIOClosure.Custody Ticket → Prop

structure Image (Ticket : Type) where
  gate : Store
  issued : Nat
  ordinary : Nat
  rows : List (Row Ticket)

def charges (rules : Rules Ticket) (rows : List (Row Ticket)) : Nat :=
  (rows.map (fun row => rules.cost row.binding)).sum

def used (rules : Rules Ticket) (state : Image Ticket) : Nat :=
  state.ordinary + charges rules state.rows

structure Sound (rules : Rules Ticket) (state : Image Ticket) : Prop where
  fits : used rules state ≤ rules.limit
  known : ∀ row ∈ state.rows, row.serial ≤ state.issued
  localPool : ∀ row ∈ state.rows, row.identity.pool = rules.authority.custodian
  paid : ∀ key binding, state.gate.grants key = some binding →
    ∃ row ∈ state.rows, row.key = key ∧ row.binding = binding
  provider : ∀ row ∈ state.rows, ProviderIOClosure.Sound row.provider
  unique : (state.rows.map Row.key).Nodup

def allocated (state : Image Ticket) (key : Key) (binding : Binding) : Row Ticket :=
  ⟨state.issued + 1, key, binding, ProviderIOClosure.initial⟩

def prepare (state : Image Ticket) (key : Key) (binding : Binding) : Image Ticket :=
  {state with
    gate := ChannelLifecycle.setGrant state.gate key (some binding)
    issued := state.issued + 1
    rows := allocated state key binding :: state.rows}

structure Admits (rules : Rules Ticket) (state : Image Ticket) (key : Key) (binding : Binding) : Prop where
  route : key.handle.custodian = rules.authority.custodian
  authentic : rules.authority.planned key binding
  gateRoom : rules.authority.mayPin state.gate
  eligible : ChannelLifecycle.decideAcquire state.gate key binding = .admit
  newKey : ∀ row ∈ state.rows, row.key ≠ key
  fits : used rules state + rules.cost binding ≤ rules.limit

variable [DecidableEq Ticket]

inductive Step (rules : Rules Ticket) : Image Ticket → Image Ticket → Prop
  | prepare {state} (key : Key) (binding : Binding) (allows : Admits rules state key binding) :
      Step rules state (PoolState.prepare state key binding)
  | ordinary {state} (next : Nat) (fits : next + charges rules state.rows ≤ rules.limit) :
      Step rules state {state with ordinary := next}
  | gate {state next} (change : ChannelLifecycle.Step rules.authority state.gate next)
      (sameGrants : next.grants = state.gate.grants) :
      Step rules state {state with gate := next}
  | fence {state} (key : Key) (binding : Binding)
      (choice : rules.authority.mayRelease key binding)
      (issued : key.handle.nonce ≤ state.gate.issued)
      (compatible : state.gate.grants key = none ∨ state.gate.grants key = some binding) :
      Step rules state {state with gate := ChannelLifecycle.releaseGrant state.gate key}
  | provider {state row next} (earlier later : List (Row Ticket)) (exact : state.rows = earlier ++ row :: later)
      (effect : ProviderIOClosure.Step rules.reserve row.provider next)
      (grant : ∀ ticket, row.provider.status ticket = .unused → next.status ticket = .pending →
        state.gate.grants row.key = some row.binding) :
      Step rules state {state with rows := earlier ++ {row with provider := next} :: later}
  | refund {state row} (earlier later : List (Row Ticket)) (exact : state.rows = earlier ++ row :: later)
      (closed : CopyFence.Closed state.gate row.key) (erased : row.provider.erased = true) :
      Step rules state {state with rows := earlier ++ later}

inductive Trace (rules : Rules Ticket) : Image Ticket → Image Ticket → Prop
  | same (state : Image Ticket) : Trace rules state state
  | next {first before after} : Trace rules first before → Step rules before after → Trace rules first after

theorem local_prepare_mints_its_version_on_arrival
    (rules : Rules Ticket) (state : Image Ticket) (key : Key) (binding : Binding)
    (can : Admits rules state key binding) :
    let after := prepare state key binding
    Step rules state after ∧ (allocated state key binding).identity = ⟨rules.authority.custodian, state.issued + 1⟩ ∧
      allocated state key binding ∈ after.rows ∧
      ChannelLifecycle.decideAcquire after.gate key binding = .replay := by
  have granted : (prepare state key binding).gate.grants key = some binding := by
    simp [prepare, ChannelLifecycle.setGrant]
  exact ⟨.prepare key binding can, by simp [allocated, Row.identity, can.route], List.mem_cons_self,
    (ChannelLifecycle.existing_grant_retries_without_channel_metadata granted (other := binding)).1⟩

omit [DecidableEq Ticket] in
theorem equal_local_serials_in_distinct_pools_are_distinct_physical_versions
    (left right serial : Nat) (different : left ≠ right) :
    (⟨left, serial⟩ : Identity) ≠ ⟨right, serial⟩ :=
  fun same => different (congrArg Identity.pool same)

omit [DecidableEq Ticket] in
private theorem replace_row_fields {before after : Row Ticket}
    (serial : before.serial = after.serial) (key : before.key = after.key)
    (binding : before.binding = after.binding) (earlier later : List (Row Ticket)) :
    ∀ row ∈ earlier ++ after :: later, ∃ prior ∈ earlier ++ before :: later,
      prior.serial = row.serial ∧ prior.key = row.key ∧ prior.binding = row.binding := by
  intro row member
  rcases List.mem_append.mp member with prior | suffix
  · exact ⟨row, List.mem_append_left _ prior, rfl, rfl, rfl⟩
  · rcases List.mem_cons.mp suffix with rfl | laterMember
    · exact ⟨before, List.mem_append_right _ List.mem_cons_self, serial, key, binding⟩
    · exact ⟨row, List.mem_append_right _ (List.mem_cons_of_mem _ laterMember), rfl, rfl, rfl⟩

theorem every_local_decision_preserves_capacity_and_exact_paid_grants
    {rules : Rules Ticket} {before after : Image Ticket}
    (safe : Sound rules before) (step : Step rules before after) : Sound rules after := by
  cases step with
  | prepare key binding can =>
      constructor
      · simpa [prepare, used, charges, allocated, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using can.fits
      · intro row member
        rcases List.mem_cons.mp member with rfl | prior
        · exact Nat.le_refl _
        · exact Nat.le_trans (safe.known row prior) (Nat.le_succ _)
      · intro row member
        rcases List.mem_cons.mp member with rfl | prior
        · exact can.route
        · exact safe.localPool row prior
      · intro query value found
        by_cases same : query = key
        · subst query
          have exactValue : binding = value := by
            exact Option.some.inj (by simpa [prepare, ChannelLifecycle.setGrant] using found)
          exact ⟨allocated before key binding, List.mem_cons_self, rfl, exactValue⟩
        · have prior : before.gate.grants query = some value := by
            simpa [prepare, ChannelLifecycle.setGrant, same] using found
          obtain ⟨row, member, matchesKey, bound⟩ := safe.paid query value prior
          exact ⟨row, List.mem_cons_of_mem _ member, matchesKey, bound⟩
      · intro row member
        rcases List.mem_cons.mp member with rfl | prior
        · exact ProviderIOClosure.initial_sound
        · exact safe.provider row prior
      · refine List.nodup_cons.mpr ⟨?_, safe.unique⟩
        intro present
        obtain ⟨row, member, equal⟩ := List.mem_map.mp present
        exact can.newKey row member equal
  | ordinary next fits => exact ⟨fits, safe.known, safe.localPool, safe.paid, safe.provider, safe.unique⟩
  | gate _ sameGrants =>
      exact ⟨safe.fits, safe.known, safe.localPool, fun key binding present =>
        safe.paid key binding (by simpa only [sameGrants] using present), safe.provider, safe.unique⟩
  | fence key _ _ _ _ =>
      refine ⟨safe.fits, safe.known, safe.localPool, ?_, safe.provider, safe.unique⟩
      intro query value found
      have releases := ChannelLifecycle.release_clears_only_the_exact_key before.gate key
      by_cases same : query = key
      · subst query
        rw [releases.1] at found
        cases found
      · exact safe.paid query value ((releases.2 query same).symm.trans found)
  | @provider row next earlier later exactRows effect _ =>
      let updated := {row with provider := next}
      have known : ∀ query ∈ earlier ++ updated :: later, ∃ prior ∈ before.rows,
          prior.serial = query.serial ∧ prior.key = query.key ∧ prior.binding = query.binding := by
        rw [exactRows]
        exact replace_row_fields (before := row) (after := updated) rfl rfl rfl earlier later
      constructor
      · simpa [used, charges, exactRows, updated] using safe.fits
      · intro query member
        obtain ⟨prior, inPrior, same, _, _⟩ := known query member
        exact same ▸ safe.known prior inPrior
      · intro query member
        obtain ⟨prior, inPrior, _, same, _⟩ := known query member
        simpa [Row.identity, ← same] using safe.localPool prior inPrior
      · intro query value held
        obtain ⟨prior, inPrior, same, bound⟩ := safe.paid query value held
        rw [exactRows] at inPrior
        rcases replace_row_fields (before := updated) (after := row) rfl rfl rfl earlier later prior inPrior with
          ⟨laterRow, inLater, _, sameLater, boundLater⟩
        exact ⟨laterRow, inLater, sameLater.trans same, boundLater.trans bound⟩
      · intro query member
        have covered : row ∈ before.rows := by rw [exactRows]; simp
        rcases List.mem_append.mp member with prior | suffix
        · exact safe.provider query (by rw [exactRows]; exact List.mem_append_left _ prior)
        · rcases List.mem_cons.mp suffix with rfl | rest
          · exact ProviderIOClosure.sound_step (safe.provider row covered) effect
          · exact safe.provider query (by rw [exactRows]; exact List.mem_append_right _ (List.mem_cons_of_mem _ rest))
      · simpa [exactRows] using safe.unique
  | @refund row earlier later exactRows closed _ =>
      have original : ∀ query ∈ earlier ++ later, query ∈ before.rows := by
        rw [exactRows]
        intro query member
        rcases List.mem_append.mp member with front | back
        · exact List.mem_append_left _ front
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ back)
      refine ⟨?_, fun query present => safe.known query (original query present),
        fun query present => safe.localPool query (original query present), ?_,
        (fun query present => safe.provider query (original query present)), ?_⟩
      · have fits := safe.fits
        simp [used, charges, exactRows] at fits ⊢
        omega
      · intro query value present
        obtain ⟨prior, member, keyMatches, bound⟩ := safe.paid query value present
        rw [exactRows] at member
        rcases List.mem_append.mp member with front | suffix
        · exact ⟨prior, List.mem_append_left _ front, keyMatches, bound⟩
        · rcases List.mem_cons.mp suffix with rfl | rest
          · rw [← keyMatches, closed.empty] at present
            cases present
          · exact ⟨prior, List.mem_append_right _ rest, keyMatches, bound⟩
      · have surviving := ((List.Sublist.refl later).cons row).append_left earlier
        exact (surviving.map Row.key).nodup (by simpa only [exactRows] using safe.unique)

omit [DecidableEq Ticket] in
theorem a_live_preparation_retry_resolves_to_its_one_exact_physical_row
    {rules : Rules Ticket} {state : Image Ticket} {key : Key} {binding : Binding}
    (safe : Sound rules state) (held : state.gate.grants key = some binding) :
    ∃ row ∈ state.rows, row.key = key ∧ row.binding = binding ∧
      ChannelLifecycle.decideAcquire state.gate key binding = .replay ∧
      ∀ other ∈ state.rows, other.key = key → other = row := by
  have unique (rows : List (Row Ticket)) (nodup : (rows.map Row.key).Nodup) :
      ∀ left right, left ∈ rows → right ∈ rows → left.key = right.key → left = right := by
    induction rows with
    | nil => simp
    | cons first rest prior =>
        have separated := List.nodup_cons.mp nodup
        intro left right leftRow rightRow exactKey
        rcases List.mem_cons.mp leftRow with rfl | leftTail
        · rcases List.mem_cons.mp rightRow with rfl | rightTail
          · rfl
          · exact False.elim (separated.1 (List.mem_map.mpr ⟨right, rightTail, exactKey.symm⟩))
        · rcases List.mem_cons.mp rightRow with rfl | rightTail
          · exact False.elim (separated.1 (List.mem_map.mpr ⟨left, leftTail, exactKey⟩))
          · exact prior separated.2 left right leftTail rightTail exactKey
  obtain ⟨row, member, exactKey, exactBinding⟩ := safe.paid key binding held
  exact ⟨row, member, exactKey, exactBinding,
    (ChannelLifecycle.existing_grant_retries_without_channel_metadata held (other := binding)).1,
    fun other present same => unique state.rows safe.unique other row present member (same.trans exactKey.symm)⟩

theorem all_local_histories_keep_the_exact_allocator_and_capacity
    {rules : Rules Ticket} {first last : Image Ticket}
    (safe : Sound rules first) (trace : Trace rules first last) :
    Sound rules last ∧ first.issued ≤ last.issued := by
  induction trace with
  | same => exact ⟨safe, Nat.le_refl _⟩
  | next _ event prior =>
      refine ⟨every_local_decision_preserves_capacity_and_exact_paid_grants prior.1 event,
        Nat.le_trans prior.2 ?_⟩
      cases event <;> simp [prepare]

theorem every_decision_preserves_an_old_admission_fence
    {rules : Rules Ticket} {before after : Image Ticket} {key : Key}
    (closed : CopyFence.Closed before.gate key) (event : Step rules before after) :
    CopyFence.Closed after.gate key := by
  cases event with
  | prepare candidate binding can =>
      exact CopyFence.a_copy_fence_survives_every_custodian_step closed
        (.acquire candidate binding can.authentic can.gateRoom can.eligible)
  | gate effect _ => exact CopyFence.a_copy_fence_survives_every_custodian_step closed effect
  | fence candidate binding choice _ compatible =>
      exact CopyFence.a_copy_fence_survives_every_custodian_step closed (.release candidate binding compatible choice)
  | _ => exact closed

theorem after_any_local_history_a_closed_scope_stays_refused
    {rules : Rules Ticket} {first last : Image Ticket} {key : Key}
    (closed : CopyFence.Closed first.gate key) (trace : Trace rules first last) :
    CopyFence.Closed last.gate key := by
  induction trace with
  | same => exact closed
  | next _ event prior => exact every_decision_preserves_an_old_admission_fence prior event

omit [DecidableEq Ticket] in
theorem positive_charges_bound_all_live_physical_rows
    {rules : Rules Ticket} {state : Image Ticket} (safe : Sound rules state) : state.rows.length ≤ rules.limit := by
  have lower (rows : List (Row Ticket)) : rows.length ≤ charges rules rows := by
    induction rows with
    | nil => simp [charges]
    | cons row others ih =>
        have positive := rules.positive row.binding
        simp [charges] at ih ⊢
        omega
  exact Nat.le_trans (lower state.rows) (Nat.le_trans (Nat.le_add_left ..) safe.fits)

omit [DecidableEq Ticket] in
theorem a_physical_refund_requires_its_own_provider_absence
    {rules : Rules Ticket} {state : Image Ticket} {row : Row Ticket}
    (safe : Sound rules state) (member : row ∈ state.rows) (erased : row.provider.erased = true) :
    ProviderIOClosure.StableAbsence row.provider :=
  (safe.provider row member).erasure erased

def Holds (state : Image Ticket) (identity : Identity) (key : Key) (binding : Binding) : Prop :=
  ∃ row ∈ state.rows, row.identity = identity ∧ row.key = key ∧ row.binding = binding

def Disposed (state : Image Ticket) (identity : Identity) (key : Key) (binding : Binding) : Prop :=
  ∃ row ∈ state.rows, row.identity = identity ∧ row.key = key ∧ row.binding = binding ∧
    ProviderIOClosure.StableAbsence row.provider

theorem a_paid_extent_stays_charged_until_its_own_stable_absence
    {rules : Rules Ticket} {first last : Image Ticket} {identity : Identity} {key : Key} {binding : Binding}
    (safe : Sound rules first) (trace : Trace rules first last) (paid : Holds first identity key binding) :
    Holds last identity key binding ∨ ∃ before, Trace rules first before ∧ Disposed before identity key binding := by
  induction trace with
  | same => exact .inl paid
  | @next before after earlier event prior =>
      rcases prior with live | disposed
      · obtain ⟨row, member, hasId, hasKey, hasBinding⟩ := live
        cases event with
        | prepare candidate value _ =>
            exact .inl ⟨row, List.mem_cons_of_mem _ member, hasId, hasKey, hasBinding⟩
        | ordinary _ _ | gate _ _ | fence _ _ _ _ _ =>
            exact .inl ⟨row, member, hasId, hasKey, hasBinding⟩
        | @provider changed next front back exactRows _ _ =>
            let updated := {changed with provider := next}
            rw [exactRows] at member
            obtain ⟨kept, afterMember, serial, keyMatches, bindingMatches⟩ :=
              replace_row_fields (before := updated) (after := changed) rfl rfl rfl front back row member
            exact .inl ⟨kept, afterMember, (by simp [Row.identity, serial, keyMatches, ← hasId]),
              keyMatches.trans hasKey, bindingMatches.trans hasBinding⟩
        | @refund removed front back exactRows _ erased =>
            have priorMember := member
            rw [exactRows] at member
            rcases List.mem_append.mp member with inFront | suffix
            · exact .inl ⟨row, List.mem_append_left _ inFront, hasId, hasKey, hasBinding⟩
            · rcases List.mem_cons.mp suffix with rfl | inBack
              · exact .inr ⟨before, earlier, row, priorMember, hasId, hasKey, hasBinding,
                  a_physical_refund_requires_its_own_provider_absence
                    (all_local_histories_keep_the_exact_allocator_and_capacity safe earlier).1 priorMember erased⟩
              · exact .inl ⟨row, List.mem_append_right _ inBack, hasId, hasKey, hasBinding⟩
      · exact .inr disposed

def Region (Ticket : Type) := Nat → Image Ticket

def replacePool (state : Region Ticket) (pool : Nat) (replacement : Image Ticket) : Region Ticket :=
  fun query => if query = pool then replacement else state query

def prepareAt (state : Region Ticket) (pool : Nat) (key : Key) (binding : Binding) : Region Ticket :=
  replacePool state pool (prepare (state pool) key binding)

omit [DecidableEq Ticket] in
theorem an_unrelated_pool_decision_has_no_effect_on_local_prepare
    (all : Nat → Rules Ticket) (before : Region Ticket) (changed localPool : Nat)
    (replacement : Image Ticket) (key : Key) (binding : Binding)
    (different : localPool ≠ changed)
    (admit : Admits (all localPool) (before localPool) key binding) :
    let after := replacePool before changed replacement
    Admits (all localPool) (after localPool) key binding ∧
      (allocated (after localPool) key binding).identity = (allocated (before localPool) key binding).identity := by
  simp [replacePool, different, admit]

omit [DecidableEq Ticket] in
theorem preparations_at_distinct_pools_commute_without_reminting
    (state : Region Ticket) (left right : Nat) (leftKey rightKey : Key) (leftBinding rightBinding : Binding)
    (different : left ≠ right) :
    prepareAt (prepareAt state left leftKey leftBinding) right rightKey rightBinding =
      prepareAt (prepareAt state right rightKey rightBinding) left leftKey leftBinding := by
  funext query
  by_cases isLeft : query = left
  · subst query
    simp [prepareAt, replacePool, different]
  · by_cases isRight : query = right
    · subst query
      simp [prepareAt, replacePool, Ne.symm different]
    · simp [prepareAt, replacePool, isLeft, isRight]

#print axioms local_prepare_mints_its_version_on_arrival
#print axioms equal_local_serials_in_distinct_pools_are_distinct_physical_versions
#print axioms every_local_decision_preserves_capacity_and_exact_paid_grants
#print axioms a_live_preparation_retry_resolves_to_its_one_exact_physical_row
#print axioms all_local_histories_keep_the_exact_allocator_and_capacity
#print axioms every_decision_preserves_an_old_admission_fence
#print axioms after_any_local_history_a_closed_scope_stays_refused
#print axioms positive_charges_bound_all_live_physical_rows
#print axioms a_physical_refund_requires_its_own_provider_absence
#print axioms a_paid_extent_stays_charged_until_its_own_stable_absence
#print axioms an_unrelated_pool_decision_has_no_effect_on_local_prepare
#print axioms preparations_at_distinct_pools_commute_without_reminting

end PoolState
