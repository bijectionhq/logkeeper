set_option warningAsError true

namespace ProviderIOClosure

variable {Ticket : Type}

inductive Status where
  | unused
  | pending
  | done
  deriving DecidableEq

structure Custody (Ticket : Type) where
  footprintReserved : Bool
  tracks : Ticket → Prop

structure State (Ticket : Type) where
  admitOpen : Bool
  providerClosed : Bool
  status : Ticket → Status
  observedFence : Bool
  observedDone : Ticket → Prop
  present : Bool
  erased : Bool
  target : Bool
  custodian : Option (Custody Ticket)

def initial : State Ticket :=
  ⟨true, false, fun _ => .unused, false, fun _ => False, false, false, true, none⟩

def writeStatus [DecidableEq Ticket] (status : Ticket → Status) (ticket : Ticket) (next : Status) :
    Ticket → Status :=
  fun queried => if queried = ticket then next else status queried

def MayWrite (state : State Ticket) (ticket : Ticket) : Prop :=
  state.providerClosed = false ∧ state.status ticket = .pending

def ClosureKnown (state : State Ticket) : Prop :=
  state.admitOpen = false ∧
    (state.observedFence = true ∨ ∀ ticket, state.status ticket ≠ .unused → state.observedDone ticket)

def StableAbsence (state : State Ticket) : Prop :=
  state.admitOpen = false ∧ state.present = false ∧ ∀ ticket, ¬ MayWrite state ticket

def Covers (state : State Ticket) (custody : Custody Ticket) : Prop :=
  state.admitOpen = false ∧ custody.footprintReserved = true ∧
    ∀ ticket, state.status ticket ≠ .unused → custody.tracks ticket

def HasCustody (state : State Ticket) : Prop := ∃ custody, state.custodian = some custody

def CanReleaseTarget (state : State Ticket) : Prop :=
  state.erased = true ∨ HasCustody state

structure Knowledge (state : State Ticket) : Prop where
  fence : state.observedFence = true → state.providerClosed = true
  done : ∀ ticket, state.observedDone ticket → state.status ticket = .done

structure Sound (state : State Ticket) : Prop where
  knowledge : Knowledge state
  erasure : state.erased = true → StableAbsence state
  custody : ∀ record, state.custodian = some record → Covers state record
  charged : state.target = true ∨ CanReleaseTarget state

inductive Step [DecidableEq Ticket] (reserve : Custody Ticket → Prop) : State Ticket → State Ticket → Prop
  | issue {state} (ticket : Ticket) (opened : state.admitOpen = true) (funded : state.target = true)
      (fresh : state.status ticket = .unused) :
      Step reserve state {state with status := writeStatus state.status ticket .pending}
  | effect {state} (ticket : Ticket) (eligible : MayWrite state ticket) :
      Step reserve state {state with status := writeStatus state.status ticket .done, present := true}
  | closeEntrance {state} :
      Step reserve state {state with admitOpen := false}
  | closeAtProvider {state} (closed : state.admitOpen = false) :
      Step reserve state {state with providerClosed := true}
  | observeFence {state} (committed : state.providerClosed = true) :
      Step reserve state {state with observedFence := true}
  | observeDone {state} (ticket : Ticket) (committed : state.status ticket = .done) :
      Step reserve state {state with observedDone := fun id => id = ticket ∨ state.observedDone id}
  | delete {state} (drained : ClosureKnown state) :
      Step reserve state {state with present := false}
  | confirmAbsence {state} (drained : ClosureKnown state) (absent : state.present = false) :
      Step reserve state {state with erased := true}
  | takeCustody {state} (record : Custody Ticket) (covers : Covers state record) (room : reserve record) :
      Step reserve state {state with custodian := some record}
  | releaseTarget {state} (disposition : CanReleaseTarget state) :
      Step reserve state {state with target := false}
  | releaseCustodian {state} (erased : state.erased = true) :
      Step reserve state {state with custodian := none}
  | restart {state} :
      Step reserve state state

inductive Trace [DecidableEq Ticket] (reserve : Custody Ticket → Prop) : State Ticket → State Ticket → Prop
  | same (state : State Ticket) : Trace reserve state state
  | next {first before after} : Trace reserve first before → Step reserve before after →
      Trace reserve first after

theorem admitted_ticket_needs_a_provider_check
    {state : State Ticket} {ticket : Ticket} (closed : state.providerClosed = true) :
    ¬ MayWrite state ticket := by
  intro permission
  have inconsistent : state.providerClosed = false := by
    exact permission.1
  rw [closed] at inconsistent
  cases inconsistent

theorem completed_ticket_cannot_apply_again
    {state : State Ticket} {ticket : Ticket} (done : state.status ticket = .done) :
    ¬ MayWrite state ticket := by
  intro permission
  have pending : state.status ticket = .pending := by
    exact permission.2
  rw [done] at pending
  cases pending

theorem observed_closure_excludes_every_write
    {state : State Ticket} (knowledge : Knowledge state) (drained : ClosureKnown state) :
    ∀ ticket, ¬ MayWrite state ticket := by
  intro ticket permission
  rcases drained.2 with scope | perTicket
  · exact admitted_ticket_needs_a_provider_check (knowledge.fence scope) permission
  · have issued : state.status ticket ≠ .unused := by
      rw [permission.2]
      decide
    exact completed_ticket_cannot_apply_again (knowledge.done ticket (perTicket ticket issued)) permission

theorem initial_sound : Sound (initial : State Ticket) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, .inl rfl⟩
  · intro impossible
    cases impossible
  · intro ticket impossible
    cases impossible
  · intro impossible
    cases impossible
  · intro custody impossible
    cases impossible

theorem custody_tracks_every_possible_write
    {state : State Ticket} {record : Custody Ticket} {ticket : Ticket}
    (covers : Covers state record) (pending : MayWrite state ticket) :
    record.tracks ticket := by
  have issued : state.status ticket ≠ .unused := by
    rw [pending.2]
    decide
  exact covers.2.2 ticket issued

variable [DecidableEq Ticket]

theorem a_consumed_ticket_stays_consumed
    {reserve : Custody Ticket → Prop} {first last : State Ticket} {ticket : Ticket}
    (done : first.status ticket = .done) (trace : Trace reserve first last) :
    last.status ticket = .done := by
  induction trace with
  | same => exact done
  | next _ step prior =>
      cases step with
      | issue added _ _ unused =>
          by_cases same : ticket = added
          · subst added
            rw [unused] at prior
            cases prior
          · simpa [writeStatus, same] using prior
      | effect landed _ =>
          by_cases same : ticket = landed
          · simp [writeStatus, same]
          · simpa [writeStatus, same] using prior
      | _ => exact prior

private theorem knowledge_persists
    {reserve : Custody Ticket → Prop} {before after : State Ticket}
    (known : Knowledge before) (step : Step reserve before after) : Knowledge after := by
  cases step with
  | issue added _ _ unused =>
      refine ⟨known.fence, ?_⟩
      intro ticket evidence
      by_cases same : ticket = added
      · subst ticket
        have prior := known.done added evidence
        rw [unused] at prior
        cases prior
      · simpa [writeStatus, same] using known.done ticket evidence
  | effect landed _ =>
      refine ⟨known.fence, ?_⟩
      intro ticket evidence
      by_cases same : ticket = landed
      · simp [writeStatus, same]
      · simpa [writeStatus, same] using known.done ticket evidence
  | closeAtProvider _ => exact ⟨fun _ => rfl, known.done⟩
  | observeFence committed => exact ⟨fun _ => committed, known.done⟩
  | observeDone completed committed =>
      refine ⟨known.fence, ?_⟩
      intro ticket evidence
      rcases evidence with same | prior
      · exact same ▸ committed
      · exact known.done ticket prior
  | _ => exact ⟨known.fence, known.done⟩

private theorem stable_absence_step
    {reserve : Custody Ticket → Prop} {before after : State Ticket}
    (stable : StableAbsence before) (step : Step reserve before after) : StableAbsence after := by
  cases step with
  | issue _ opened _ _ =>
      have closed := stable.1
      rw [opened] at closed
      cases closed
  | effect ticket eligible => exact False.elim (stable.2.2 ticket eligible)
  | closeEntrance => exact ⟨rfl, stable.2⟩
  | closeAtProvider _ =>
      exact ⟨stable.1, stable.2.1, fun _ => admitted_ticket_needs_a_provider_check rfl⟩
  | delete _ => exact ⟨stable.1, rfl, stable.2.2⟩
  | _ => exact stable

private theorem erasure_persists
    {reserve : Custody Ticket → Prop} {before after : State Ticket}
    (already : before.erased = true) (step : Step reserve before after) : after.erased = true := by
  cases step with
  | confirmAbsence _ _ => rfl
  | _ => exact already

private theorem custody_coverage_persists
    {reserve : Custody Ticket → Prop} {before after : State Ticket}
    (covers : ∀ record, before.custodian = some record → Covers before record)
    (step : Step reserve before after) :
    ∀ record, after.custodian = some record → Covers after record := by
  cases step with
  | issue _ opened _ _ =>
      intro record found
      have closed := (covers record found).1
      rw [opened] at closed
      cases closed
  | effect written eligible =>
      intro record found
      obtain ⟨closed, bytes, tickets⟩ := covers record found
      refine ⟨closed, bytes, ?_⟩
      intro ticket issued
      by_cases same : ticket = written
      · subst ticket
        exact tickets written (by simp [eligible.2])
      · exact tickets ticket (by simpa [writeStatus, same] using issued)
  | closeEntrance =>
      intro record found
      exact ⟨rfl, (covers record found).2⟩
  | takeCustody record covered _ =>
      intro observed found
      have same := Option.some.inj found
      subst observed
      exact covered
  | releaseCustodian _ =>
      intro record impossible
      cases impossible
  | _ => exact covers

private theorem charge_or_erasure_persists
    {reserve : Custody Ticket → Prop} {before after : State Ticket}
    (proved : CanReleaseTarget before) (step : Step reserve before after) : CanReleaseTarget after := by
  cases step with
  | confirmAbsence _ _ => exact .inl rfl
  | takeCustody record _ _ => exact .inr ⟨record, rfl⟩
  | releaseCustodian erased => exact .inl erased
  | _ => exact proved

theorem sound_step {reserve : Custody Ticket → Prop} {before after : State Ticket}
    (sound : Sound before) (step : Step reserve before after) : Sound after := by
  have forwardAbsence := fun stable => stable_absence_step stable step
  have forwardCharge := fun charged => charge_or_erasure_persists charged step
  refine ⟨knowledge_persists sound.knowledge step, ?_, custody_coverage_persists sound.custody step, ?_⟩
  · intro erased
    cases step with
    | confirmAbsence drained absent =>
        exact ⟨drained.1, absent, observed_closure_excludes_every_write (state := before) sound.knowledge drained⟩
    | _ => exact forwardAbsence (sound.erasure erased)
  · cases step with
    | releaseTarget disposition => exact .inr disposition
    | _ =>
        rcases sound.charged with target | other
        · exact .inl target
        · exact .inr (forwardCharge other)

theorem sound_trace {reserve : Custody Ticket → Prop} {first last : State Ticket}
    (sound : Sound first) (trace : Trace reserve first last) : Sound last := by
  induction trace with
  | same => exact sound
  | next _ step prior => exact sound_step prior step

theorem no_write_can_recreate_a_certified_erasure
    {reserve : Custody Ticket → Prop} {first last : State Ticket}
    (sound : Sound first) (receipt : first.erased = true) (trace : Trace reserve first last) :
    last.erased = true ∧ StableAbsence last := by
  have stays : last.erased = true := by
    induction trace with
    | same => exact receipt
    | next _ step prior => exact erasure_persists prior step
  exact ⟨stays, (sound_trace sound trace).erasure stays⟩

omit [DecidableEq Ticket] in
theorem release_needs_stable_absence_or_reserved_custody
    {state : State Ticket} (sound : Sound state) (released : state.target = false) :
    StableAbsence state ∨ ∃ custody, state.custodian = some custody ∧ Covers state custody := by
  have other := sound.charged.resolve_left (fun charged => Bool.noConfusion (released.symm.trans charged))
  rcases other with erased | ⟨custody, installed⟩
  · exact .inl (sound.erasure erased)
  · exact .inr ⟨custody, installed, sound.custody custody installed⟩

theorem a_prior_custody_receipt_stays_valid_through_erasure
    {reserve : Custody Ticket → Prop} {first last : State Ticket}
    (receipt : HasCustody first) (trace : Trace reserve first last) :
    CanReleaseTarget last := by
  induction trace with
  | same => exact .inr receipt
  | next _ step prior => exact charge_or_erasure_persists prior step

theorem target_release_can_keep_a_write_pending
    (state : State Ticket) (record : Custody Ticket) (reserve : Custody Ticket → Prop) (ticket : Ticket)
    (pending : MayWrite state ticket) (covers : Covers state record) (room : reserve record) :
    ∃ after, Trace reserve state after ∧ after.target = false ∧ after.custodian = some record ∧
      MayWrite after ticket := by
  let held := {state with custodian := some record}
  let released := {held with target := false}
  have allowed : CanReleaseTarget held := .inr ⟨record, rfl⟩
  exact ⟨released, .next (.next (.same state) (.takeCustody record covers room)) (.releaseTarget allowed),
    rfl, rfl, pending⟩

structure Observations (Ticket : Type) where
  admitOpen : Bool
  issued : Ticket → Prop
  observedFence : Bool
  observedDone : Ticket → Prop
  present : Bool

def observe (state : State Ticket) : Observations Ticket :=
  ⟨state.admitOpen, (fun ticket => state.status ticket ≠ .unused),
    state.observedFence, state.observedDone, state.present⟩

theorem equal_observations_can_hide_a_write_that_may_still_land
    (reserve : Custody Ticket → Prop) (state : State Ticket) (ticket : Ticket)
    (closed : state.admitOpen = false) (absent : state.present = false) (pending : MayWrite state ticket) :
    ∃ next, Step reserve state next ∧ observe next = observe state ∧ StableAbsence next ∧ ¬ StableAbsence state := by
  let fenced := {state with providerClosed := true}
  exact ⟨fenced, .closeAtProvider closed, rfl,
    ⟨closed, absent, fun _ => admitted_ticket_needs_a_provider_check rfl⟩,
    fun stable => stable.2.2 ticket pending⟩

#print axioms admitted_ticket_needs_a_provider_check
#print axioms completed_ticket_cannot_apply_again
#print axioms observed_closure_excludes_every_write
#print axioms initial_sound
#print axioms custody_tracks_every_possible_write
#print axioms a_consumed_ticket_stays_consumed
#print axioms sound_step
#print axioms sound_trace
#print axioms no_write_can_recreate_a_certified_erasure
#print axioms release_needs_stable_absence_or_reserved_custody
#print axioms a_prior_custody_receipt_stays_valid_through_erasure
#print axioms target_release_can_keep_a_write_pending
#print axioms equal_observations_can_hide_a_write_that_may_still_land

end ProviderIOClosure
