import ProviderIOClosure
import Reservation

set_option warningAsError true

namespace TicketBook

open ProviderIOClosure (Status)

variable {Image : Type}

structure Ticket (Image : Type) where
  serial : Nat
  image : Image

structure Book (Image : Type) where
  issued : Nat
  live : List (Ticket Image)

def Serials (book : Book Image) : List Nat := book.live.map Ticket.serial

def status (book : Book Image) (serial : Nat) : Status :=
  if 0 < serial ∧ serial ≤ book.issued then
    if serial ∈ Serials book then .pending else .done
  else .unused

structure State (Image : Type) where
  book : Book Image
  admitOpen : Bool
  providerClosed : Bool
  present : Bool
  erased : Bool

def initial : State Image := ⟨⟨0, []⟩, true, false, false, false⟩

def issue (book : Book Image) (image : Image) : Book Image :=
  ⟨book.issued + 1, ⟨book.issued + 1, image⟩ :: book.live⟩

def consume (book : Book Image) (serial : Nat) : Book Image :=
  {book with live := book.live.filter (fun ticket => decide (ticket.serial ≠ serial))}

def ExactLive (state : State Image) (ticket : Ticket Image) : Prop :=
  ticket ∈ state.book.live

def MayWrite (state : State Image) (ticket : Ticket Image) : Prop :=
  state.providerClosed = false ∧ ExactLive state ticket

def ClosedSerial (book : Book Image) (serial : Nat) : Prop :=
  0 < serial ∧ serial ≤ book.issued ∧ serial ∉ Serials book

def CanErase (state : State Image) : Prop :=
  state.admitOpen = false ∧ (state.providerClosed = true ∨ state.book.live = [])

structure BookSound (width : Nat) (book : Book Image) : Prop where
  numbered : ∀ serial ∈ Serials book, 0 < serial ∧ serial ≤ book.issued
  unique : (Serials book).Nodup
  withinWidth : book.live.length ≤ width

inductive Step (width : Nat) : State Image → State Image → Prop
  | issue {state} (image : Image) (opened : state.admitOpen = true)
      (room : state.book.live.length < width) :
      Step width state {state with book := issue state.book image}
  | effect {state} (ticket : Ticket Image) (allowed : MayWrite state ticket) :
      Step width state {state with book := consume state.book ticket.serial, present := true}
  | sealEntrance {state} : Step width state {state with admitOpen := false}
  | sealProvider {state} (closed : state.admitOpen = false) :
      Step width state {state with providerClosed := true}
  | erase {state} (drained : CanErase state) :
      Step width state {state with present := false, erased := true}
  | restart {state} : Step width state state

inductive Trace (width : Nat) : State Image → State Image → Prop
  | same (state) : Trace width state state
  | next {first before after} : Trace width first before → Step width before after → Trace width first after

theorem issued_within_the_current_gate {state : State Image} {ticket : Ticket Image}
    (live : ExactLive state ticket) : ticket ∈ state.book.live := by
  exact live

private theorem serial_mem_consume {book : Book Image} {serial removed : Nat} :
    serial ∈ Serials (consume book removed) ↔ serial ∈ Serials book ∧ serial ≠ removed := by
  simp only [consume, Serials, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨ticket, ⟨live, notRemoved⟩, rfl⟩
    exact ⟨⟨ticket, live, rfl⟩, notRemoved⟩
  · rintro ⟨⟨ticket, live, rfl⟩, notRemoved⟩
    exact ⟨ticket, ⟨live, notRemoved⟩, rfl⟩

private theorem live_serial {book : Book Image} {ticket : Ticket Image} (live : ticket ∈ book.live) :
    ticket.serial ∈ Serials book :=
  List.mem_map.mpr ⟨ticket, live, rfl⟩

private theorem unique_serials_identify_exact_tickets (tickets : List (Ticket Image))
    (unique : (tickets.map Ticket.serial).Nodup) {first second : Ticket Image}
    (left : first ∈ tickets) (right : second ∈ tickets) (serial : first.serial = second.serial) :
    first = second := by
  induction tickets with
  | nil => cases left
  | cons live rest prior =>
      obtain ⟨fresh, remaining⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp left with atHead | inTail
      · subst first
        rcases List.mem_cons.mp right with same | other
        · exact same.symm
        · exact False.elim (fresh (List.mem_map.mpr ⟨second, other, serial.symm⟩))
      · rcases List.mem_cons.mp right with atHead | inTailRight
        · subst second
          exact False.elim (fresh (List.mem_map.mpr ⟨first, inTail, serial⟩))
        · exact prior remaining inTail inTailRight

theorem numbered_slot_has_exactly_one_binding {book : Book Image} {width : Nat}
    (sound : BookSound width book) {first second : Ticket Image}
    (left : first ∈ book.live) (right : second ∈ book.live) (serial : first.serial = second.serial) :
    first = second :=
  unique_serials_identify_exact_tickets book.live sound.unique left right serial

theorem completing_the_effect_certifies_closed_exact_ticket {state : State Image}
    {ticket : Ticket Image} {width : Nat} (sound : BookSound width state.book) (eligible : MayWrite state ticket) :
    ClosedSerial (consume state.book ticket.serial) ticket.serial := by
  obtain ⟨positive, issued⟩ := sound.numbered _ (live_serial (issued_within_the_current_gate eligible.2))
  exact ⟨positive, issued, fun found => (serial_mem_consume.mp found).2 rfl⟩

theorem initial_book_is_bounded (width : Nat) : BookSound width (initial : State Image).book := by
  refine ⟨?_, List.nodup_nil, Nat.zero_le _⟩
  intro serial membership
  cases membership

theorem each_step_preserves_durable_issuance_and_live_bound {before after : State Image} {width : Nat}
    (sound : BookSound width before.book) (step : Step width before after) : BookSound width after.book := by
  cases step with
  | issue image _ room =>
      refine ⟨?_, ?_, Nat.succ_le_of_lt room⟩
      · intro serial membership
        rcases List.mem_cons.mp membership with rfl | older
        · exact ⟨Nat.zero_lt_succ _, Nat.le_refl _⟩
        · obtain ⟨positive, issued⟩ := sound.numbered serial older
          exact ⟨positive, Nat.le_trans issued (Nat.le_succ _)⟩
      · apply List.nodup_cons.mpr
        exact ⟨fun old => Nat.not_succ_le_self _ (sound.numbered _ old).2, sound.unique⟩
  | effect ticket _ =>
      refine ⟨fun serial live => sound.numbered serial (serial_mem_consume.mp live).1, ?_, ?_⟩
      · have subset := (List.filter_sublist (l := before.book.live)
          (p := fun item => decide (item.serial ≠ ticket.serial))).map Ticket.serial
        exact subset.nodup sound.unique
      · exact Nat.le_trans (List.length_filter_le _ _) sound.withinWidth
  | _ => exact sound

theorem arbitrary_histories_need_only_the_live_ticket_window
    {first last : State Image} {width : Nat} (sound : BookSound width first.book)
    (trace : Trace width first last) : BookSound width last.book := by
  induction trace with
  | same => exact sound
  | next _ step prior => exact each_step_preserves_durable_issuance_and_live_bound prior step

theorem issued_absence_is_a_terminal_provider_status {book : Book Image} {serial : Nat}
    (closed : ClosedSerial book serial) : status book serial = .done := by
  have issued : 0 < serial ∧ serial ≤ book.issued := by
    exact ⟨closed.1, closed.2.1⟩
  simp [status, issued, closed.2.2]

theorem a_compacted_book_cannot_identify_the_old_payload {first second : Image} (different : first ≠ second) :
    ¬ ∃ recover : Book Image → Image,
      recover (consume (issue ⟨0, []⟩ first) 1) = first ∧
      recover (consume (issue ⟨0, []⟩ second) 1) = second := by
  rintro ⟨recover, left, right⟩
  have same : consume (issue ⟨0, []⟩ first) 1 = consume (issue ⟨0, []⟩ second) 1 := by
    simp [consume, issue]
  rw [same] at left
  exact different (left.symm.trans right)

theorem closed_serial_survives_every_compact_book_step {before after : State Image} {width serial : Nat}
    (closed : ClosedSerial before.book serial) (step : Step width before after) : ClosedSerial after.book serial := by
  cases step with
  | issue _ _ _ =>
      have different : serial ≠ before.book.issued + 1 := by
        have issued := closed.2.1
        omega
      exact ⟨closed.1, Nat.le_trans closed.2.1 (Nat.le_succ _), by
        simpa [Serials, issue, different] using closed.2.2⟩
  | effect _ _ => exact ⟨closed.1, closed.2.1, fun live => closed.2.2 (serial_mem_consume.mp live).1⟩
  | _ => exact closed

theorem a_certified_ticket_cannot_be_reopened
    {first last : State Image} {serial width : Nat}
    (closed : ClosedSerial first.book serial) (trace : Trace width first last) :
    ClosedSerial last.book serial ∧ ∀ ticket, ticket.serial = serial → ¬ MayWrite last ticket := by
  have current : ClosedSerial last.book serial := by
    induction trace with
    | same => exact closed
    | next _ step prior => exact closed_serial_survives_every_compact_book_step prior step
  refine ⟨current, ?_⟩
  intro ticket same permit
  exact current.2.2 (same ▸ live_serial (issued_within_the_current_gate permit.2))

private theorem issuing_refines_status (book : Book Image) (image : Image) :
    status (issue book image) = ProviderIOClosure.writeStatus (status book) (book.issued + 1) .pending := by
  funext serial
  by_cases promoted : serial = book.issued + 1
  · subst serial
    simp [status, issue, Serials, ProviderIOClosure.writeStatus]
  · have range : (0 < serial ∧ serial ≤ book.issued + 1) ↔ (0 < serial ∧ serial ≤ book.issued) := by omega
    simp [status, issue, Serials, ProviderIOClosure.writeStatus, promoted, range]

private theorem consuming_refines_status (book : Book Image) {serial : Nat}
    (issued : 0 < serial ∧ serial ≤ book.issued) :
    status (consume book serial) = ProviderIOClosure.writeStatus (status book) serial .done := by
  funext queried
  by_cases same : queried = serial
  · subst queried
    have absent : serial ∉ Serials (consume book serial) := by
      intro found
      exact (serial_mem_consume.mp found).2 rfl
    have stillIssued : 0 < serial ∧ serial ≤ (consume book serial).issued := issued
    simp [status, stillIssued, ProviderIOClosure.writeStatus, absent]
  · have remains : queried ∈ Serials (consume book serial) ↔ queried ∈ Serials book :=
      ⟨fun yes => (serial_mem_consume.mp yes).1, fun yes => serial_mem_consume.mpr ⟨yes, same⟩⟩
    show (if 0 < queried ∧ queried ≤ book.issued then
      if queried ∈ Serials (consume book serial) then Status.pending else Status.done else Status.unused) = _
    simp [ProviderIOClosure.writeStatus, same, remains, status]

def toProvider (state : State Image) : ProviderIOClosure.State Nat :=
  ⟨state.admitOpen, state.providerClosed, status state.book, false, (fun _ => False),
    state.present, state.erased, true, none⟩

theorem issuance_refines_the_provider_model {state : State Image} (image : Image)
    (opened : state.admitOpen = true) (reserve : ProviderIOClosure.Custody Nat → Prop) :
    ProviderIOClosure.Step reserve (toProvider state) (toProvider {state with book := issue state.book image}) := by
  have beyond : ¬ state.book.issued + 1 ≤ state.book.issued := by omega
  have issued : status state.book (state.book.issued + 1) = .unused := by simp [status, beyond]
  have step := ProviderIOClosure.Step.issue (state := toProvider state) (reserve := reserve)
    (state.book.issued + 1) opened rfl issued
  change ProviderIOClosure.Step reserve (toProvider state)
    ⟨state.admitOpen, state.providerClosed, status (issue state.book image), false,
      (fun _ => False), state.present, state.erased, true, none⟩
  rw [issuing_refines_status]
  exact step

theorem consumption_refines_a_single_provider_effect {state : State Image} {ticket : Ticket Image} {width : Nat}
    (sound : BookSound width state.book) (allowed : MayWrite state ticket)
    (reserve : ProviderIOClosure.Custody Nat → Prop) :
    ProviderIOClosure.Step reserve (toProvider state)
      (toProvider {state with book := consume state.book ticket.serial, present := true}) := by
  have live := live_serial (issued_within_the_current_gate allowed.2)
  have issued := sound.numbered _ live
  have pending : status state.book ticket.serial = .pending := by simp [status, issued, live]
  have step := ProviderIOClosure.Step.effect (state := toProvider state) (reserve := reserve)
    ticket.serial ⟨allowed.1, pending⟩
  change ProviderIOClosure.Step reserve (toProvider state)
    ⟨state.admitOpen, state.providerClosed, status (consume state.book ticket.serial), false,
      (fun _ => False), true, state.erased, true, none⟩
  rw [consuming_refines_status _ issued]
  exact step

def certifiedProviderView (state : State Image) : ProviderIOClosure.State Nat :=
  {toProvider state with
    observedFence := state.providerClosed
    observedDone := fun serial => status state.book serial = .done}

theorem authenticated_compact_view_can_certify_erasure {state : State Image}
    (closed : CanErase state) (absent : state.present = false) (reserve : ProviderIOClosure.Custody Nat → Prop) :
    ProviderIOClosure.Step reserve (certifiedProviderView state)
      {certifiedProviderView state with erased := true} := by
  have closure : ProviderIOClosure.ClosureKnown (certifiedProviderView state) := by
    refine ⟨closed.1, ?_⟩
    rcases closed.2 with fenced | empty
    · exact .inl fenced
    · refine .inr ?_
      intro serial known
      change status state.book serial = .done
      by_cases issued : 0 < serial ∧ serial ≤ state.book.issued
      · simp [status, issued, Serials, empty]
      · exact False.elim (known (by simp [certifiedProviderView, toProvider, status, issued]))
  exact .confirmAbsence closure absent

theorem confirmed_erase_rejects_delayed_effects {first last : State Image} {width : Nat}
    (closed : CanErase first) (absent : first.present = false) (trace : Trace width first last) :
    last.present = false ∧ ∀ ticket, ¬ MayWrite last ticket := by
  have refuses {state : State Image} (ineligible : CanErase state) (ticket : Ticket Image) :
      ¬ MayWrite state ticket := by
    intro attempt
    rcases ineligible.2 with fenced | empty
    · have inconsistent := attempt.1
      rw [fenced] at inconsistent
      cases inconsistent
    · have live := issued_within_the_current_gate attempt.2
      rw [empty] at live
      cases live
  have stable : CanErase last ∧ last.present = false := by
    induction trace with
    | same => exact ⟨closed, absent⟩
    | next _ step prior =>
        cases step with
        | issue _ opened _ =>
            have alreadyClosed := prior.1.1
            rw [opened] at alreadyClosed
            cases alreadyClosed
        | effect ticket eligible => exact False.elim (refuses prior.1 ticket eligible)
        | sealEntrance => exact ⟨⟨rfl, prior.1.2⟩, prior.2⟩
        | sealProvider stopped => exact ⟨⟨stopped, .inl rfl⟩, prior.2⟩
        | erase ready => exact ⟨ready, rfl⟩
        | restart => exact prior
  exact ⟨stable.2, refuses stable.1⟩

structure Address (Image : Type) where
  slot : Reservation.Slot
  state : State Image

def LiveNamespace (address : Address Image) (id : Nat) : Prop :=
  address.slot.live = some id

def ScopedWrite (address : Address Image) (id : Nat) (ticket : Ticket Image) : Prop :=
  LiveNamespace address id ∧ MayWrite address.state ticket

theorem scoped_write_requires_current_namespace {address : Address Image} {id : Nat} {ticket : Ticket Image}
    (permitted : ScopedWrite address id ticket) : LiveNamespace address id := by
  exact permitted.1

def CanReclaim (address : Address Image) : Prop :=
  CanErase address.state ∧ address.state.present = false

inductive AddressStep (width : Nat) : Address Image → Address Image → Prop
  | start {address} (vacant : address.slot.live = none) :
      AddressStep width address ⟨⟨address.slot.issuedThrough + 1, some (address.slot.issuedThrough + 1)⟩, initial⟩
  | run {address next} (namespaceId : Nat) (sameScope : LiveNamespace address namespaceId)
      (step : Step width address.state next) :
      AddressStep width address {address with state := next}
  | reclaim {address} (namespaceId : Nat) (current : LiveNamespace address namespaceId)
      (verified : CanReclaim address) :
      AddressStep width address ⟨{address.slot with live := none}, initial⟩
  | restart {address} : AddressStep width address address

inductive AddressTrace (width : Nat) : Address Image → Address Image → Prop
  | same (address) : AddressTrace width address address
  | next {first before after} : AddressTrace width first before → AddressStep width before after →
      AddressTrace width first after

theorem reclamation_requires_stable_absence {address : Address Image} (verified : CanReclaim address) :
    CanErase address.state ∧ address.state.present = false := by
  exact verified

theorem a_recycled_address_never_admits_the_old_namespace
    {first last : Address Image} {width id : Nat} (stale : Reservation.Stale id first.slot)
    (trace : AddressTrace width first last) : ¬ LiveNamespace last id := by
  have preserved : Reservation.Stale id last.slot := by
    induction trace with
    | same => exact stale
    | next _ step prior =>
        cases step with
        | start empty => exact Reservation.stale_preserved prior (.prepare empty)
        | reclaim _ current _ => exact Reservation.stale_preserved prior (.consume current)
        | _ => exact prior
  exact preserved.2

theorem an_old_ticket_cannot_apply_at_a_recycled_address
    {first last : Address Image} {width id : Nat} (stale : Reservation.Stale id first.slot)
    (trace : AddressTrace width first last) (ticket : Ticket Image) :
    ¬ ScopedWrite last id ticket := by
  intro permitted
  exact a_recycled_address_never_admits_the_old_namespace stale trace
    (scoped_write_requires_current_namespace permitted)

theorem a_scoped_ticket_can_take_the_exact_physical_step
    {address : Address Image} {width id : Nat} {ticket : Ticket Image}
    (allowed : ScopedWrite address id ticket) :
    AddressStep width address
      {address with state := {address.state with book := consume address.state.book ticket.serial, present := true}} :=
  .run id (scoped_write_requires_current_namespace allowed) (.effect ticket allowed.2)

#print axioms issued_within_the_current_gate
#print axioms numbered_slot_has_exactly_one_binding
#print axioms completing_the_effect_certifies_closed_exact_ticket
#print axioms initial_book_is_bounded
#print axioms each_step_preserves_durable_issuance_and_live_bound
#print axioms arbitrary_histories_need_only_the_live_ticket_window
#print axioms issued_absence_is_a_terminal_provider_status
#print axioms a_compacted_book_cannot_identify_the_old_payload
#print axioms closed_serial_survives_every_compact_book_step
#print axioms a_certified_ticket_cannot_be_reopened
#print axioms issuance_refines_the_provider_model
#print axioms consumption_refines_a_single_provider_effect
#print axioms authenticated_compact_view_can_certify_erasure
#print axioms confirmed_erase_rejects_delayed_effects
#print axioms scoped_write_requires_current_namespace
#print axioms reclamation_requires_stable_absence
#print axioms a_recycled_address_never_admits_the_old_namespace
#print axioms an_old_ticket_cannot_apply_at_a_recycled_address
#print axioms a_scoped_ticket_can_take_the_exact_physical_step

end TicketBook
