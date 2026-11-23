import Std

set_option warningAsError true

namespace ReadCustody

structure Image (Extent Payload : Type) where
  extent : Extent
  bytes : Payload

inductive Operation (Extent Payload : Type) where
  | unadmitted
  | borrowing (image : Image Extent Payload)
  | stopped
  | completed (bytes : Payload)

structure Store (Request Extent Payload : Type) where
  admitting : Bool
  index : Option (Image Extent Payload)
  physical : Extent → Option Payload
  operations : Request → Operation Extent Payload

def replace [DecidableEq Key] (table : Key → Value) (key : Key) (value : Value) : Key → Value :=
  fun found => if found = key then value else table found

def Covered (store : Store Request Extent Payload) : Prop :=
  ∀ request image, store.operations request = .borrowing image →
    store.physical image.extent = some image.bytes

inductive Step {Request Extent Payload : Type} [DecidableEq Request] [DecidableEq Extent] (effectiveStop : Request → Prop) :
    Store Request Extent Payload → Store Request Extent Payload → Prop
  | materialize {store} (extent : Extent) (bytes : Payload)
      (fresh : store.physical extent = none) :
      Step effectiveStop store {store with physical := replace store.physical extent (some bytes)}
  | publishIndex {store} (image : Image Extent Payload)
      (materialized : store.physical image.extent = some image.bytes) :
      Step effectiveStop store {store with index := some image}
  | borrow {store} (request : Request) (image : Image Extent Payload)
      (openGate : store.admitting = true)
      (unused : store.operations request = .unadmitted)
      (indexed : store.index = some image)
      (reserved : store.physical image.extent = some image.bytes) :
      Step effectiveStop store {store with
        operations := replace store.operations request (.borrowing image)}
  | closeAdmission {store} :
      Step effectiveStop store {store with admitting := false}
  | clearIndex {store} (closedGate : store.admitting = false) :
      Step effectiveStop store {store with index := none}
  | confirmStop {store} (request : Request) (image : Image Extent Payload)
      (usingImage : store.operations request = .borrowing image)
      (stopped : effectiveStop request) :
      Step effectiveStop store {store with operations := replace store.operations request .stopped}
  | finish {store} (request : Request) (image : Image Extent Payload)
      (usingImage : store.operations request = .borrowing image) :
      Step effectiveStop store {store with
        operations := replace store.operations request (.completed image.bytes)}
  | reclaim {store} (extent : Extent)
      (unreferenced : ∀ image, store.index = some image → image.extent ≠ extent)
      (unborrowed : ∀ request image, store.operations request = .borrowing image →
        image.extent ≠ extent) :
      Step effectiveStop store {store with physical := replace store.physical extent none}

private theorem nonBorrowingUpdate [DecidableEq Request]
    {store : Store Request Extent Payload} (covered : Covered store) (request : Request)
    (result : Operation Extent Payload) (finishes : ∀ image, result ≠ .borrowing image) :
    Covered {store with operations := replace store.operations request result} := by
  intro other image live
  by_cases equal : other = request
  · exact False.elim (finishes image (by simpa [replace, equal] using live))
  · exact covered other image (by simpa [replace, equal] using live)

theorem step_preserves_exact_borrows [DecidableEq Request] [DecidableEq Extent]
    {effectiveStop : Request → Prop} {before after : Store Request Extent Payload}
    (covered : Covered before) (transition : Step effectiveStop before after) : Covered after := by
  cases transition with
  | materialize extent _ fresh =>
      intro request image live
      have old := covered request image live
      have different : image.extent ≠ extent := by
        intro same
        rw [same, fresh] at old
        contradiction
      simpa [replace, different] using old
  | publishIndex => exact covered
  | borrow request image _ _ _ reserved =>
      intro observer borrowed live
      by_cases equal : observer = request
      · have same := Operation.borrowing.inj (by simpa [replace, equal] using live)
        subst borrowed
        exact reserved
      · exact covered observer borrowed (by simpa [replace, equal] using live)
  | closeAdmission => exact covered
  | clearIndex => exact covered
  | confirmStop request _ _ _ => exact nonBorrowingUpdate covered request .stopped (by simp)
  | finish request image _ => exact nonBorrowingUpdate covered request (.completed image.bytes) (by simp)
  | reclaim extent _ unborrowed =>
      intro request image live
      have distinct : image.extent ≠ extent := unborrowed request image live
      simpa [replace, distinct] using covered request image live

inductive Trace {Request Extent Payload : Type} [DecidableEq Request] [DecidableEq Extent] (effectiveStop : Request → Prop) :
    Store Request Extent Payload → Store Request Extent Payload → Prop
  | same (store : Store Request Extent Payload) : Trace effectiveStop store store
  | next {origin before after} : Trace effectiveStop origin before → Step effectiveStop before after →
      Trace effectiveStop origin after

theorem trace_preserves_exact_borrows [DecidableEq Request] [DecidableEq Extent]
    {effectiveStop : Request → Prop} {first last : Store Request Extent Payload}
    (covered : Covered first) (trace : Trace effectiveStop first last) : Covered last := by
  induction trace with
  | same => exact covered
  | next _ step prior => exact step_preserves_exact_borrows prior step

theorem admission_was_open [DecidableEq Request] [DecidableEq Extent]
    {effectiveStop : Request → Prop} {before after : Store Request Extent Payload}
    (transition : Step effectiveStop before after) (openAfter : after.admitting = true) :
    before.admitting = true := by
  cases transition <;> simp_all

theorem fenced_operation_never_succeeds [DecidableEq Request] [DecidableEq Extent]
    {effectiveStop : Request → Prop} {first last : Store Request Extent Payload} {request : Request}
    (stopped : first.operations request = .stopped) (trace : Trace effectiveStop first last) :
    last.operations request = .stopped := by
  induction trace with
  | same => exact stopped
  | next _ transition prior =>
      cases transition with
      | borrow other _ _ unused _ _ =>
          have otherId : request ≠ other := by
            intro same
            rw [← same, prior] at unused
            contradiction
          simpa [replace, otherId] using prior
      | confirmStop other _ _ _ =>
          by_cases same : request = other
          · simp [replace, same]
          · simpa [replace, same] using prior
      | finish other _ usingImage =>
          have otherId : request ≠ other := by
            intro same
            rw [← same, prior] at usingImage
            contradiction
          simpa [replace, otherId] using prior
      | _ => exact prior

theorem already_borrowed_read_can_finish_after_close [DecidableEq Request] [DecidableEq Extent]
    {effectiveStop : Request → Prop} {store : Store Request Extent Payload}
    (request : Request) (image : Image Extent Payload)
    (known : Covered store) (reading : store.operations request = .borrowing image) :
    ∃ result, Trace effectiveStop store result ∧
      result.admitting = false ∧ result.operations request = .completed image.bytes ∧
      result.physical image.extent = some image.bytes := by
  let closed := {store with admitting := false}
  let finished := {closed with operations := replace closed.operations request (.completed image.bytes)}
  exact ⟨finished, .next (.next (.same store) .closeAdmission) (.finish request image reading),
    rfl, by simp [finished, replace], known request image reading⟩

theorem unknown_endpoint_stop_cannot_justify_reclamation
    (reclaim : Observer → Bool) (stillReading stopped : Observer)
    (sameObservation : stillReading = stopped) (safety : reclaim stillReading = false) :
    reclaim stopped = false := by
  rw [← sameObservation, safety]

#print axioms step_preserves_exact_borrows
#print axioms trace_preserves_exact_borrows
#print axioms admission_was_open
#print axioms fenced_operation_never_succeeds
#print axioms already_borrowed_read_can_finish_after_close
#print axioms unknown_endpoint_stop_cannot_justify_reclamation

end ReadCustody
