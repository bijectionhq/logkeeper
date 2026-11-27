import Logkeeper.ConsensusAdditions.OffloadPrefix
import Logkeeper.ConsensusAdditions.EpochLease

set_option warningAsError true

namespace Logkeeper.ConsensusAdditions.JournalContract

structure Writer where
  epoch : Nat
  principal : Nat
  session : Nat
  deriving DecidableEq, Repr

structure RecoveryFence where
  epoch : Nat
  head : Nat
  deriving DecidableEq, Repr

inductive Source where
  | survivor
  | objectStore
  deriving DecidableEq, Repr

structure Recovery where
  fence : RecoveryFence
  configurationEpoch : Nat
  lossPoint : Nat
  exact : Bool
  source : Source
  time : Nat
  deriving DecidableEq, Repr

inductive Entry where
  | data (epoch payload : Nat)
  | recovery (record : Recovery) (marker : Option Nat)
  deriving DecidableEq, Repr

/-- Positions start at one. The list includes a ghost copy of trimmed history,
so a refinement can compare the exact retained prefix across a recovery. -/
structure State where
  entries : List Entry := []
  floor : Nat := 1
  epoch : Nat := 0
  writer : Option Writer := none
  configurationEpoch : Nat := 0
  pending : Option Recovery := none
  /-- Ghost: every recovery installed so far, oldest first. -/
  recoveries : List Recovery := []
  deriving DecidableEq, Repr

def State.head (state : State) : Nat := state.entries.length

def State.retained (state : State) (lsn : Nat) : Option Entry :=
  if 0 < lsn ∧ state.floor ≤ lsn then state.entries[lsn - 1]? else none

def State.owns (state : State) (writer : Writer) : Prop :=
  state.pending = none ∧ state.writer = some writer

instance (state : State) (writer : Writer) : Decidable (state.owns writer) :=
  inferInstanceAs (Decidable (_ ∧ _))

inductive Command where
  | «seal» (writer : Writer)
  | append (writer : Writer) (lsn payload : Nat)
  | trim (writer : Writer) (through : Nat)
  | recover (survivor offloaded time : Nat)
  | acknowledge (fence : RecoveryFence) (marker : Option Nat)
  | head
  deriving DecidableEq, Repr

inductive Reply where
  | at (lsn : Nat)
  | trimmed (floor : Nat)
  | fenced (epoch : Nat)
  | conflict (head : Nat)
  | recovered (head : Nat)
  | unavailable
  | unit
  deriving DecidableEq, Repr

def advanceFloor (state : State) (through : Nat) : Nat :=
  max state.floor (min through state.head + 1)

def report (state : State) (survivor offloaded time : Nat) : Recovery :=
  let cut := max survivor offloaded
  ⟨⟨state.epoch + 1, cut⟩, state.configurationEpoch + 1, cut, true,
    if survivor < offloaded then .objectStore else .survivor, time⟩

def install (state : State) (record : Recovery) : State :=
  { state with
    entries := state.entries.take record.fence.head
    epoch := record.fence.epoch
    writer := none
    configurationEpoch := record.configurationEpoch
    pending := some record
    recoveries := state.recoveries ++ [record] }

def writeEntry (state : State) (record : Recovery) (marker : Option Nat) : State :=
  { state with pending := none, entries := state.entries ++ [.recovery record marker] }

/-- The ordered keeper reducer after admission of an authenticated command.
The recovery installer is the effect of the catalog decision and lease
wait-out. The command carries two certified committed cuts in journal LSNs. -/
def apply (state : State) : Command → State × Reply
  | .seal writer =>
    if state.pending.isSome then (state, .recovered state.head)
    else if state.epoch < writer.epoch then
      ({ state with epoch := writer.epoch, writer := some writer }, .at state.head)
    else if state.writer = some writer then (state, .at state.head)
    else (state, .fenced state.epoch)
  | .append writer lsn payload =>
    if !decide (state.owns writer) then (state, .fenced state.epoch)
    else if lsn < state.floor then (state, .trimmed state.floor)
    else if state.retained lsn = some (.data writer.epoch payload) then (state, .at lsn)
    else if lsn = state.head + 1 then
      ({ state with entries := state.entries ++ [.data writer.epoch payload] }, .at lsn)
    else (state, .conflict state.head)
  | .trim writer through =>
    if state.owns writer then ({ state with floor := advanceFloor state through }, .unit)
    else (state, .fenced state.epoch)
  | .recover survivor offloaded time =>
    let next := report state survivor offloaded time
    if state.floor ≤ next.lossPoint + 1 ∧ next.lossPoint ≤ state.head then
      (install state next, .recovered next.lossPoint)
    else (state, .conflict state.head)
  | .acknowledge fence marker =>
    let lsn := fence.head + 1
    match state.pending with
    | some record =>
      if record.fence = fence ∧ state.head = fence.head then
        (writeEntry state record marker, .at lsn)
      else (state, .conflict state.head)
    | none =>
      match state.retained lsn with
      | some (.recovery record original) =>
        if record.fence = fence ∧ original = marker then (state, .at lsn)
        else (state, .conflict state.head)
      | _ => (state, if lsn < state.floor then .trimmed state.floor else .conflict state.head)
  | .head => (state, .at state.head)

/-- Successful abstract transitions. Refusals below leave the abstract state
unchanged and carry the observations that justify their error. -/
inductive Contract : State → Command → Reply → State → Prop
  | «seal» {state writer} :
      state.pending = none → state.epoch < writer.epoch →
      Contract state (.seal writer) (.at state.head)
        { state with epoch := writer.epoch, writer := some writer }
  | sealRetry {state writer} : state.owns writer →
      Contract state (.seal writer) (.at state.head) state
  | append {state writer lsn payload} :
      state.owns writer → state.floor ≤ lsn → lsn = state.head + 1 →
      Contract state (.append writer lsn payload) (.at lsn)
        { state with entries := state.entries ++ [.data writer.epoch payload] }
  | appendRetry {state writer lsn payload} :
      state.owns writer → state.retained lsn = some (.data writer.epoch payload) →
      Contract state (.append writer lsn payload) (.at lsn) state
  | trim {state writer through floor} :
      state.owns writer → floor = max state.floor (min through state.head + 1) →
      Contract state (.trim writer through) .unit { state with floor }
  | recover {state survivor offloaded time cut record} :
      cut = max survivor offloaded → state.floor ≤ cut + 1 → cut ≤ state.head →
      record = ⟨⟨state.epoch + 1, cut⟩, state.configurationEpoch + 1, cut, true,
        if survivor < offloaded then .objectStore else .survivor, time⟩ →
      Contract state (.recover survivor offloaded time) (.recovered cut)
        { state with
          entries := state.entries.take cut
          epoch := record.fence.epoch
          writer := none
          pending := some record
          configurationEpoch := record.configurationEpoch
          recoveries := state.recoveries ++ [record] }
  | acknowledge {state record fence marker} :
      state.pending = some record → record.fence = fence → state.head = fence.head →
      Contract state (.acknowledge fence marker) (.at (fence.head + 1))
        { state with pending := none, entries := state.entries ++ [.recovery record marker] }
  | acknowledgeRetry {state fence marker record} :
      state.pending = none → state.retained (fence.head + 1) = some (.recovery record marker) →
      record.fence = fence → Contract state (.acknowledge fence marker) (.at (fence.head + 1)) state
  | readHead (state) : Contract state .head (.at state.head) state
  | refuseSealRecovery {state writer record} : state.pending = some record →
      Contract state (.seal writer) (.recovered state.head) state
  | refuseSeal {state writer} : state.pending = none → writer.epoch ≤ state.epoch →
      state.writer ≠ some writer → Contract state (.seal writer) (.fenced state.epoch) state
  | refuseAppendFence {state writer lsn payload} : ¬ state.owns writer →
      Contract state (.append writer lsn payload) (.fenced state.epoch) state
  | refuseAppendTrimmed {state writer lsn payload} : state.owns writer → lsn < state.floor →
      Contract state (.append writer lsn payload) (.trimmed state.floor) state
  | refuseAppendConflict {state writer lsn payload} : state.owns writer → state.floor ≤ lsn →
      state.retained lsn ≠ some (.data writer.epoch payload) → lsn ≠ state.head + 1 →
      Contract state (.append writer lsn payload) (.conflict state.head) state
  | refuseTrim {state writer through} : ¬ state.owns writer →
      Contract state (.trim writer through) (.fenced state.epoch) state
  | refuseRecover {state survivor offloaded time} :
      ¬ (state.floor ≤ max survivor offloaded + 1 ∧ max survivor offloaded ≤ state.head) →
      Contract state (.recover survivor offloaded time) (.conflict state.head) state
  | refuseStandingAck {state record fence marker} : state.pending = some record →
      ¬ (record.fence = fence ∧ state.head = fence.head) →
      Contract state (.acknowledge fence marker) (.conflict state.head) state
  | refuseTrimmedAck {state fence marker} : state.pending = none → fence.head + 1 < state.floor →
      Contract state (.acknowledge fence marker) (.trimmed state.floor) state
  | refuseRetainedAck {state fence marker} : state.pending = none → state.floor ≤ fence.head + 1 →
      (∀ record, state.retained (fence.head + 1) = some (.recovery record marker) →
        record.fence ≠ fence) →
      Contract state (.acknowledge fence marker) (.conflict state.head) state

theorem ordered_keeper_step_refines (state : State) (command : Command) :
    Contract state command (apply state command).2 (apply state command).1 := by
  cases command with
  | «seal» writer =>
    cases pending : state.pending with
    | some record => simpa [apply, pending] using
        (Contract.refuseSealRecovery (writer := writer) pending)
    | none =>
      by_cases advances : state.epoch < writer.epoch
      · simpa [apply, pending, advances] using (Contract.seal pending advances)
      · by_cases bound : state.writer = some writer
        · simpa [apply, pending, advances, bound] using
            (Contract.sealRetry (state := state) (writer := writer) ⟨pending, bound⟩)
        · simpa [apply, pending, advances, bound] using
            (Contract.refuseSeal pending (Nat.le_of_not_gt advances) bound)
  | append writer lsn payload =>
    by_cases owns : state.owns writer
    · by_cases trimmed : lsn < state.floor
      · simpa [apply, owns, trimmed] using (Contract.refuseAppendTrimmed (payload := payload) owns trimmed)
      · by_cases retained : state.retained lsn = some (.data writer.epoch payload)
        · simpa [apply, owns, trimmed, retained] using (Contract.appendRetry owns retained)
        · by_cases next : lsn = state.head + 1
          · subst lsn
            simpa [apply, owns, trimmed, retained] using
              (Contract.append (payload := payload) owns (Nat.le_of_not_gt trimmed) rfl)
          · simpa [apply, owns, trimmed, retained, next] using
              (Contract.refuseAppendConflict owns (Nat.le_of_not_gt trimmed) retained next)
    · simpa [apply, owns] using (Contract.refuseAppendFence (lsn := lsn) (payload := payload) owns)
  | trim writer through =>
    by_cases owns : state.owns writer
    · simpa [apply, owns, advanceFloor] using (Contract.trim (through := through) owns rfl)
    · simpa [apply, owns] using (Contract.refuseTrim (through := through) owns)
  | recover survivor offloaded time =>
    by_cases valid : state.floor ≤ max survivor offloaded + 1 ∧ max survivor offloaded ≤ state.head
    · simpa [apply, report, install, valid] using (Contract.recover (time := time) rfl valid.1 valid.2 rfl)
    · simpa [apply, report, valid] using (Contract.refuseRecover (time := time) valid)
  | acknowledge fence marker =>
    cases pending : state.pending with
    | some record =>
      by_cases same : record.fence = fence ∧ state.head = fence.head
      · simpa [apply, pending, same, writeEntry] using
          (Contract.acknowledge (marker := marker) pending same.1 same.2)
      · simpa [apply, pending, same] using (Contract.refuseStandingAck (marker := marker) pending same)
    | none =>
      have trimmedOrConflict (noMatch : ∀ record,
          state.retained (fence.head + 1) = some (.recovery record marker) → record.fence ≠ fence) :
          Contract state (.acknowledge fence marker)
            (if fence.head + 1 < state.floor then .trimmed state.floor else .conflict state.head)
            state := by
        split
        · exact .refuseTrimmedAck pending (by assumption)
        · exact .refuseRetainedAck pending (by omega) noMatch
      cases kept : state.retained (fence.head + 1) with
      | none => simpa [apply, pending, kept] using trimmedOrConflict (by simp [kept])
      | some entry =>
        cases entry with
        | data =>
          simpa [apply, pending, kept] using trimmedOrConflict (by simp [kept])
        | recovery record original =>
          by_cases same : record.fence = fence ∧ original = marker
          · rcases same with ⟨sameFence, sameMarker⟩
            subst original
            have retry := Contract.acknowledgeRetry pending kept sameFence
            simpa [apply, pending, kept, sameFence] using retry
          · have above : state.floor ≤ fence.head + 1 := by
              unfold State.retained at kept
              split at kept
              · rename_i bounds
                exact bounds.2
              · contradiction
            have noMatch : ∀ candidate,
                state.retained (fence.head + 1) = some (.recovery candidate marker) →
                candidate.fence ≠ fence := by
              intro candidate equal
              rw [kept] at equal
              cases equal
              exact fun fenceEqual => same ⟨fenceEqual, rfl⟩
            simpa [apply, pending, kept, same] using Contract.refuseRetainedAck pending above noMatch
  | head => exact .readHead state

/-- A finite linearization certificate supplied by Raft and the lease-gated
catalog installer. Lost replies can leave events in this order. -/
structure Invocation where
  command : Command
  called : Nat
  decided : Nat
  answered : Nat

def Invocation.inInterval (call : Invocation) : Prop :=
  call.called ≤ call.decided ∧ call.decided ≤ call.answered

def execute : State → List Invocation → List Reply × State
  | state, [] => ([], state)
  | state, call :: tail =>
    let (after, reply) := apply state call.command
    let (replies, final) := execute after tail
    (reply :: replies, final)

inductive Linearized : State → List Invocation → List Reply → State → Prop
  | nil (state) : Linearized state [] [] state
  | cons {before after final call tail reply replies} :
      Contract before call.command reply after → call.inInterval →
      Linearized after tail replies final →
      Linearized before (call :: tail) (reply :: replies) final

theorem ordered_trace_refines (state : State) (calls : List Invocation)
    (intervals : ∀ call ∈ calls, call.inInterval) :
    Linearized state calls (execute state calls).1 (execute state calls).2 := by
  induction calls generalizing state with
  | nil => exact .nil state
  | cons call tail prior =>
    have rest := prior (apply state call.command).1 (by
      intro other member
      exact intervals other (List.mem_cons_of_mem _ member))
    exact .cons (ordered_keeper_step_refines state call.command)
      (intervals call (by simp)) rest

theorem linearization_respects_completed_calls (first second : Invocation)
    (firstValid : first.inInterval) (secondValid : second.inInterval)
    (before : first.answered < second.called) :
    first.decided < second.decided := by
  exact Nat.lt_of_le_of_lt firstValid.2 (Nat.lt_of_lt_of_le before secondValid.1)

theorem recovery_does_not_overlap_old_authority {D H L M commit grant learned t u : Nat}
    {holder waiter : EpochLease.Clock D H} (margin : D ≤ M) (horizon : L + M + D ≤ H)
    (granted : grant ≤ commit) (learnt : commit ≤ learned)
    (valid : EpochLease.Holds holder L M grant t) (waited : EpochLease.Waited waiter L M learned u) :
    t < u :=
  EpochLease.lease_precedes_wait margin horizon granted learnt valid waited

/-- The offload proof uses opaque carried records. The projection identifies
the same committed stream, its retained floor, and both certified cuts. -/
theorem recovery_reports_exact_loss (state : State) (encode : Entry → OffloadPrefix.Entry)
    (offload : OffloadPrefix.Offload) (survivor : OffloadPrefix.Survivor) (time : Nat)
    (sameLog : state.entries.map encode = offload.committed)
    (sameFloor : state.floor = offload.floor + 1)
    (good : OffloadPrefix.Good offload)
    (chosen : survivor.log.take survivor.commit <+: offload.committed)
    (held : survivor.commit ≤ survivor.log.length) :
    let cut := OffloadPrefix.known offload survivor
    let (next, reply) := apply state (.recover survivor.commit offload.through time)
    reply = .recovered cut ∧ next.head = cut ∧
      next.pending = some (report state survivor.commit offload.through time) ∧
      (next.entries.drop offload.floor).map encode = OffloadPrefix.restore offload survivor ∧
      state.entries.drop offload.floor =
        next.entries.drop offload.floor ++ state.entries.drop cut := by
  have ⟨restored, _⟩ := OffloadPrefix.restore_exact good survivor chosen held
  have heldChosen := chosen.length_le
  rw [List.length_take, Nat.min_eq_left held, ← sameLog, List.length_map] at heldChosen
  have offloadedChosen := OffloadPrefix.through_committed good
  rw [← sameLog, List.length_map] at offloadedChosen
  have cutWithin : max survivor.commit offload.through ≤ state.head := by
    unfold State.head
    omega
  have offloadFloor := good.floorBelow
  have floorWithin : state.floor ≤ max survivor.commit offload.through + 1 := by omega
  simp only [apply, report, floorWithin, cutWithin, and_self, ite_true, install]
  rw [Nat.max_comm survivor.commit offload.through]
  simp only [OffloadPrefix.known, State.head]
  have exactLength : max offload.through survivor.commit ≤ state.entries.length := by
    rw [Nat.max_comm] at cutWithin
    exact cutWithin
  refine ⟨trivial, by simp [Nat.min_eq_left exactLength], trivial, ?_, ?_⟩
  · rw [restored]
    unfold OffloadPrefix.segment OffloadPrefix.known
    rw [← sameLog, List.drop_take, List.map_take, List.map_drop]
  · have cutAbove : offload.floor ≤ max offload.through survivor.commit := by omega
    rw [List.drop_take]
    have parts := List.take_append_drop (max offload.through survivor.commit - offload.floor)
      (state.entries.drop offload.floor)
    rw [List.drop_drop, Nat.add_sub_of_le cutAbove] at parts
    exact parts.symm

theorem acknowledge_atomically_publishes_typed_entry (state : State) (record : Recovery)
    (marker : Option Nat) (standing : state.pending = some record)
    (atHead : state.head = record.fence.head) :
    let (next, reply) := apply state (.acknowledge record.fence marker)
    next.pending = none ∧ reply = .at (record.fence.head + 1) ∧
      next.entries = state.entries ++ [.recovery record marker] := by
  simp [apply, standing, atHead, writeEntry]

/-! ## Retries across an operator recovery

A writer whose append went unanswered retries it, and when the retry is
refused `Fenced` or `Trimmed` asks `Request::Written` whether its record is
in the stream. Below, `keeperWritten` is the lookup the keeper answers
today and `written` the one the contract needs. Without a recovery the
history is linear, so a committed attempt keeps its record or is trimmed,
and a negative lookup is conclusive. A recovery breaks that: it can erase
committed positions above its loss point. -/

def Entry.epoch : Entry → Nat
  | .data epoch _ => epoch
  | .recovery record _ => record.fence.epoch

/-- Facts of every reachable state. -/
structure Inv (state : State) : Prop where
  writer : ∀ bound, state.writer = some bound → bound.epoch = state.epoch
  bounded : ∀ entry ∈ state.entries, entry.epoch ≤ state.epoch
  pending : ∀ record, state.pending = some record → record.fence.epoch = state.epoch

theorem init_inv : Inv {} := ⟨by simp, by simp, by simp⟩

theorem step_inv {state : State} (inv : Inv state) (command : Command) :
    Inv (apply state command).1 := by
  cases command with
  | «seal» writer =>
    simp only [apply]
    split
    · exact inv
    · rename_i standing
      split
      · rename_i advances
        have none : state.pending = none := by simpa using standing
        refine ⟨?_, ?_, ?_⟩
        · intro bound same
          cases same
          rfl
        · exact fun entry member => Nat.le_of_lt (Nat.lt_of_le_of_lt (inv.bounded entry member) advances)
        · intro record same
          simp [none] at same
      · split <;> exact inv
  | append writer lsn payload =>
    simp only [apply]
    split
    · exact inv
    · rename_i owns
      have owned : state.owns writer := by simpa using owns
      split
      · exact inv
      · split
        · exact inv
        · split
          · refine ⟨inv.writer, ?_, inv.pending⟩
            intro entry member
            rcases List.mem_append.mp member with old | new
            · exact inv.bounded entry old
            · simp at new
              subst new
              exact Nat.le_of_eq (inv.writer writer owned.2)
          · exact inv
  | trim writer through =>
    simp only [apply]
    split
    · exact ⟨inv.writer, inv.bounded, inv.pending⟩
    · exact inv
  | recover survivor offloaded time =>
    simp only [apply]
    split
    · refine ⟨by simp [install], ?_, ?_⟩
      · intro entry member
        exact Nat.le_succ_of_le (inv.bounded entry (List.mem_of_mem_take member))
      · intro record same
        simp only [install, Option.some.injEq] at same
        subst same
        rfl
    · exact inv
  | acknowledge fence marker =>
    simp only [apply]
    split
    · rename_i record standing
      split
      · refine ⟨inv.writer, ?_, by simp [writeEntry]⟩
        intro entry member
        rcases List.mem_append.mp member with old | new
        · exact inv.bounded entry old
        · simp at new
          subst new
          exact Nat.le_of_eq (inv.pending record standing)
      · exact inv
    · split <;> first | exact inv | (split <;> exact inv)
  | head => exact inv

abbrev Attempt := Writer × Nat × Nat

/-- The append a reply says committed. -/
def committedBy : Command → Reply → List Attempt
  | .append writer lsn payload, .at _ => [(writer, lsn, payload)]
  | _, _ => []

/-- Reachable states with every append committed on the way, answered or not. -/
inductive Reach : State → List Attempt → Prop
  | init : Reach {} []
  | step {state attempts} (command : Command) : Reach state attempts →
      Reach (apply state command).1 (attempts ++ committedBy command (apply state command).2)

/-- A recovery installed after `writer`'s epoch that kept less than `lsn`. -/
def MayHaveErased (state : State) (writer : Writer) (lsn : Nat) : Prop :=
  ∃ record ∈ state.recoveries, writer.epoch < record.fence.epoch ∧ record.lossPoint < lsn

/-- A committed attempt keeps its record in the history, trimmed or not, or
a later recovery may have erased it. -/
def Evidence (state : State) (attempt : Attempt) : Prop :=
  (0 < attempt.2.1 ∧ state.entries[attempt.2.1 - 1]? = some (.data attempt.1.epoch attempt.2.2)) ∨
    MayHaveErased state attempt.1 attempt.2.1

private theorem evidence_extend {state next : State} {attempt : Attempt} (more : List Entry)
    (entries : next.entries = state.entries ++ more) (recoveries : next.recoveries = state.recoveries)
    (evidence : Evidence state attempt) : Evidence next attempt := by
  rcases evidence with ⟨positive, kept⟩ | ⟨record, member, erased⟩
  · have within : attempt.2.1 - 1 < state.entries.length := by
      rcases List.getElem?_eq_some_iff.mp kept with ⟨within, _⟩
      exact within
    exact Or.inl ⟨positive, by rw [entries, List.getElem?_append_left within, kept]⟩
  · exact Or.inr ⟨record, recoveries ▸ member, erased⟩

private theorem evidence_step {state : State} (inv : Inv state) (command : Command)
    {attempt : Attempt} (evidence : Evidence state attempt) :
    Evidence (apply state command).1 attempt := by
  have same : Evidence state attempt := evidence
  cases command with
  | «seal» writer =>
    simp only [apply]
    split
    · exact same
    · split
      · exact evidence_extend [] (by simp) rfl same
      · split <;> exact same
  | append writer lsn payload =>
    simp only [apply]
    split
    · exact same
    · split
      · exact same
      · split
        · exact same
        · split
          · exact evidence_extend _ rfl rfl same
          · exact same
  | trim writer through =>
    simp only [apply]
    split
    · exact evidence_extend [] (by simp) rfl same
    · exact same
  | recover survivor offloaded time =>
    simp only [apply]
    split
    · rcases same with ⟨positive, kept⟩ | ⟨record, member, erased⟩
      · by_cases within : attempt.2.1 ≤ (report state survivor offloaded time).fence.head
        · left
          refine ⟨positive, ?_⟩
          simp only [install]
          rw [List.getElem?_take_of_lt (by omega), kept]
        · right
          have epoch := inv.bounded _ (List.mem_of_getElem? kept)
          refine ⟨report state survivor offloaded time, by simp [install], ?_, ?_⟩
          · simp only [Entry.epoch] at epoch
            simp only [report]
            omega
          · simp only [report] at within ⊢
            omega
      · exact Or.inr ⟨record, by simp [install, member], erased⟩
    · exact same
  | acknowledge fence marker =>
    simp only [apply]
    split
    · split
      · exact evidence_extend _ rfl rfl same
      · exact same
    · split <;> first | exact same | (split <;> exact same)
  | head => exact same

private theorem evidence_new {state : State} {command : Command} {attempt : Attempt}
    (member : attempt ∈ committedBy command (apply state command).2) :
    Evidence (apply state command).1 attempt := by
  cases command with
  | append writer lsn payload =>
    by_cases owns : state.owns writer
    · by_cases trimmed : lsn < state.floor
      · simp [apply, owns, trimmed, committedBy] at member
      · by_cases kept : state.retained lsn = some (.data writer.epoch payload)
        · simp only [apply, owns, trimmed, kept, decide_true, Bool.not_true, Bool.false_eq_true,
            ite_false, ite_true, committedBy, List.mem_singleton] at member ⊢
          subst member
          unfold State.retained at kept
          split at kept
          · rename_i bounds
            exact Or.inl ⟨bounds.1, kept⟩
          · contradiction
        · by_cases next : lsn = state.head + 1
          · subst next
            simp only [apply, owns, trimmed, kept, decide_true, Bool.not_true, Bool.false_eq_true,
              ite_false, ite_true, committedBy, List.mem_singleton] at member ⊢
            subst member
            exact Or.inl ⟨Nat.succ_pos _, by simp [State.head]⟩
          · simp [apply, owns, trimmed, kept, next, committedBy] at member
    · simp [apply, owns, committedBy] at member
  | «seal» | trim | recover | acknowledge | head =>
    simp [committedBy] at member

theorem reach_evidence {state : State} {attempts : List Attempt} (reach : Reach state attempts) :
    Inv state ∧ ∀ attempt ∈ attempts, Evidence state attempt := by
  induction reach with
  | init => exact ⟨init_inv, by simp⟩
  | step command _ prior =>
    refine ⟨step_inv prior.1 command, ?_⟩
    intro attempt member
    rcases List.mem_append.mp member with old | new
    · exact evidence_step prior.1 command (prior.2 attempt old)
    · exact evidence_new new

inductive Written where
  | matching
  | missing
  | unknown
  | erased (lossPoint : Nat)
  deriving DecidableEq, Repr

/-- The keeper's `Request::Written` today: the retained history alone. -/
def keeperWritten (state : State) (writer : Writer) (lsn payload : Nat) : Written :=
  if lsn < state.floor then .unknown
  else if state.retained lsn = some (.data writer.epoch payload) then .matching
  else .missing

def erasedBy (state : State) (writer : Writer) (lsn : Nat) : Option Recovery :=
  state.recoveries.find? (fun record => decide (writer.epoch < record.fence.epoch ∧ record.lossPoint < lsn))

/-- The lookup the contract needs: a negative answer is conclusive only
when no recovery since the writer's epoch kept less than the position. -/
def written (state : State) (writer : Writer) (lsn payload : Nat) : Written :=
  match keeperWritten state writer lsn payload, erasedBy state writer lsn with
  | .missing, some record => .erased record.lossPoint
  | observed, _ => observed

/-- The client's answer to a refused retry: the refusal stands only on a
conclusive miss; an erased attempt reports the recovery. -/
def retryReply (refusal : Reply) : Written → Reply
  | .missing => refusal
  | .erased lossPoint => .recovered lossPoint
  | _ => .unavailable

theorem committed_attempt_is_never_missing {state : State} {attempts : List Attempt}
    (reach : Reach state attempts) {writer : Writer} {lsn payload : Nat}
    (committed : (writer, lsn, payload) ∈ attempts) :
    written state writer lsn payload ≠ .missing := by
  have evidence := (reach_evidence reach).2 _ committed
  intro missing
  cases refused : keeperWritten state writer lsn payload with
  | missing =>
    cases found : erasedBy state writer lsn with
    | some record => simp [written, refused, found] at missing
    | none =>
      unfold keeperWritten at refused
      split at refused
      · contradiction
      · rename_i above
        split at refused
        · contradiction
        · rename_i absent
          rcases evidence with ⟨positive, kept⟩ | ⟨record, member, erased⟩
          · exact absent (by simp [State.retained, positive, Nat.le_of_not_gt above, kept])
          · have := List.find?_eq_none.mp found record member
            simp [erased] at this
  | matching | unknown | erased => simp [written, refused] at missing

/-- The contract for an ambiguous retry: once an attempt committed, its retry
is never refused definitely, whatever happened since, including an operator
recovery that erased it. It answers `Unavailable`, or `Recovered` with the
loss point of a recovery that may have erased it. -/
theorem committed_attempt_retry_is_indefinite {state : State} {attempts : List Attempt}
    (reach : Reach state attempts) {writer : Writer} {lsn payload : Nat}
    (committed : (writer, lsn, payload) ∈ attempts) (refusal : Reply) :
    retryReply refusal (written state writer lsn payload) = .unavailable ∨
      ∃ lossPoint, retryReply refusal (written state writer lsn payload) = .recovered lossPoint := by
  have never := committed_attempt_is_never_missing reach committed
  cases h : written state writer lsn payload with
  | missing => exact absurd h never
  | erased lossPoint => exact Or.inr ⟨lossPoint, rfl⟩
  | matching | unknown => exact Or.inl rfl

/-- Without a recovery since the writer's epoch the keeper's lookup is
already the contract's: its negative answer is conclusive. -/
theorem keeper_lookup_is_exact_without_recovery (state : State) (writer : Writer) (lsn payload : Nat)
    (linear : erasedBy state writer lsn = none) :
    written state writer lsn payload = keeperWritten state writer lsn payload := by
  unfold written
  rw [linear]
  cases keeperWritten state writer lsn payload <;> rfl

/-- The keeper today: an append commits at LSN 1, and a recovery that keeps
nothing erases it. The keeper's lookup misses it and the client turns the
retry's `Fenced` refusal into a definite answer
(`a_retry_across_a_recovery_that_erased_its_attempt_is_not_refused_definitely`). -/
theorem keeper_lookup_refuses_an_erased_attempt :
    ∃ state, Reach state [(⟨1, 0, 0⟩, 1, 7)] ∧
      keeperWritten state ⟨1, 0, 0⟩ 1 7 = .missing ∧
      retryReply (.fenced state.epoch) (keeperWritten state ⟨1, 0, 0⟩ 1 7) = .fenced 2 := by
  have reach := Reach.step (.recover 0 0 0) (Reach.step (.append ⟨1, 0, 0⟩ 1 7)
    (Reach.step (.seal ⟨1, 0, 0⟩) Reach.init))
  exact ⟨_, by simpa [apply, committedBy, State.head, State.owns, State.retained] using reach,
    by decide, by decide⟩

/-- What the keeper must keep durably to decide `written`: the latest
recovery's epoch and the lowest loss point of any recovery. -/
def absorb (summary : Option (Nat × Nat)) (record : Recovery) : Option (Nat × Nat) :=
  some <| match summary with
    | none => (record.fence.epoch, record.lossPoint)
    | some held => (max held.1 record.fence.epoch, min held.2 record.lossPoint)

def summary (recoveries : List Recovery) : Option (Nat × Nat) := recoveries.foldl absorb none

private theorem summary_from (recoveries : List Recovery) (start : Option (Nat × Nat))
    {writer : Writer} {lsn : Nat}
    (witness : (∃ epoch loss, start = some (epoch, loss) ∧ writer.epoch < epoch ∧ loss < lsn) ∨
      ∃ record ∈ recoveries, writer.epoch < record.fence.epoch ∧ record.lossPoint < lsn) :
    ∃ epoch loss, recoveries.foldl absorb start = some (epoch, loss) ∧
      writer.epoch < epoch ∧ loss < lsn := by
  induction recoveries generalizing start with
  | nil =>
    rcases witness with found | ⟨_, member, _⟩
    · exact found
    · simp at member
  | cons first rest prior =>
    apply prior
    rcases witness with ⟨epoch, loss, rfl, newer, below⟩ | ⟨record, member, newer, below⟩
    · exact Or.inl ⟨_, _, rfl, by omega, by omega⟩
    · rcases List.mem_cons.mp member with rfl | later
      · left
        cases start with
        | none => exact ⟨_, _, rfl, newer, below⟩
        | some held => exact ⟨_, _, rfl, by omega, by omega⟩
      · exact Or.inr ⟨record, later, newer, below⟩

/-- Two numbers per stream decide the rule conservatively: a writer older
than the latest recovery, retrying above the lowest loss point. -/
theorem summary_covers_every_erasing_recovery (recoveries : List Recovery) (writer : Writer)
    (lsn : Nat) (erasing : ∃ record ∈ recoveries, writer.epoch < record.fence.epoch ∧ record.lossPoint < lsn) :
    ∃ epoch loss, summary recoveries = some (epoch, loss) ∧ writer.epoch < epoch ∧ loss < lsn :=
  summary_from recoveries none (Or.inr erasing)

#print axioms ordered_keeper_step_refines
#print axioms ordered_trace_refines
#print axioms linearization_respects_completed_calls
#print axioms recovery_does_not_overlap_old_authority
#print axioms recovery_reports_exact_loss
#print axioms acknowledge_atomically_publishes_typed_entry
#print axioms step_inv
#print axioms reach_evidence
#print axioms committed_attempt_is_never_missing
#print axioms committed_attempt_retry_is_indefinite
#print axioms keeper_lookup_is_exact_without_recovery
#print axioms keeper_lookup_refuses_an_erased_attempt
#print axioms summary_covers_every_erasing_recovery

end Logkeeper.ConsensusAdditions.JournalContract
