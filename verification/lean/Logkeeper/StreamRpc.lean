import Logkeeper.StreamHead
import Logkeeper.StreamWriter

/-! Per-keeper exchanges at the writer's asynchronous boundaries. Indices are
cuts in a timeline of three keepers. A lost or cancelled reply does not produce
a completed exchange. -/

namespace Logkeeper.StreamRpc

open PrefixAgreement StreamJournal StreamIO StreamHead
open JournalRefinement (Majority majorities_overlap)

set_option autoImplicit false
set_option warningAsError true

variable {Payload : Type}

/-- A completed RPC carries its keeper, request and the delivery that produced its reply.
    A later delivery of the same packet can have a different decision index. -/
structure Exchange (trace : Timeline Payload) (keeper : KeeperId) (caller : Nat)
    (request : Request Payload) where
  sent : Nat
  decided : Nat
  received : Nat
  send : Next (trace.state sent) (.send (.call keeper caller request)) (trace.state (sent + 1))
  deliver : Next (trace.state decided) (.deliver (.call keeper caller request))
    (trace.state (decided + 1))
  inFlight : sent < decided + 1
  durableBeforeReceive : decided + 1 ≤ received

variable {trace : Timeline Payload} {keeper : KeeperId} {caller : Nat} {request : Request Payload}

def Exchange.sample (rpc : Exchange trace keeper caller request) : Nat := rpc.decided + 1

theorem Exchange.effect (rpc : Exchange trace keeper caller request) :
    (trace.state rpc.sample).keeper keeper =
      StreamIO.effect (trace.state rpc.decided).writer caller
        ((trace.state rpc.decided).keeper keeper) request := by
  have delivered := rpc.deliver
  change (trace.state (rpc.decided + 1)).keeper keeper = _
  generalize trace.state rpc.decided = before at delivered ⊢
  generalize trace.state (rpc.decided + 1) = after at delivered ⊢
  cases delivered
  simp [State.apply, update]

theorem Exchange.admitted (rpc : Exchange trace keeper caller request) :
    Admitted ((trace.state rpc.decided).keeper keeper) caller request := by
  have delivered := rpc.deliver
  generalize trace.state rpc.decided = before at delivered ⊢
  generalize trace.state (rpc.decided + 1) = after at delivered
  cases delivered with
  | deliver _ admitted => exact admitted

/-- The exact head bound carried by an admitted publication RPC. A complete Sync
    and a floor install can also establish local publication coverage. -/
def Publication : Request Payload → Nat → Prop
  | .sync _ _ _ _ head, cut | .installFloor _ head, cut
  | .append _ _ _ head, cut | .publish _ head, cut => cut ≤ head
  | _, _ => False

theorem publication_covers (rpc : Exchange trace keeper caller request)
    {cut : Nat} (sent : Publication request cut) :
    cut ≤ ((trace.state rpc.sample).keeper keeper).head := by
  rw [rpc.effect]
  cases request <;> simp_all [Publication, effect, accept] <;> omega

/-- The writer puts these successes into slots indexed by the originating lane. -/
def Counted (a b : KeeperId) : KeeperId → Bool := fun k => decide (k = a ∨ k = b)

theorem distinct_slots {a b : KeeperId} (distinct : a ≠ b) :
    Majority ensemble (Counted a b) :=
  two_of_three_is_majority a b distinct

/-- A successful local publication wait either covers the empty prefix or has
    two distinct lane completions that each published the requested cut. -/
def PublishedBefore (trace : Timeline Payload) (cut completion : Nat) : Prop :=
  cut = 0 ∨ ∃ (left right : KeeperId) (caller : Nat) (a b : Request Payload), left ≠ right ∧
    ∃ x : Exchange trace left caller a, ∃ y : Exchange trace right caller b,
      Publication a cut ∧ Publication b cut ∧ x.received ≤ completion ∧ y.received ≤ completion

theorem publication_wait_covers {cut completion : Nat}
    (waited : PublishedBefore trace cut completion) : Committed (trace.state completion) cut := by
  rcases waited with rfl | ⟨left, _, _, _, _, _, x, _, published, _, done, _⟩
  · exact published_cut trace 0 (Nat.le_refl completion) (Nat.zero_le _)
  · exact published_cut trace left (Nat.le_trans x.durableBeforeReceive done)
      (publication_covers x published)

theorem trim_reply_covers {epoch through : Nat}
    (rpc : Exchange trace keeper caller (.trim epoch through)) :
    through < ((trace.state rpc.sample).keeper keeper).floor ∧
    through ≤ ((trace.state rpc.sample).keeper keeper).head := by
  have admitted := rpc.admitted
  rw [rpc.effect]
  exact ⟨Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right ..), admitted.2.2.2⟩

theorem delete_reply_tombstone (rpc : Exchange trace keeper caller (.delete : Request Payload)) :
    ((trace.state rpc.sample).keeper keeper).deleted = true := by
  rw [rpc.effect]
  rfl

/-- Return after two distinct exact Trim replies. The writer's successful local
    gate, when called for, precedes both sends. The other branch gets coverage
    independently from the two keeper admissions. -/
theorem trim_completion {epoch through localHead checked completion : Nat} {a b : KeeperId}
    (left : Exchange trace a caller (.trim epoch through))
    (right : Exchange trace b caller (.trim epoch through))
    (distinct : a ≠ b)
    (waited : through ≤ localHead → PublishedBefore trace through checked)
    (sentAfterCheck : checked ≤ left.sent ∧ checked ≤ right.sent)
    (received : left.received ≤ completion ∧ right.received ≤ completion) :
    Majority ensemble (Counted a b) ∧
    (∀ k ∈ ensemble, Counted a b k = true → ∃ sample, sample ≤ completion ∧
      through < ((trace.state sample).keeper k).floor) ∧
    (through ≤ localHead → Committed (trace.state checked) through) ∧
    Committed (trace.state completion) through := by
  have leftInTime := Nat.le_trans left.durableBeforeReceive received.1
  have rightInTime := Nat.le_trans right.durableBeforeReceive received.2
  have localCut (known : through ≤ localHead) := publication_wait_covers (waited known)
  have covered : Committed (trace.state completion) through := by
    by_cases known : through ≤ localHead
    · exact trace.committed
        (by have := left.inFlight; have := sentAfterCheck.1; omega) (localCut known)
    · exact published_cut trace a leftInTime (trim_reply_covers left).2
  refine ⟨distinct_slots distinct, ?_, localCut, covered⟩
  intro k _ counted
  simp only [Counted, decide_eq_true_eq] at counted
  rcases counted with rfl | rfl
  · exact ⟨left.sample, leftInTime, (trim_reply_covers left).1⟩
  · exact ⟨right.sample, rightInTime, (trim_reply_covers right).1⟩

theorem delete_completion {a b : KeeperId} {completion : Nat}
    (left : Exchange trace a caller (.delete : Request Payload))
    (right : Exchange trace b caller (.delete : Request Payload))
    (distinct : a ≠ b) (received : left.received ≤ completion ∧ right.received ≤ completion) :
    Majority ensemble (Counted a b) ∧
    ∀ k ∈ ensemble, Counted a b k = true → ∃ sample, sample ≤ completion ∧
      ((trace.state sample).keeper k).deleted = true := by
  refine ⟨distinct_slots distinct, ?_⟩
  intro k _ counted
  simp only [Counted, decide_eq_true_eq] at counted
  rcases counted with rfl | rfl
  · exact ⟨left.sample, Nat.le_trans left.durableBeforeReceive received.1, delete_reply_tombstone left⟩
  · exact ⟨right.sample, Nat.le_trans right.durableBeforeReceive received.2, delete_reply_tombstone right⟩

theorem tombstone_persists (trace : Timeline Payload) {first last : Nat}
    (ordered : first ≤ last) (keeper : KeeperId)
    (deleted : ((trace.state first).keeper keeper).deleted = true) :
    ((trace.state last).keeper keeper).deleted = true := by
  induction ordered with
  | refl => exact deleted
  | @step time _ prior =>
      obtain ⟨_, next⟩ := trace.next time
      rcases (every_action_refines (trace.reachable time) next).2 keeper with step | same
      · exact tombstone_is_terminal step prior
      · rwa [same]

theorem delete_blocks_future_quorum {a b : KeeperId} {completion later : Nat}
    (left : Exchange trace a caller (.delete : Request Payload))
    (right : Exchange trace b caller (.delete : Request Payload))
    (distinct : a ≠ b) (received : left.received ≤ completion ∧ right.received ≤ completion)
    (after : completion ≤ later) :
    ¬ Majority ensemble (fun k => !((trace.state later).keeper k).deleted) := by
  obtain ⟨quorum, evidence⟩ := delete_completion left right distinct received
  apply StreamWriter.delete_quorum_blocks_live_quorum quorum
  intro k member counted
  obtain ⟨sample, checked, deleted⟩ := evidence k member counted
  rw [tombstone_persists trace (Nat.le_trans checked after) k deleted]
  rfl

/-- A lane sample is a Check or the successful Append that provided the observed tail.
    A retained retry corresponds to a publication in the keeper automaton. -/
inductive HeadSource : Request Payload → Prop
  | checked : HeadSource .observe
  | appended {epoch position records head} : HeadSource (.append epoch position records head)
  | published {epoch head} : HeadSource (.publish epoch head)

structure HeadReply (trace : Timeline Payload) (keeper : KeeperId) where
  caller : Nat
  request : Request Payload
  rpc : Exchange trace keeper caller request
  source : HeadSource request

/-- Read the exact view used to project the reply. Appended carries its tail only;
    its eligibility is established by the request's admission and effect. -/
def HeadReply.view (response : HeadReply trace keeper) : CheckView :=
  check (effect (trace.state response.rpc.decided).writer response.caller
    ((trace.state response.rpc.decided).keeper keeper) response.request)

theorem exact_head_reply (response : HeadReply trace keeper) :
    response.view = check ((trace.state response.rpc.sample).keeper keeper) := by
  rw [response.rpc.effect]
  rfl

theorem append_reply_eligible {epoch position head : Nat} {records : List Payload}
    (rpc : Exchange trace keeper caller (.append epoch position records head)) :
    Synced ((trace.state rpc.sample).keeper keeper) epoch := by
  rw [rpc.effect]
  exact ⟨rfl, rfl⟩

theorem publish_reply_eligible {epoch head : Nat}
    (rpc : Exchange trace keeper caller (.publish epoch head : Request Payload)) :
    Synced ((trace.state rpc.sample).keeper keeper) epoch := by
  have admitted := rpc.admitted
  rw [rpc.effect]
  exact admitted.2.1

/-- Queue drain fixes the batch. Each counted slot is tagged by its keeper and
    follows the drain and the round's own fresh send. -/
structure HeadBatch (trace : Timeline Payload) (call : Invocation) (epoch : Nat) where
  opened : Nat
  drained : call.started ≤ opened
  replies : (keeper : KeeperId) → Option (HeadReply trace keeper)
  quorum : Majority ensemble (fun k => (replies k).isSome)
  counted : ∀ k (response : HeadReply trace k), replies k = some response →
    opened ≤ response.rpc.sent ∧ response.rpc.received ≤ call.replied ∧
    response.view.promised = epoch ∧ response.view.synced = epoch

def HeadBatch.round {call : Invocation} {epoch : Nat}
    (batch : HeadBatch trace call epoch) : CheckRound :=
  ⟨epoch, batch.opened, fun k => (batch.replies k).isSome,
    fun k => ((batch.replies k).map (·.rpc.sample)).getD 0,
    fun k => ((batch.replies k).map (·.view)).getD ⟨0, 0, 0, 0⟩⟩

def HeadBatch.sent {call : Invocation} {epoch : Nat} (batch : HeadBatch trace call epoch)
    (keeper : KeeperId) : Nat := ((batch.replies keeper).map (·.rpc.sent)).getD 0

def HeadBatch.samples {call : Invocation} {epoch : Nat}
    (batch : HeadBatch trace call epoch) : Samples call batch.round where
  sent := batch.sent
  queued := batch.drained
  quorum := batch.quorum
  fresh k _ answered := by
    cases slot : batch.replies k with
    | none => simp [HeadBatch.round, slot] at answered
    | some response =>
        have evidence := batch.counted k response slot
        simpa [HeadBatch.round, HeadBatch.sent, Exchange.sample, slot] using
          And.intro evidence.1 (And.intro (Nat.le_of_lt response.rpc.inFlight)
            (Nat.le_trans response.rpc.durableBeforeReceive evidence.2.1))
  eligible k _ answered := by
    cases slot : batch.replies k with
    | none => simp [HeadBatch.round, slot] at answered
    | some response => simpa [HeadBatch.round, slot] using (batch.counted k response slot).2.2

theorem HeadBatch.exact_view {call : Invocation} {epoch : Nat}
    (batch : HeadBatch trace call epoch) (keeper : KeeperId)
    (answered : batch.round.answered keeper = true) :
    batch.round.view keeper = check ((trace.state (batch.round.sampled keeper)).keeper keeper) := by
  cases slot : batch.replies keeper with
  | none => simp [HeadBatch.round, slot] at answered
  | some response => simpa [HeadBatch.round, slot] using exact_head_reply response

theorem writer_head_completion {call : Invocation} {epoch result prior : Nat}
    (batch : HeadBatch trace call epoch) (covers : SamplesCovered batch.round result)
    {writer : Nat} (keeper₁ keeper₂ : KeeperId)
    {left right : Request Payload}
    (published₁ : Exchange trace keeper₁ writer left)
    (published₂ : Exchange trace keeper₂ writer right)
    (distinct : keeper₁ ≠ keeper₂)
    (publication : Publication left result ∧ Publication right result)
    (finished : published₁.received ≤ call.replied ∧ published₂.received ≤ call.replied)
    (priorAck : Committed (trace.state call.started) prior) :
    Majority ensemble (Counted keeper₁ keeper₂) ∧ prior ≤ result ∧
    ∃ event, call.started ≤ event ∧ event ≤ call.replied ∧ AtCut trace batch.opened result event := by
  have chosen := published_cut trace keeper₁
    (Nat.le_trans published₁.durableBeforeReceive finished.1)
    (publication_covers published₁ publication.1)
  exact ⟨distinct_slots distinct, head_linearizable trace batch.samples
    (fun k _ answered => batch.exact_view k answered) covers chosen priorAck⟩

theorem observer_head_completion {call : Invocation} {epoch confirmedEpoch result prior : Nat}
    (batch : HeadBatch trace call epoch) (confirmed : HeadBatch trace call confirmedEpoch)
    (covers : SamplesCovered batch.round result)
    (published : Majority ensemble
      (fun k => confirmed.round.answered k && decide (result ≤ (confirmed.round.view k).head)))
    (priorAck : Committed (trace.state call.started) prior) :
    prior ≤ result ∧ ∃ event, call.started ≤ event ∧ event ≤ call.replied ∧
      AtCut trace batch.opened result event :=
  head_after_publication trace batch.samples confirmed.samples
    (fun k _ answered => batch.exact_view k answered)
    (fun k _ answered => confirmed.exact_view k answered) covers published priorAck

/-- Continue the reachable inherited-publication execution with a real send
    and delivery for Trim through the inherited head. -/
theorem trim_exchange_witness :
    ∃ trace : Timeline Nat, ∃ rpc : Exchange trace 0 2 (.trim 2 1),
      rpc.sent = 0 ∧ rpc.sample = 2 ∧ ((trace.state rpc.sample).keeper 0).floor = 2 := by
  obtain ⟨s, reached, head, synced, _, _, _, _, elected, live, owner⟩ := StreamIOWitness.automaton_witness
  let packet := Packet.call (Payload := Nat) 0 2 (.trim 2 1)
  let flight := { s with net := packet :: s.net }
  let durable := flight.apply 0 2 (.trim 2 1)
  let states : Nat → State Nat
    | 0 => s
    | 1 => flight
    | _ => durable
  have send : Next (states 0) (.send packet) (states 1) := by
    change Next s (.send packet) flight
    exact .send elected
  have deliver : Next (states 1) (.deliver packet) (states 2) := by
    change Next flight (.deliver packet) durable
    exact .deliver List.mem_cons_self ⟨live, owner, synced, Nat.le_of_eq head.symm⟩
  let trace : Timeline Nat := ⟨states, reached, fun time => by
    cases time with
    | zero => exact ⟨_, send⟩
    | succ time =>
        cases time with
        | zero => exact ⟨_, deliver⟩
        | succ time => exact ⟨.restart 0, .restart⟩⟩
  let rpc : Exchange trace 0 2 (.trim 2 1) := ⟨0, 1, 2, send, deliver, by decide, by decide⟩
  refine ⟨trace, rpc, rfl, rfl, ?_⟩
  rw [rpc.effect]
  change max (s.keeper 0).floor 2 = 2
  apply Nat.max_eq_right
  have floor := (keeper_bounds ((reachable_inv reached).reached 0)).2.2
  omega

#print axioms trim_completion
#print axioms delete_completion
#print axioms delete_blocks_future_quorum
#print axioms exact_head_reply
#print axioms writer_head_completion
#print axioms observer_head_completion
#print axioms trim_exchange_witness

end Logkeeper.StreamRpc
