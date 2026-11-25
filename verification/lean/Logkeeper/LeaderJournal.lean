import Logkeeper.LeaderJournal.Application

namespace Logkeeper.LeaderJournal

set_option warningAsError true

abbrev Cluster (Payload : Type) := State (Request Payload)

def appliedView [DecidableEq Payload] (s : Cluster Payload) (keeper : KeeperId) : Journal Payload :=
  replay (s.applied keeper)

def committedView [DecidableEq Payload] (s : Cluster Payload) : Journal Payload :=
  replay s.committed

/-- A reply can be emitted by a leader once its exact command has been applied.
    The suffix after the command can already contain additional decisions. -/
structure AppendReply [DecidableEq Payload] (s : Cluster Payload) (lsn : Nat) (payload : Payload) where
  keeper : KeeperId
  term : Nat
  fence : Fence
  prior : Log (Request Payload)
  leader : s.leader = some keeper
  applied : (prior ++ [⟨term, .apply (.append fence lsn payload)⟩]) <+: s.applied keeper
  result : (execute (replay prior) (.append fence lsn payload)).2 = .appended lsn

theorem AppendReply.applied_record [DecidableEq Payload] {s : Cluster Payload}
    {lsn : Nat} {payload : Payload} (reply : AppendReply s lsn payload) :
    (appliedView s reply.keeper).record lsn = some payload := by
  have record := (successful_append_record reply.result).2.2
  have progress := replay_progress reply.applied
  have atDecision :
      (replay (reply.prior ++ [⟨reply.term, .apply (.append reply.fence lsn payload)⟩])).record lsn =
        some payload := by
    simpa [replay, List.foldl_append, applyEntry] using record
  exact progress.record atDecision

theorem acknowledged_append_survives [DecidableEq Payload] {members : List KeeperId}
    {acknowledged later : Cluster Payload} {lsn : Nat} {payload : Payload}
    (reached : Reachable members acknowledged) (reply : AppendReply acknowledged lsn payload)
    (trace : Trace acknowledged later) :
    (committedView later).record lsn = some payload := by
  have sound := reachable_sound reached
  have earlier := (sound.applied reply.keeper).1.trans (trace_committed_prefix trace sound)
  exact (replay_progress earlier).record reply.applied_record

theorem elected_leader_recovers_acknowledged [DecidableEq Payload] {members : List KeeperId}
    {acknowledged before : Cluster Payload} {lsn : Nat} {payload : Payload}
    {candidate : KeeperId} {votes : KeeperId → Bool}
    (reached : Reachable members acknowledged) (reply : AppendReply acknowledged lsn payload)
    (trace : Trace acknowledged before)
    (permitted : before.configuration = before.candidateConfiguration candidate ∨
      before.configuration.Change (before.candidateConfiguration candidate))
    (quorum : (before.candidateConfiguration candidate).quorum votes)
    (rank : ∀ keeper, votes keeper = true → AtLeast (before.durable keeper) (before.durable candidate)) :
    (replay (before.durable candidate)).record lsn = some payload := by
  have sound := trace.sound (reachable_sound reached)
  have history := elected_log_contains_committed sound permitted quorum rank
  exact (replay_progress history).record (acknowledged_append_survives reached reply trace)

theorem record_bounds {state : Journal Payload} {lsn : Nat} {payload : Payload}
    (record : state.record lsn = some payload) : 0 < lsn ∧ lsn ≤ state.head := by
  by_cases zero : lsn = 0
  · simp [Journal.record, zero] at record
  · rw [Journal.record, ite_eq_right zero] at record
    have inBounds := (List.getElem?_eq_some_iff.mp record).1
    unfold Journal.head
    omega

/-- Use a configuration revision as well as its member set. A later move can
    return to a roster with the same names. -/
def configurationVersion (log : Log Application) : Nat :=
  log.countP fun entry =>
    match entry.command with
    | .configure _ => true
    | _ => false

/-- The invocation, capture, quorum confirmation and apply wait are in trace
    order. A confirmation is a round-bound response in this abstract machine. -/
structure HeadRead [DecidableEq Payload] (invoked returned : Cluster Payload) where
  keeper : KeeperId
  captured : Cluster Payload
  confirmed : Cluster Payload
  invokedBeforeCapture : Trace invoked captured
  capturedBeforeConfirmation : Trace captured confirmed
  confirmedBeforeReturn : Trace confirmed returned
  capturedByLeader : captured.leader = some keeper
  confirmedByLeader : confirmed.leader = some keeper
  currentTermCommitted : lastTerm captured.committed = captured.term
  settledAtCapture : captured.configuration = captured.effectiveConfiguration
  settledAtConfirmation : confirmed.configuration = confirmed.effectiveConfiguration
  sameTerm : captured.term = confirmed.term
  sameMembership : captured.configuration = confirmed.configuration
  sameRevision : configurationVersion captured.committed = configurationVersion confirmed.committed
  voters : KeeperId → Bool
  quorum : captured.configuration.quorum voters
  responds : confirmed.responds voters
  applied : captured.committed <+: returned.applied keeper

def HeadRead.reply [DecidableEq Payload] {invoked returned : Cluster Payload}
    (call : HeadRead invoked returned) : Except Reply Nat :=
  observeHead (replay ((returned.applied call.keeper).take call.captured.committed.length))

theorem HeadRead.reply_at_capture [DecidableEq Payload] {invoked returned : Cluster Payload}
    (call : HeadRead invoked returned) : call.reply = observeHead (committedView call.captured) := by
  have applied := call.applied
  obtain ⟨suffix, applied⟩ := applied
  unfold HeadRead.reply committedView
  rw [← applied, List.take_append_of_le_length (Nat.le_refl _), List.take_length]

theorem head_linearizes_at_capture [DecidableEq Payload] {members : List KeeperId}
    {invoked returned : Cluster Payload} (reached : Reachable members invoked)
    (call : HeadRead invoked returned) :
    invoked.committed <+: call.captured.committed ∧
      call.captured.committed <+: returned.committed ∧
      call.reply = observeHead (committedView call.captured) := by
  have sound := reachable_sound reached
  have first := trace_committed_prefix call.invokedBeforeCapture sound
  have middle := trace_committed_prefix call.capturedBeforeConfirmation
    (call.invokedBeforeCapture.sound sound)
  have last := trace_committed_prefix call.confirmedBeforeReturn
    (call.capturedBeforeConfirmation.sound (call.invokedBeforeCapture.sound sound))
  exact ⟨first, middle.trans last, call.reply_at_capture⟩

theorem head_after_acknowledged_append [DecidableEq Payload] {members : List KeeperId}
    {acknowledged invoked returned : Cluster Payload} {lsn head : Nat} {payload : Payload}
    (reached : Reachable members acknowledged) (reply : AppendReply acknowledged lsn payload)
    (beforeInvocation : Trace acknowledged invoked) (call : HeadRead invoked returned)
    (served : call.reply = .ok head) :
    lsn ≤ head ∧ (committedView call.captured).record lsn = some payload := by
  have record := acknowledged_append_survives reached reply beforeInvocation
  have sampled := trace_committed_prefix call.invokedBeforeCapture
    (beforeInvocation.sound (reachable_sound reached))
  have exactRecord := (replay_progress sampled).record record
  have bound := (record_bounds exactRecord).2
  have value : (committedView call.captured).head = head := by
    rw [call.reply_at_capture] at served
    unfold observeHead at served
    split at served
    · contradiction
    · exact Except.ok.inj served
  exact ⟨value ▸ bound, exactRecord⟩

theorem local_page_returns_committed_bytes [DecidableEq Payload] {members : List KeeperId}
    {s : Cluster Payload} {keeper start limit offset : Nat} {page : Page Payload}
    {payload : Payload} (reached : Reachable members s)
    (read : readPage (appliedView s keeper) start limit = .ok page)
    (item : page.records[offset]? = some payload) :
    page.floor ≤ start + offset ∧ start + offset ≤ page.head ∧
      (committedView s).record (start + offset) = some payload := by
  obtain ⟨floor, head, retained, withinHead, record⟩ :=
    page_record_exact (replay_valid (s.applied keeper)) read item
  have represents := ((reachable_sound reached).applied keeper).1
  exact ⟨floor.symm ▸ retained, head.symm ▸ withinHead, (replay_progress represents).record record⟩

theorem committed_floor_and_tombstone_monotone [DecidableEq Payload] {members : List KeeperId}
    {before after : Cluster Payload} (reached : Reachable members before)
    (trace : Trace before after) :
    (committedView before).floor ≤ (committedView after).floor ∧
      ((committedView before).deleted = true → observeHead (committedView after) = .error .deleted) := by
  have progresses := replay_progress (trace_committed_prefix trace (reachable_sound reached))
  refine ⟨progresses.floor, ?_⟩
  intro deleted
  have terminal : (committedView after).deleted = true := progresses.deleted deleted
  simp [observeHead, terminal]

#print axioms elected_log_contains_committed
#print axioms step_preserves_sound
#print axioms step_changes_configuration
#print axioms seal_refuses_previous_writer
#print axioms retry_retained
#print axioms conflicting_retry_refused
#print axioms elected_leader_recovers_acknowledged
#print axioms acknowledged_append_survives
#print axioms head_linearizes_at_capture
#print axioms head_after_acknowledged_append
#print axioms local_page_returns_committed_bytes
#print axioms committed_floor_and_tombstone_monotone

end Logkeeper.LeaderJournal
