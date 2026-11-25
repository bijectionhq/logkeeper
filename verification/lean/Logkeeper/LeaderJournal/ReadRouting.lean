import Logkeeper.LeaderJournal.ReplicaGate

namespace Logkeeper.LeaderJournal.ReadRouting

set_option warningAsError true

structure Scope where
  stream : Bootstrap.StreamId
  genesisIdentity : Nat
  deriving DecidableEq, Repr

structure Preferred where
  revision : Nat
  members : List KeeperId
  deriving DecidableEq, Repr

/-- The adapter verifies the committed revision and scope before supplying a
    candidate. Hints used for discovery never call this transition directly. -/
def Preferred.refresh (cached candidate : Preferred) : Preferred :=
  if cached.revision < candidate.revision then candidate else cached

theorem refresh_never_regresses (cached candidate : Preferred) :
    cached.revision ≤ (cached.refresh candidate).revision := by
  unfold Preferred.refresh
  split <;> omega

structure Attempt where
  primary : Option KeeperId
  hedge : Option KeeperId
  fallback : List KeeperId
  deriving DecidableEq, Repr

/-- The hedge starts only if the primary is still pending after the delay.
    Discovery refresh has its own finite retry allowance in the adapter. -/
def plan (preferred discovery : List KeeperId) (fallbackLimit : Nat) : Attempt :=
  let primary := preferred.head?
  let hedge := (preferred.filter fun keeper => some keeper != primary).head?
  ⟨primary, hedge, (discovery.filter fun keeper => some keeper != primary && some keeper != hedge).take fallbackLimit⟩

def hedgeOnDelay (attempt : Attempt) (primaryPending : Bool) : Option KeeperId :=
  if primaryPending then attempt.hedge else none

theorem fallback_is_bounded (preferred discovery : List KeeperId) (budget : Nat) :
    (plan preferred discovery budget).fallback.length ≤ budget :=
  List.length_take_le _ _

def PageGate (expected authenticated : Scope) (requiredHead : Nat) (page : Page Payload) : Prop :=
  authenticated = expected ∧ requiredHead ≤ page.head

/-- The authenticated response and source proof bind to the same stream. A
    later observation can have any roster reachable by the committed trace. -/
theorem delayed_page_preserves_committed_bytes [DecidableEq Payload]
    {members : List KeeperId} {fleet : Installation.Fleet (Request Payload)}
    {expected authenticated : Scope} {served observed : Cluster Payload}
    {keeper start limit offset requiredHead : Nat} {page : Page Payload} {payload : Payload}
    (gate : PageGate expected authenticated requiredHead page)
    (reached : Reachable members served) (later : Trace served observed)
    (read : Installation.HealthyPage fleet authenticated.stream served keeper start limit page)
    (item : page.records[offset]? = some payload) :
    authenticated = expected ∧ requiredHead ≤ page.head ∧
      page.floor ≤ start + offset ∧ start + offset ≤ page.head ∧
      (committedView observed).record (start + offset) = some payload := by
  obtain ⟨floor, head, exactRecord⟩ := Installation.checked_page_returns_committed_bytes reached read item
  have committedPrefix := trace_committed_prefix later (reachable_sound reached)
  exact ⟨gate.1, gate.2, floor, head, (replay_progress committedPrefix).record exactRecord⟩

theorem page_below_required_head_rejected {expected authenticated : Scope} {page : Page Payload}
    (behind : page.head < requiredHead) : ¬ PageGate expected authenticated requiredHead page := by
  intro accepted
  exact Nat.not_le_of_gt behind accepted.2

theorem wrong_stream_or_genesis_rejected {expected authenticated : Scope} {page : Page Payload}
    (wrong : authenticated ≠ expected) : ¬ PageGate expected authenticated requiredHead page :=
  fun accepted => wrong accepted.1

/-- Authoritative absence is an answer from the trusted bootstrap binding
    authority. A routing miss maps to unknown and has no such evidence. -/
def provesAbsent (authority : Bootstrap.Lookup) : Prop := authority = .known none

theorem route_miss_is_not_absence : ¬ provesAbsent .unknown := by
  simp [provesAbsent]

theorem routed_head_requires_quorum_read [DecidableEq Payload] {members : List KeeperId}
    {invoked returned : Cluster Payload} (reached : Reachable members invoked)
    (read : HeadRead invoked returned) :
    invoked.committed <+: read.captured.committed ∧
      read.captured.committed <+: returned.committed ∧
      read.reply = observeHead (committedView read.captured) :=
  head_linearizes_at_capture reached read

theorem obsolete_preferred_tries_discovery :
    (plan [7, 8] [7, 8, 10, 11, 12] 2).fallback = [10, 11] := by decide

theorem slow_preferred_issues_one_hedge :
    let attempt := plan [7, 8, 9] [10] 1
    attempt.primary = some 7 ∧ hedgeOnDelay attempt true = some 8 ∧
      hedgeOnDelay attempt false = none := by decide

#print axioms delayed_page_preserves_committed_bytes
#print axioms page_below_required_head_rejected
#print axioms routed_head_requires_quorum_read

end Logkeeper.LeaderJournal.ReadRouting
