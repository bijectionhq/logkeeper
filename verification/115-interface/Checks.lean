import Interface

namespace Interface

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b =>
    if same : a = b then isTrue (congrArg Except.ok same)
    else isFalse (fun equal => same (Except.ok.inj equal))
  | .error a, .error b =>
    if same : a = b then isTrue (congrArg Except.error same)
    else isFalse (fun equal => same (Except.error.inj equal))
  | .error _, .ok _ => isFalse (by intro equal; cases equal)
  | .ok _, .error _ => isFalse (by intro equal; cases equal)

def key : Key := ⟨1, 2⟩
def other : Key := ⟨1, 3⟩
def selector : Range := ⟨1, 2, 4⟩

def write (key : Key) (value : Nat) : Write := ⟨key, 5, 9, some value⟩

def create : Request := ⟨1, 10, 0, [], [write key 7, write other 8]⟩
def overwrite : Request := ⟨1, 11, 1, [], [write key 12]⟩
def stale : Request := ⟨1, 12, 1, [.point key 5 (some 7)], [write other 99]⟩
def countStale : Request := ⟨1, 13, 0, [.count selector 5 0], [write other 100]⟩

def started := apply {} (.transaction create)
def held := apply started (.holdCut (.acquire 1 (.exact 1) 10))
def changed := apply held (.transaction overwrite)
def refused := apply changed (.transaction stale)

def atPoint (view : ReadView) := view.point key 5

theorem exactTemporalRead :
    read changed (.exact 1) atPoint = .ok (1, some 7) ∧
    read changed .latest atPoint = .ok (2, some 12) ∧
    read changed (.exact 1) (fun view => view.point key 9) = .ok (1, none) := by
  decide

theorem projectedRange :
    read changed (.exact 1) (fun view =>
      let rows := view.range selector 5
      (rows.take 1, rows.length)) = .ok (1, ([(2, 7)], 2)) := by
  decide

theorem validateAtDecision :
    (transact changed stale).2 = .ok ⟨3, false⟩ ∧
    (transact changed countStale).2 = .ok ⟨3, false⟩ ∧
    read refused .latest (fun view => view.point other 5) = .ok (3, some 8) := by
  decide

theorem retryUsesOriginal :
    (transact refused create).2 = .ok ⟨1, true⟩ ∧
    (transact refused stale).2 = .ok ⟨3, false⟩ ∧
    head (transact refused stale).1 = 3 := by
  decide

theorem retryRejectsChanged :
    (transact refused { create with writes := [] }).2 = .error .changedRequest := by
  decide

theorem exactHold :
    heldRead (armFloor changed 2) 1 0 atPoint = .ok (1, some 7) ∧
    heldRead (advanceTime changed 10) 1 0 atPoint = .error .noLease ∧
    heldRead changed 2 0 atPoint = .error .noLease ∧
    heldRead (hold changed (.release 2 0)).1 1 0 atPoint = .ok (1, some 7) := by
  decide

theorem freshReadRetry :
    (hold (advanceTime changed 10) (.acquire 1 (.exact 1) 20)).2 = .ok (some 1) ∧
    heldRead (hold (advanceTime changed 10) (.acquire 1 (.exact 1) 20)).1
      1 1 atPoint = .ok (1, some 7) ∧
    (hold (armFloor (advanceTime changed 10) 2) (.acquire 1 (.exact 1) 20)).2 =
      .error .unavailable := by
  decide

theorem watchResets :
    subscribe (armFloor (advanceTime changed 10) 2) 1 = .reset 2 := by
  decide

theorem watchOrdered :
    subscribe refused 1 = .batch 3 [(2, overwrite.writes)] := by
  decide

theorem effectiveOverlay :
    overlayPoint (some 7) [] = some 7 ∧
    overlayPoint (some 7) [some 12, none] = none := by
  decide

def erased := forget changed key.subject 4

theorem forgetAtDecision :
    read erased .latest atPoint = .ok (3, none) ∧
    read erased .latest (fun view => view.point other 5) = .ok (3, some 8) ∧
    heldRead erased 1 0 atPoint = .ok (1, some 7) ∧
    (transact erased ⟨1, 99, 3, [], [write key 15]⟩).2 = .error .forgottenSubject := by
  decide

theorem forgetAtDeadline :
    (advanceTime erased 4).leases.length = 1 ∧
    heldRead (advanceTime erased 4) 1 0 atPoint = .error .erased ∧
    subscribe erased 1 = .reset 3 := by
  decide

theorem witness :
    ∃ store, Reachable store ∧
      read store .latest (fun view => view.point other 5) = .ok (4, some 8) ∧
      heldRead store 1 0 atPoint = .error .erased ∧
      subscribe store 1 = .reset 4 ∧
      (transact store stale).2 = .ok ⟨3, false⟩ := by
  refine ⟨[Step.transaction create, .holdCut (.acquire 1 (.exact 1) 10),
    .transaction overwrite, .transaction stale, .erase key.subject 4, .time 4]
      |>.foldl apply {}, traceReachable _ _ .empty, ?_⟩
  decide

#print axioms trimRespectsLiveHold
#print axioms exactCut
#print axioms projectionAtOneCut
#print axioms prefixStable
#print axioms originalRetry
#print axioms changedRetry
#print axioms conflictingGuardRefuses
#print axioms rejectedWatchInvisible
#print axioms rejectedWritesInvisible
#print axioms resetBelowFloor
#print axioms orderedBatch
#print axioms forgottenPoint
#print axioms forgetKeepsHolds
#print axioms revokedRead
#print axioms untouchedOverlay
#print axioms overlayWins
#print axioms traceReachable
#print axioms exactTemporalRead
#print axioms projectedRange
#print axioms validateAtDecision
#print axioms retryUsesOriginal
#print axioms retryRejectsChanged
#print axioms exactHold
#print axioms freshReadRetry
#print axioms watchResets
#print axioms watchOrdered
#print axioms effectiveOverlay
#print axioms forgetAtDecision
#print axioms forgetAtDeadline
#print axioms witness

end Interface
