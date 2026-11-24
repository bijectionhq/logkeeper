import Logkeeper.DurableAcceptor

namespace Logkeeper.PrefixTrace

open PrefixAgreement DurableAcceptor JournalRefinement

set_option warningAsError true

abbrev History := List Nat
abbrev Report := Nat × Nat  -- ballot and exact encoded prefix ID

inductive Event where
  | roster (group : Nat) (members : List Nat)
  | promise (group voter ballot : Nat) (report : Option Report)
  | prepared (group ballot : Nat) (winner : Option Report) (voters : List Nat)
  | issue (group ballot image : Nat) (history : History)
  | accept (group voter ballot image : Nat) (history : History)
  | choice (group ballot image : Nat) (voters : List Nat)
  | restart (group voter floor : Nat) (report : Option Report)
  | seal (source target base : Nat) (history : History)
  | install (group voter ballot base image : Nat) (history : History)

private def get [BEq K] (items : List (K × V)) (key : K) : Option V :=
  (items.find? fun pair => pair.1 == key).map Prod.snd

private def check (ok : Bool) (error : String) : Except String Unit :=
  if ok then .ok () else .error error

def ConfiguredMajority (members voters : List Nat) : Prop :=
  voters.Nodup ∧ (∀ voter ∈ voters, voter ∈ members) ∧ Majority members voters.contains

def majorityCheck (members voters : List Nat) : Bool :=
  decide voters.Nodup && voters.all members.contains && decide (Majority members voters.contains)

theorem majorityCheck_spec (members voters : List Nat) :
    majorityCheck members voters = true ↔ ConfiguredMajority members voters := by
  simp [majorityCheck, ConfiguredMajority, List.all_eq_true, and_assoc]

theorem checked_certificate_is_chosen {ledger : Ledger Nat Command} (voters : List Nat)
    (quorum : majorityCheck ledger.members voters = true) (ballot : Nat) (history : List Command)
    (evidence : ∀ voter ∈ voters, ledger.voted voter ⟨ballot, history⟩) :
    Chosen ledger ballot history := by
  refine ⟨voters.contains, ((majorityCheck_spec _ _).mp quorum).2.2, ?_⟩
  intro voter _ counted
  exact ⟨_, evidence voter (List.contains_iff_mem.mp counted), rfl, List.prefix_rfl⟩

#guard !(majorityCheck [1, 2, 3] [1, 1])
#guard !(majorityCheck [1, 2, 3] [1, 4])

#print axioms majorityCheck_spec
#print axioms checked_certificate_is_chosen

structure Cohort where
  members : List Nat
  floor : List (Nat × Nat) := []
  latest : List (Nat × Report) := []
  replies : List ((Nat × Nat) × Option Report) := []
  rounds : List (Nat × (History × List Nat)) := []
  issued : List (Nat × Nat) := []
  voted : List (Nat × Report) := []
  chosen : List (Nat × History) := []
  images : List (Nat × History) := []
  sealed : Option History := none

structure TraceState where
  groups : List (Nat × Cohort) := []
  transfers : List (Nat × (Nat × History)) := []

private def requireMember (state : Cohort) (voter : Nat) : Except String Unit :=
  check (state.members.contains voter) "unconfigured voter"

private def remember (state : Cohort) (image : Nat) (history : History) : Except String Cohort := do
  check (image != 0 && ((get state.images image).all (· == history))) "image changed history"
  return { state with images := (image, history) :: state.images }

private def materialize (state : Cohort) (report : Report) :
    Except String (Vote Nat) := do
  let some history := get state.images report.2 | throw "unknown accepted image"
  return ⟨report.1, history⟩

private def recordVote (state : Cohort) (voter ballot image : Nat) : Cohort :=
  { state with latest := (voter, ballot, image) :: state.latest
               voted := (voter, ballot, image) :: state.voted }

private def stepGroup (state : TraceState) (group : Nat)
    (update : Cohort → Except String Cohort) : Except String TraceState := do
  let some current := get state.groups group | throw "unknown cohort"
  let next ← update current
  return { state with groups := (group, next) :: state.groups.filter (·.1 != group) }

def step (state : TraceState) : Event → Except String TraceState
  | .roster group members => do
    check ((get state.groups group).isNone && decide members.Nodup) "duplicate cohort or voter"
    return { state with groups := (group, { members }) :: state.groups }
  | .promise group voter ballot report => stepGroup state group fun current => do
    requireMember current voter
    let floor := (get current.floor voter).getD 0
    check (ballot != 0 && decide (PrepareAdmitted floor ballot)) "promise floor"
    check (report == get current.latest voter) "promise report"
    -- An equal-floor reply is an acknowledgement retry. A recorded fresh reply
    -- stays fixed, even if a retry is made after an accept at that same ballot.
    if floor == ballot then return current
    return { current with floor := (voter, ballot) :: current.floor
                          replies := ((ballot, voter), report) :: current.replies }
  | .prepared group ballot winner voters => stepGroup state group fun current => do
    check ((get current.rounds ballot).isNone) "duplicate coordinator prepare"
    check (majorityCheck current.members voters) "prepare majority"
    let reports ← voters.mapM fun voter =>
      match get current.replies (ballot, voter) with
      | some report => pure report
      | none => throw "missing promise"
    let observed := reports.filterMap id
    let seed ← match winner with
      | none =>
        if observed.isEmpty then pure [] else throw "recovery omitted accepted image"
      | some report => do
        check (observed.contains report && report.1 < ballot) "unreported recovery image"
        let best ← materialize current report
        for candidate in observed do
          let other ← materialize current candidate
          check (candidate.1 < ballot && decide (WinnerDominates other best)) "recovery rank"
          check (candidate.1 != report.1 || candidate.2 == report.2) "divergent equal-rank images"
        pure best.history
    return { current with rounds := (ballot, seed, voters) :: current.rounds }
  | .issue group ballot image history => stepGroup state group fun current => do
    let some (seed, _) := get current.rounds ballot | throw "issue without prepare"
    check ((get current.issued ballot).isNone) "multiple issued images at ballot"
    check (seed.isPrefixOf history && history.length ≤ seed.length + 1) "does not extend recovery seed"
    check (current.sealed.all (· == history)) "extension after seal"
    let next ← remember current image history
    return { next with issued := (ballot, image) :: next.issued }
  | .accept group voter ballot image history => stepGroup state group fun current => do
    requireMember current voter
    let floor := (get current.floor voter).getD 0
    check (decide (AcceptAtPromise floor ballot)) "accept floor"
    let some (_, prepared) := get current.rounds ballot | throw "accept without prepare"
    check (prepared.contains voter && get current.issued ballot == some image) "accept without exact proposal"
    if let some previous := get current.latest voter then
      let old ← materialize current previous
      check (decide (RankLE old ⟨ballot, history⟩)) "accepted rank regressed"
      check (previous.1 != ballot || previous.2 == image) "different image at same ballot"
    let next ← remember current image history
    return recordVote next voter ballot image
  | .choice group ballot image voters => stepGroup state group fun current => do
    check (majorityCheck current.members voters) "chosen majority"
    check (voters.all (fun voter => current.voted.contains (voter, ballot, image))) "missing exact accept"
    check (get current.issued ballot == some image) "choice without exact proposal"
    let vote ← materialize current (ballot, image)
    for (older, history) in current.chosen do
      check (if older ≤ ballot then history.isPrefixOf vote.history else vote.history.isPrefixOf history)
        "chosen histories disagree"
    return { current with chosen := (ballot, vote.history) :: current.chosen }
  | .restart group voter floor report => stepGroup state group fun current => do
    requireMember current voter
    check ((get current.floor voter).getD 0 == floor && get current.latest voter == report)
      "restart lost selected media"
    return current
  | .seal source target base history => do
    check (source != target && (get state.groups target).isSome && base != 0) "invalid seal scope"
    check ((get state.transfers target).all (· == (base, history))) "conflicting transfer"
    let next ← stepGroup state source fun current => do
      check (current.chosen.any (fun (_, chosen) => chosen == history)) "seal lacks exact choice"
      check (current.chosen.all (fun (_, chosen) => chosen.isPrefixOf history)) "seal lost history"
      check (current.sealed.all (· == history)) "conflicting seal"
      return { current with sealed := some history }
    return { next with transfers := (target, base, history) :: next.transfers }
  | .install group voter ballot base image history => stepGroup state group fun current => do
    requireMember current voter
    let some transfer := get state.transfers group | throw "installation without predecessor seal"
    check (decide (ExactImage transfer (base, history))) "installation changed predecessor image"
    check (ballot == ballotRank 1 1 && (get current.floor voter).isNone) "invalid bootstrap"
    let next ← remember current image history
    return recordVote { next with floor := (voter, ballot) :: next.floor } voter ballot image

private def optionalReport (round nonce image : Nat) : Option Report :=
  if image == 0 then none else some (ballotRank round nonce, image)

private def parse (line : String) : Except String Event := do
  let op :: fields := (line.splitOn " ") | throw "empty event"
  let values ← fields.mapM fun field =>
    match field.toNat? with
    | some value => pure value
    | none => throw "invalid number"
  match op, values with
  | "roster", g :: members => return .roster g members
  | "promise", [g, v, r, n] => return .promise g v (ballotRank r n) none
  | "promise", [g, v, r, n, ar, an, i] => return .promise g v (ballotRank r n) (optionalReport ar an i)
  | "prepared", g :: r :: n :: wr :: wn :: i :: voters =>
    return .prepared g (ballotRank r n) (optionalReport wr wn i) voters
  | "issue", g :: r :: n :: i :: h => return .issue g (ballotRank r n) i h
  | "accept", g :: v :: r :: n :: i :: h => return .accept g v (ballotRank r n) i h
  | "choice", g :: r :: n :: i :: voters => return .choice g (ballotRank r n) i voters
  | "restart", [g, v, r, n] => return .restart g v (ballotRank r n) none
  | "restart", [g, v, r, n, ar, an, i] => return .restart g v (ballotRank r n) (optionalReport ar an i)
  | "seal", source :: target :: base :: h => return .seal source target base h
  | "install", g :: v :: r :: n :: base :: i :: h => return .install g v (ballotRank r n) base i h
  | _, _ => throw ("invalid event " ++ op)

def validate (trace : List String) : Except String Nat := do
  let mut state : TraceState := {}
  let mut line := 0
  for event in trace do
    line := line + 1
    state ← ((parse event).bind (step state)).mapError (fun reason => s!"line {line}: {reason}")
  return line

private def witness : List String := [
  "roster 1 1 2 3", "promise 1 1 1 1", "promise 1 2 1 1", "prepared 1 1 1 0 0 0 1 2",
  "issue 1 1 1 1 42", "accept 1 1 1 1 1 42", "accept 1 2 1 1 1 42", "choice 1 1 1 1 1 2",
  "promise 1 1 2 1 1 1 1"]

#eval validate witness
#guard (validate witness).toOption == some 9
#guard (validate (witness ++ ["accept 1 1 1 1 1 42"])) matches .error "line 10: accept floor"
#guard (validate (witness ++ ["choice 1 1 1 1 1 1"])) matches .error "line 10: chosen majority"

end Logkeeper.PrefixTrace
