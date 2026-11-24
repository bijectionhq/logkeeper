import Logkeeper.AsyncGroup

namespace Logkeeper.AsyncGroup.Witness

open AsyncPrefix PrefixAgreement DurableAcceptor PrefixTrace

set_option warningAsError true

private theorem update_self {f : Nat → α} {v : Nat} : update f v (f v) = f := by
  funext k
  by_cases atKey : k = v <;> simp [update, atKey]

private theorem update_to_current {f : Nat → α} {v : Nat} {x : α} (eq : f v = x) :
    update f v x = f := by
  rw [← eq]
  exact update_self

@[simp] private theorem update_twice {f : Nat → α} {v : Nat} {x y : α} :
    update (update f v x) v y = update f v y := by
  funext k
  by_cases atKey : k = v <;> simp [update, atKey]

private theorem finishFirst {s : State} (run : Reachable members s)
    (work : s.voters v = .first request todo) :
    Reachable members { s with voters := update s.voters v (.first request []) } := by
  induction todo generalizing s with
  | nil => simpa only [← work, update_self] using run
  | cons a rest ih =>
    have next := Reachable.extend run (Step.firstWrite v request a rest work)
    simpa [update] using ih next (by simp [update])

private theorem finishMirror {s : State} (run : Reachable members s)
    (work : s.voters v = .mirror reply todo) :
    Reachable members { s with voters := update s.voters v (.mirror reply []) } := by
  induction todo generalizing s with
  | nil => simpa only [← work, update_self] using run
  | cons a rest ih =>
    have next := Reachable.extend run (Step.mirrorEffect v reply a rest work)
    simpa [update] using ih next (by simp [update])

private theorem finishReopen {s : State} (run : Reachable members s)
    (work : s.voters v = .reopening candidate todo) :
    Reachable members { s with voters := update s.voters v (.reopening candidate []) } := by
  induction todo generalizing s with
  | nil => simpa only [← work, update_self] using run
  | cons a rest ih =>
    have next := Reachable.extend run (Step.reopenEffect v candidate a rest work)
    simpa [update] using ih next (by simp [update])

private theorem deliverLocal {s : State} {p : Packet}
    (run : Reachable members { s with net := Wire.begin p :: s.net }) :
    Reachable members { s with net := Wire.done p :: s.net } := by
  simpa using Reachable.extend run (Step.localDelivery p (by simp))

private def gather (s : State) (b v : Nat) (r : Round) : State :=
  { s.withRound b { r with promises := v :: r.promises } with
    core := { s.core with media := update s.core.media v (DurableAcceptor.promise (s.core.media v) b) } }

private theorem gather_reachable {s : State} (run : Reachable members s) {v b : Nat} {r : Round}
    (member : v ∈ members) (peer : v ∈ r.peers) (new : v ∉ r.promises)
    (round : s.rounds b = some r) (preparing : r.phase = .preparing)
    (ready : s.voters v = .ready) (later : (s.core.media v).promised < b)
    (below : (s.core.media v).latest.any (fun vote => b ≤ vote.ballot) = false) :
    Reachable members (gather s b v r) := by
  let request := Request.prepare b
  let reply := Packet.promise v b (s.core.media v).latest.isSome
  have nonzero : b ≠ 0 := by omega
  have admitted : PrepareAdmitted (s.core.media v).promised b := Nat.le_of_lt later
  have sent := deliverLocal (Reachable.extend run (Step.sendPrepare v b r round preparing peer))
  have started := Reachable.extend sent (Step.startJob v request (by simp [request]) ready
    ⟨member, nonzero, admitted⟩)
  have written := finishFirst started (v := v) (request := request) (todo := writeSlot) (by simp [update])
  have saved := Reachable.extend written
    (Step.firstSync v request _ _ _ (by simp [update]) (Save.promise b nonzero admitted))
  have mirrored := finishMirror saved (v := v) (reply := promisePacket v b (s.core.media v))
    (todo := writeSlot ++ [.fileSync]) (by simp [update])
  have acknowledged := Reachable.extend mirrored (Step.reply v (promisePacket v b (s.core.media v)) (by simp [update]))
  have locallyDelivered := Reachable.extend acknowledged
    (Step.localDelivery (promisePacket v b (s.core.media v)) (by simp))
  have matchReport : promisePacket v b (s.core.media v) = reply := by simp [promisePacket, below, reply]
  have strict : (s.core.media v).promised ≠ b := by omega
  have collected := Reachable.extend locallyDelivered
    (Step.collectPromise v b r (s.core.media v).latest round preparing peer new
      (by simp [update, prepareOrRetry, strict, DurableAcceptor.promise])
      (by simp [matchReport, reply]))
  simpa [gather, request, reply, matchReport, State.withRound, update, update_to_current ready,
    prepareOrRetry, strict] using collected

private def afterReopen (s : State) (b v : Nat) (p : Proposal) : State :=
  { s with core := { s.core with media := update s.core.media v (acceptVote (s.core.media v) ⟨b, p.history⟩) } }

private theorem accept_header_crash_and_reopen {s : State} (run : Reachable members s)
    {v b : Nat} {r : Round} {p : Proposal}
    (member : v ∈ members) (round : s.rounds b = some r) (accepting : r.phase = .accepting)
    (promised : v ∈ r.promises) (issued : s.core.issued b = some p)
    (ready : s.voters v = .ready) (floor : AcceptGuard (s.core.media v).promised b) :
    Reachable members (afterReopen s b v p) := by
  let request := Request.accept b p
  have sent := deliverLocal (Reachable.extend run (Step.sendAccept v b r p round accepting promised issued))
  have started := Reachable.extend sent (Step.startJob v request (by simp [request]) ready ⟨member, issued, floor⟩)
  have written := finishFirst started (v := v) (request := request) (todo := writeSlot) (by simp [update])
  have crashed := Reachable.extend written (Step.voterCrash v (by simp [update]) (by simp [update]))
  have reopening := Reachable.extend crashed (Step.beginRestart v (some request)
    (by simp [update, crashCandidate]))
  have checked := finishReopen reopening (v := v) (candidate := some request) (todo := reopen) (by simp [update])
  have selected := Reachable.extend checked
    (Step.reopenCandidate v request _ _ _ (by simp [update]) (Save.accept b p issued floor))
  simpa [afterReopen, request, update, update_to_current ready] using selected

private def countVote (s : State) (b v : Nat) (r : Round) (p : Proposal) : State :=
  { (afterReopen s b v p).withRound b { r with votes := v :: r.votes } with net := s.net }

private theorem vote_reachable {s : State} (run : Reachable members s)
    {v b : Nat} {r : Round} {p : Proposal}
    (member : v ∈ members) (round : s.rounds b = some r) (accepting : r.phase = .accepting)
    (promised : v ∈ r.promises) (new : v ∉ r.votes) (issued : s.core.issued b = some p)
    (ready : s.voters v = .ready) (floor : AcceptGuard (s.core.media v).promised b) :
    Reachable members (countVote s b v r p) := by
  let request := Request.accept b p
  let reply := Packet.vote v b p.image p.readBack true
  let effects := writeSlot ++ [.fileSync] ++ if p.readBack then readSlot ++ readSlot else []
  have sent := deliverLocal (Reachable.extend run (Step.sendAccept v b r p round accepting promised issued))
  have started := Reachable.extend sent (Step.startJob v request (by simp [request]) ready ⟨member, issued, floor⟩)
  have written := finishFirst started (v := v) (request := request) (todo := writeSlot) (by simp [update])
  have saved := Reachable.extend written
    (Step.firstSync v request _ reply effects (by simp [update]) (Save.accept b p issued floor))
  have mirrored := finishMirror saved (v := v) (reply := reply) (todo := effects) (by simp [update])
  have acknowledged := Reachable.extend mirrored (Step.reply v reply (by simp [update]))
  have delivered := Reachable.extend acknowledged (Step.localDelivery reply (by simp))
  have counted := Reachable.extend delivered
    (Step.collectVote v b r p reply round accepting promised new issued rfl (by simp))
  simpa [countVote, afterReopen, request, State.withRound, update_to_current ready] using counted

private def reachedState {s : State} (_ : Reachable members s) : State := s

private def roster : List Nat := [1, 2, 3]
private def first : Round := ⟨.choose, [1, 2], .preparing, [], []⟩
private def second : Round := ⟨.recover, [1, 3], .preparing, [], []⟩
private def emptyPrep : Preparation := ⟨[2, 1], fun _ => none, none⟩
private def value : Proposal := ⟨10, [42], false⟩
private def recovered : Preparation := ⟨[3, 1], fun v => if v = 1 then some ⟨1, [42]⟩ else none,
  some ⟨1, [42]⟩⟩

theorem restart_mid_accept_then_replacement_recovers_minority :
    ∃ (afterCrash afterReplacement : State), Reachable roster afterCrash ∧
      Reachable roster afterReplacement ∧ Chosen (abstractLedger roster afterReplacement) 2 [42] ∧
      (afterCrash.core.media 1).latest = some ⟨1, [42]⟩ ∧
      (afterCrash.core.media 2).latest = none ∧ (afterCrash.core.media 3).latest = none ∧
      afterCrash.net = [] ∧ afterReplacement.core.prepared 2 = some recovered := by
  have emptyRun : Reachable roster State.initial := .initial (by decide)
  have started := Reachable.extend emptyRun (Step.start 1 first rfl (by decide) rfl (by unfold ExactQuorum; decide))
  have one := gather_reachable started (v := 1) (b := 1) (r := first)
    (by decide) (by decide) (by decide) rfl rfl rfl (by decide) rfl
  let onePromise : Round := { first with promises := [1] }
  have two := gather_reachable one (v := 2) (b := 1) (r := onePromise)
    (by decide) (by decide) (by decide) rfl rfl rfl (by decide) rfl
  let twoPromises : Round := { first with promises := [2, 1] }
  have prepared := Reachable.extend two (Step.prepared 1 twoPromises emptyPrep
    rfl rfl rfl rfl (by unfold ExactQuorum; decide)
    (by intro v member; simp [emptyPrep] at member; rcases member with rfl | rfl <;> rfl)
    (RecoveryFold.push (RecoveryFold.push .empty rfl) rfl)
    (by simp [emptyPrep]))
  let issuing := { twoPromises with phase := Phase.prepared }
  have issued := Reachable.extend prepared (Step.issue 1 issuing emptyPrep value
    rfl rfl rfl rfl ⟨List.nil_prefix, by decide⟩ (by simp [issuing, twoPromises, first]) (by decide) (by intro; rfl))
  let accepting := { twoPromises with phase := Phase.accepting }
  have crash := accept_header_crash_and_reopen issued (v := 1) (b := 1) (r := accepting) (p := value)
    (by decide) rfl rfl (by decide) rfl rfl (by unfold AcceptGuard AcceptAtPromise; exact ⟨by decide, rfl⟩)
  have replacement := Reachable.extend crash (Step.replace 1 2 accepting second
    rfl rfl (by decide) rfl (by unfold ExactQuorum; decide))
  have firstReport := gather_reachable replacement (v := 1) (b := 2) (r := second)
    (by decide) (by decide) (by decide) rfl rfl rfl (by decide) rfl
  let firstReply := { second with promises := [1] }
  have secondReport := gather_reachable firstReport (v := 3) (b := 2) (r := firstReply)
    (by decide) (by decide) (by decide) rfl rfl rfl (by decide) rfl
  let both := { second with promises := [3, 1] }
  have selected := Reachable.extend secondReport (Step.prepared 2 both recovered
    rfl rfl rfl rfl (by unfold ExactQuorum; decide)
    (by intro v member; simp [recovered] at member; rcases member with rfl | rfl <;> rfl)
    (RecoveryFold.push (RecoveryFold.push .empty rfl) rfl)
    (by
      intro v member vote reported
      simp [recovered] at member
      rcases member with rfl | rfl <;> simp [recovered] at reported
      subst vote
      decide))
  let recovering := { both with phase := Phase.prepared }
  have readyToConfirm := Reachable.extend selected (Step.issue 2 recovering recovered value
    rfl rfl rfl rfl ⟨List.prefix_rfl, by decide⟩ (by intro; rfl) (by decide) (by intro; rfl))
  let confirming := { both with phase := Phase.accepting }
  have firstVote := vote_reachable readyToConfirm (v := 1) (b := 2) (r := confirming) (p := value)
    (by decide) rfl rfl (by decide) (by decide) rfl rfl ⟨by decide, rfl⟩
  let oneVote := { confirming with votes := [1] }
  have secondVote := vote_reachable firstVote (v := 3) (b := 2) (r := oneVote) (p := value)
    (by decide) rfl rfl (by decide) (by decide) rfl rfl ⟨by decide, rfl⟩
  let counted := { confirming with votes := [3, 1] }
  have certificate := Step.certificate (members := roster) 2 counted value
    (s := reachedState secondVote)
    rfl rfl rfl (by unfold ExactQuorum; decide)
  have completed := Reachable.extend secondVote certificate
  exact ⟨_, _, crash, completed, exact_certificate_is_chosen secondVote certificate,
    rfl, rfl, rfl, rfl, rfl⟩

#print axioms restart_mid_accept_then_replacement_recovers_minority

end Logkeeper.AsyncGroup.Witness
