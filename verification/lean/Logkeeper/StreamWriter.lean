import Logkeeper.StreamIO

namespace Logkeeper.StreamWriter

open PrefixAgreement StreamJournal StreamIO

set_option warningAsError true
set_option autoImplicit false

variable {Payload : Type}

/-- Each retained position names the issuing epoch's entire prefix through that position. -/
def Origins (w : Writer Payload) (history : History Payload) : Prop :=
  ∀ (i : Nat) (record : Record Payload), history[i]? = some record →
    i < (w.issued record.epoch).length ∧
      history.take (i + 1) = (w.issued record.epoch).take (i + 1)

theorem Origins.prefix {w : Writer Payload} {short long : History Payload}
    (origins : Origins w long) (included : short <+: long) : Origins w short := by
  intro i record atShort
  have bound := (List.getElem?_eq_some_iff.mp atShort).1
  obtain ⟨length, agreement⟩ := origins i record (by
    obtain ⟨suffix, rfl⟩ := included
    rwa [List.getElem?_append_left bound])
  exact ⟨length, (take_of_prefix included (by omega)).trans agreement⟩

theorem Origins.grows {w w' : Writer Payload} {history : History Payload}
    (origins : Origins w history) (grows : Grows w w') : Origins w' history := by
  intro i record found
  obtain ⟨bound, agreement⟩ := origins i record found
  exact ⟨Nat.lt_of_lt_of_le bound (grows.issued _).length_le,
    agreement.trans (take_of_prefix (grows.issued _) (by omega))⟩

theorem issued_origins {s : State Payload} (reached : StreamIO.Reachable s) :
    ∀ e, Origins s.writer (s.writer.issued e) := by
  induction reached with
  | initial => simp [Origins, State.initial]
  | @extend s action next reached step ih =>
      have inv := reachable_inv reached
      have grows := (next_inv inv step).2.2
      cases step with
      | @choose e r _ _ first second =>
          intro x
          by_cases same : x = e
          · subst x
            change Origins (elect s.writer e r) (if e = e then r.winner.history else s.writer.issued e)
            simp only [ite_true]
            have saved := seal_source_is_a_signer r
            have voted : (s.keeper r.source).durable.votes r.winner := by
              have report : (s.keeper r.source).durable.replies e = some (some r.winner) := by
                simp only [Round.sealed, decide_eq_true_eq] at saved
                unfold Round.winner
                rcases saved with selected | selected
                · rw [selected]
                  exact inv.seals e r.first r.identity _ first
                · rw [selected]
                  exact inv.seals e r.second r.identity _ second
              have sound := DurableAcceptor.reachable_replies_cover_every_lower_vote
                (reachable_keeper_refines_durable_acceptor (inv.reached r.source))
              exact (sound.repliesSound _ _ report).2.1 _ rfl |>.1
            have follows := vote_follows_writer (inv.reached r.source) inv.reserved
              (inv.unelected 0 inv.reserved) voted
            exact ((ih r.winner.ballot).prefix follows.2.2).grows grows
          · simpa [elect, same] using (ih x).grows grows
      | @issue e payloads r elected =>
          intro x
          by_cases same : x = e
          · subst x
            intro i record found
            by_cases prior : i < (s.writer.issued e).length
            · have before : (s.writer.issued e)[i]? = some record := by
                simpa [extend, List.getElem?_append_left prior] using found
              obtain ⟨bound, eq⟩ := (ih e).grows grows i record before
              exact ⟨bound, (take_of_prefix (grows.issued e) (by omega)).symm.trans eq⟩
            · have stampAt : (stamp e payloads)[i - (s.writer.issued e).length]? = some record := by
                simpa [extend, List.getElem?_append_right (Nat.le_of_not_gt prior)] using found
              have epoch : record.epoch = e := by
                simp only [stamp, List.getElem?_map] at stampAt
                cases h : payloads[i - (s.writer.issued e).length]? with
                | none => simp [h] at stampAt
                | some value =>
                    simp only [h, Option.map_some, Option.some.injEq] at stampAt
                    rw [← stampAt]
              rw [epoch]
              exact ⟨(List.getElem?_eq_some_iff.mp found).1, rfl⟩
          · simpa [extend, same] using (ih x).grows grows
      | certify => exact ih
      | send | deliver | refuse | drop | collectSeal | collectVote | restart => exact ih

theorem keeper_origins {s : State Payload} (reached : StreamIO.Reachable s) (k : KeeperId) :
    Origins s.writer (s.keeper k).history := by
  have inv := reachable_inv reached
  have follows := vote_follows_writer (inv.reached k) inv.reserved
    (inv.unelected 0 inv.reserved) (latest_voted (inv.reached k))
  exact (issued_origins reached _).prefix follows.2.2

theorem seed_origins {s : State Payload} (reached : StreamIO.Reachable s) (e : Nat) :
    Origins s.writer (s.writer.seed e) :=
  (issued_origins reached e).prefix ((reachable_inv reached).seeded e)

/-- Equal record epochs at the same LSN imply equality of the whole prefix, even across
    different current promises and synced epochs. -/
theorem same_epoch_agrees {w : Writer Payload} {left right : History Payload}
    (leftOrigins : Origins w left) (rightOrigins : Origins w right)
    {i : Nat} {a b : Record Payload} (leftAt : left[i]? = some a)
    (rightAt : right[i]? = some b) (same : a.epoch = b.epoch) :
    left.take (i + 1) = right.take (i + 1) := by
  rw [(leftOrigins i a leftAt).2, (rightOrigins i b rightAt).2, same]


def MatchesEpoch (observed : Option Nat) (expected : Nat) : Prop := observed = some expected

def SyncStart (floor head start : Nat) (matched : Bool) : Prop :=
  floor ≤ start ∧ head < start ∧ (floor = start ∨ matched = true)

def AppendHead (head last : Nat) : Nat := min head last

def AcceptedTail (tail issued last : Nat) : Nat := max (min tail issued) last

/-- Recovery selects the floor or verifies the record immediately below its first chunk. -/
theorem recovery_agrees {s : State Payload} (reached : StreamIO.Reachable s) (keeper : KeeperId)
    {epoch floor start : Nat} {matched : Bool}
    (unstaged : (s.keeper keeper).staging = none)
    (decision : SyncStart floor (s.keeper keeper).head start matched)
    (boundary : matched = true → ∃ target seed : Record Payload,
      1 < start ∧ (s.keeper keeper).history[start - 2]? = some target ∧
      (s.writer.seed epoch)[start - 2]? = some seed ∧ MatchesEpoch (some target.epoch) seed.epoch) :
    Agrees (s.keeper keeper) epoch (s.writer.seed epoch) floor start := by
  intro _ _ _ above
  rcases decision.2.2 with atFloor | matched
  · exact False.elim (above (by simpa [Keeper.syncFloor, unstaged] using atFloor.symm))
  · obtain ⟨target, seed, positive, targetAt, seedAt, equal⟩ := boundary matched
    have same : target.epoch = seed.epoch := Option.some.inj equal
    have agrees := same_epoch_agrees (keeper_origins reached keeper) (seed_origins reached epoch)
      targetAt seedAt same
    have offset : start - 2 + 1 = start - 1 := by omega
    simpa [Keeper.image, unstaged, offset] using agrees

/-- A fallback at the seed's record epoch supplies that exact record. -/
theorem recovery_record {w : Writer Payload} {left right : History Payload}
    (leftOrigins : Origins w left) (rightOrigins : Origins w right)
    {i : Nat} {a b : Record Payload} (leftAt : left[i]? = some a)
    (rightAt : right[i]? = some b) (same : MatchesEpoch (some a.epoch) b.epoch) :
    a = b := by
  have agrees := same_epoch_agrees leftOrigins rightOrigins leftAt rightAt (Option.some.inj same)
  have atPosition := congrArg (fun (h : History Payload) => h[i]?) agrees
  simpa [List.getElem?_take, leftAt, rightAt] using atPosition

theorem sendable_stage {w : Writer Payload} {keeper : Keeper Payload}
    {identity epoch floor start : Nat} {records : History Payload}
    (elected : Elected w epoch identity) (promised : epoch ≤ keeper.promised)
    (agrees : Agrees keeper epoch (w.seed epoch) floor start)
    (recordsFromSeed : records <+: (w.seed epoch).drop (start - 1)) :
    Sendable w keeper identity (.stage epoch floor start records) :=
  ⟨elected, promised, recordsFromSeed, agrees⟩

theorem sendable_sync {w : Writer Payload} {keeper : Keeper Payload}
    {identity epoch floor start head : Nat}
    (elected : Elected w epoch identity) (promised : epoch ≤ keeper.promised)
    (agrees : Agrees keeper epoch (w.seed epoch) floor start)
    (within : head ≤ (w.seed epoch).length)
    (certified : w.advertised ((w.seed epoch).take head)) :
    Sendable w keeper identity (.sync epoch floor start ((w.seed epoch).drop (start - 1)) head) :=
  ⟨elected, promised, rfl, agrees, within, certified⟩

/-- One lane's contiguous assigned run and certified publication yield a sendable Append. -/
theorem sendable_append {w : Writer Payload} {keeper : Keeper Payload}
    {identity epoch start head : Nat} {payloads : List Payload}
    (elected : Elected w epoch identity)
    (within : start - 1 + payloads.length ≤ (w.issued epoch).length)
    (assigned : stamp epoch payloads = ((w.issued epoch).drop (start - 1)).take payloads.length)
    (certified : w.advertised ((w.issued epoch).take (AppendHead head (start - 1 + payloads.length)))) :
    Sendable w keeper identity (.append epoch start payloads (AppendHead head (start - 1 + payloads.length))) :=
  ⟨elected, within, assigned, Nat.le_trans (Nat.min_le_right ..) within, certified⟩


/-- The next chunk uses the same keeper and remains bounded by the first head.
    A later snapshot can extend that prefix, and the assembled slice stays unchanged. -/
theorem assemble_read_chunk {first current : History Payload} {start copied count : Nat}
    (included : first <+: current) (within : start + copied + count ≤ first.length) :
    (first.drop start).take copied ++ (current.drop (start + copied)).take count =
      (first.drop start).take (copied + count) := by
  have fixed : (current.drop (start + copied)).take count =
      (first.drop (start + copied)).take count := by
    rw [List.take_drop, List.take_drop, take_of_prefix included within]
  rw [fixed, ← List.drop_drop, ← List.take_add]

/-- Two durable tombstones exclude any future live mutation quorum on this roster. -/
theorem delete_quorum_blocks_live_quorum {deleted live : KeeperId → Bool}
    (durable : JournalRefinement.Majority ensemble deleted)
    (terminal : ∀ k ∈ ensemble, deleted k = true → live k = false) :
    ¬ JournalRefinement.Majority ensemble live := by
  intro quorum
  obtain ⟨k, member, tombstoned, voting⟩ :=
    JournalRefinement.majorities_overlap ensemble deleted live durable quorum
  rw [terminal k member tombstoned] at voting
  contradiction

#print axioms assemble_read_chunk
#print axioms delete_quorum_blocks_live_quorum

#print axioms recovery_agrees
#print axioms recovery_record
#print axioms sendable_stage
#print axioms sendable_sync
#print axioms sendable_append

#print axioms issued_origins
#print axioms keeper_origins
#print axioms seed_origins
#print axioms same_epoch_agrees

end Logkeeper.StreamWriter
