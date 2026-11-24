import Logkeeper.StreamIO

/-! A reachable run of the stream I/O automaton. Epoch 1 creates and syncs two keepers and
appends a record that only the first keeper accepts. Epoch 2 elects both, installs the
inherited record on the first with a complete Sync and on the second with a staged Sync
followed by completion, certifies it, and publishes head 1 with an empty Append to a
keeper that holds no epoch-2 record. -/

namespace Logkeeper.StreamIOWitness

open PrefixAgreement StreamJournal StreamIO

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 8192

private def prior : History Nat := [⟨1, 7⟩]
private def first : Round Nat := ⟨1, 0, 1, by decide, fun _ => empty⟩
private def second : Round Nat :=
  ⟨2, 0, 1, by decide, fun k => if k = 0 then ⟨1, prior⟩ else ⟨1, []⟩⟩

theorem automaton_witness :
    ∃ s : State Nat, StreamIO.Reachable s ∧ (s.keeper 0).head = 1 ∧ Synced (s.keeper 0) 2 ∧
      Synced (s.keeper 1) 2 ∧ (s.keeper 0).history = prior ∧ (s.keeper 1).history = prior ∧
      s.writer.advertised prior ∧ Elected s.writer 2 2 ∧ (s.keeper 0).live ∧ (s.keeper 0).identity = 2 := by
  have c0 := (StreamIO.Reachable.initial (Payload := Nat)).call (k := 0) (i := 1) (req := .create) trivial rfl
  have c1 := c0.call (k := 1) (i := 1) (req := .create) trivial rfl
  have p0 := c1.call (k := 0) (i := 1) (req := .promise 1) (show 0 < 1 by decide) ⟨⟨rfl, rfl⟩, Or.inl (by decide)⟩
  have p1 := p0.call (k := 1) (i := 1) (req := .promise 1) (show 0 < 1 by decide) ⟨⟨rfl, rfl⟩, Or.inl (by decide)⟩
  have g0 := StreamIO.Reachable.extend p1 (Next.collectSeal (k := 0) (e := 1) (i := 1) (v := empty)
    (.tail _ (.tail _ (.head _))) rfl)
  have g1 := StreamIO.Reachable.extend g0 (Next.collectSeal (k := 1) (e := 1) (i := 1) (v := empty)
    (.head _) rfl)
  have e1 := StreamIO.Reachable.extend g1 (Next.choose (e := 1) (r := first) (by decide) rfl rfl rfl)
  -- Epoch 1 installs the empty seed on both keepers and appends one record on the first.
  have y0 := e1.call (k := 0) (i := 1) (req := .sync 1 1 1 [] 0)
    ⟨⟨first, rfl, rfl⟩, by decide, rfl, fun _ _ _ _ => rfl, by decide, rfl⟩
    ⟨⟨rfl, rfl⟩, rfl, rfl, by decide, by unfold SyncAdmitted; decide, by decide⟩
  have y1 := y0.call (k := 1) (i := 1) (req := .sync 1 1 1 [] 0)
    ⟨⟨first, rfl, rfl⟩, by decide, rfl, fun _ _ _ _ => rfl, by decide, rfl⟩
    ⟨⟨rfl, rfl⟩, rfl, rfl, by decide, by unfold SyncAdmitted; decide, by decide⟩
  have assigned := StreamIO.Reachable.extend y1 (Next.assign (e := 1) (payloads := [7]) (r := first) rfl)
  have i1 := StreamIO.Reachable.extend assigned (Next.issue (e := 1) (payloads := [7]) (rest := []) (r := first) rfl rfl)
  have a0 := i1.call (k := 0) (i := 1) (req := .append 1 1 [7] 0)
    ⟨⟨first, rfl, rfl⟩, by decide, rfl, by decide, rfl⟩
    ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, List.cons_ne_nil _ _, by decide⟩
  -- Epoch 2 elects both keepers. The first reports the accepted record.
  have q0 := a0.call (k := 0) (i := 2) (req := .promise 2) (show 0 < 2 by decide)
    ⟨⟨rfl, rfl⟩, Or.inl (by decide)⟩
  have q1 := q0.call (k := 1) (i := 2) (req := .promise 2) (show 0 < 2 by decide)
    ⟨⟨rfl, rfl⟩, Or.inl (by decide)⟩
  have h0 := StreamIO.Reachable.extend q1 (Next.collectSeal (k := 0) (e := 2) (i := 2)
    (v := ⟨1, prior⟩) (.tail _ (.tail _ (.head _))) rfl)
  have h1 := StreamIO.Reachable.extend h0 (Next.collectSeal (k := 1) (e := 2) (i := 2)
    (v := ⟨1, []⟩) (.head _) rfl)
  have e2 := StreamIO.Reachable.extend h1 (Next.choose (e := 2) (r := second) (by decide) rfl rfl rfl)
  -- The first keeper completes Sync directly; the second stages the inherited record first.
  have z0 := e2.call (k := 0) (i := 2) (req := .sync 2 1 2 [] 0)
    ⟨⟨second, rfl, rfl⟩, by decide, rfl, fun _ _ _ _ => rfl, by decide, rfl⟩
    ⟨⟨rfl, rfl⟩, rfl, rfl, by decide, by unfold SyncAdmitted; decide, by decide⟩
  have t1 := z0.call (k := 1) (i := 2) (req := .stage 2 1 1 prior)
    ⟨⟨second, rfl, rfl⟩, by decide, List.prefix_rfl, fun _ _ _ _ => rfl⟩
    ⟨⟨rfl, rfl⟩, rfl, rfl, by decide, by unfold SyncAdmitted; decide⟩
  have z1 := t1.call (k := 1) (i := 2) (req := .sync 2 1 2 [] 0)
    ⟨⟨second, rfl, rfl⟩, by decide, rfl, fun _ _ _ _ => rfl, by decide, rfl⟩
    ⟨⟨rfl, rfl⟩, rfl, rfl, by decide, by unfold SyncAdmitted; decide, by decide⟩
  have v0 := StreamIO.Reachable.extend z1 (Next.collectVote (k := 0) (e := 2) (h := prior)
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have v1 := StreamIO.Reachable.extend v0 (Next.collectVote (k := 1) (e := 2) (h := prior) (.head _))
  have cert := StreamIO.Reachable.extend v1 (Next.certify (e := 2) (h := prior) 0 1 (by decide) rfl rfl
    List.prefix_rfl List.prefix_rfl)
  -- The empty Append publishes the inherited head on a keeper with no epoch-2 record.
  have pub := cert.call (k := 0) (i := 2) (req := .publish 2 1)
    ⟨⟨second, rfl, rfl⟩, by decide, Or.inr rfl⟩
    ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, by decide⟩
  exact ⟨_, pub, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, Or.inr rfl,
    ⟨second, rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩

private theorem wire_append_at_empty {s : State Nat} (reached : StreamIO.Reachable s)
    (elected : Elected s.writer 1 1) (issued : s.writer.issued 1 = [])
    {payloads : List Nat} (assigned : (s.pending 1).payloads = payloads) (k : KeeperId) :
    WireSendable s k 1 (.append 1 1 payloads 0) := by
  have view : (extend s.writer 1 (s.pending 1).payloads).issued 1 = stamp 1 payloads := by
    simp [extend, issued, assigned]
  refine ⟨⟨elected, ?_, ?_, Nat.zero_le _, ?_⟩, Nat.zero_le _⟩
  · simp [view, stamp]
  · rw [view]
    change stamp 1 payloads = (stamp 1 payloads).take payloads.length
    have length : (stamp 1 payloads).length = payloads.length := by simp [stamp]
    rw [← length, List.take_length]
  · simpa [extend] using (reachable_inv reached).emptyAdvertised

private theorem reuse_after_capacity {before : State Nat} (reached : StreamIO.Reachable before)
    (assigned : (before.pending 1).payloads = [7, 8])
    (unanimous : ∀ k, (before.pending 1).refused k ≠ none)
    (certain : (before.pending 1).uncertainThrough ≤ (before.writer.issued 1).length)
    (elected : before.writer.round 1 = some first) (emptyIssued : before.writer.issued 1 = []) :
    ∃ after reused : State Nat, StreamIO.Reachable before ∧
      (before.pending 1).payloads = [7, 8] ∧ Next before (.discard 1) after ∧
      Next after (.assign 1 [9]) reused ∧ (reused.pending 1).payloads = [9] ∧
      reused.writer.issued 1 = [] ∧ (∀ k, WireSendable reused k 1 (.append 1 1 [9] 0)) := by
  let after := before.withPending 1 ((before.pending 1).reset [])
  let reused := after.withPending 1 ((after.pending 1).reset ((after.pending 1).payloads ++ [9]))
  have nonempty : (before.pending 1).payloads ≠ [] := by
    rw [assigned]
    exact List.cons_ne_nil _ _
  have discarded : Next before (.discard 1) after := .discard nonempty unanimous certain
  have reassigned : Next after (.assign 1 [9]) reused := .assign elected
  have bytes : (reused.pending 1).payloads = [9] := by
    simp [after, reused, State.withPending, Pending.reset]
  exact ⟨after, reused, reached, assigned, discarded, reassigned, bytes, emptyIssued,
    wire_append_at_empty ((reached.extend discarded).extend reassigned)
      ⟨first, elected, rfl⟩ emptyIssued bytes⟩

private def stateAt {s : State Nat} (_ : StreamIO.Reachable s) : State Nat := s

/-- A two-record suffix is released after three current capacity refusals. The next
    assignment reuses the first position with different bytes. -/
theorem capacity_reassignment_witness :
    ∃ sent before after reused : State Nat, StreamIO.Reachable sent ∧
      (∀ k, WireSendable sent k 1 (.append 1 1 [7, 8] 0)) ∧
      (∃ left right,
        Next sent (.rejectCapacity 1 0 1 .full) left ∧
        Next left (.rejectCapacity 1 1 1 .full) right ∧
        Next right (.rejectCapacity 1 2 1 .tooLarge) before) ∧
      StreamIO.Reachable before ∧ (before.pending 1).payloads = [7, 8] ∧
      Next before (.discard 1) after ∧ Next after (.assign 1 [9]) reused ∧
      (reused.pending 1).payloads = [9] ∧ reused.writer.issued 1 = [] ∧
      (∀ k, WireSendable reused k 1 (.append 1 1 [9] 0)) := by
  have c0 := (StreamIO.Reachable.initial (Payload := Nat)).call (k := 0) (i := 1) (req := .create) trivial rfl
  have c1 := c0.call (k := 1) (i := 1) (req := .create) trivial rfl
  have c2 := c1.call (k := 2) (i := 1) (req := .create) trivial rfl
  have p0 := c2.call (k := 0) (i := 1) (req := .promise 1) (show 0 < 1 by decide) ⟨⟨rfl, rfl⟩, Or.inl (by decide)⟩
  have p1 := p0.call (k := 1) (i := 1) (req := .promise 1) (show 0 < 1 by decide) ⟨⟨rfl, rfl⟩, Or.inl (by decide)⟩
  have p2 := p1.call (k := 2) (i := 1) (req := .promise 1) (show 0 < 1 by decide) ⟨⟨rfl, rfl⟩, Or.inl (by decide)⟩
  have g0 := StreamIO.Reachable.extend p2 (Next.collectSeal (k := 0) (e := 1) (i := 1) (v := empty)
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) rfl)
  have g1 := StreamIO.Reachable.extend g0 (Next.collectSeal (k := 1) (e := 1) (i := 1) (v := empty)
    (.tail _ (.tail _ (.head _))) rfl)
  have elected := StreamIO.Reachable.extend g1 (Next.choose (e := 1) (r := first) (by decide) rfl rfl rfl)
  have y0 := elected.call (k := 0) (i := 1) (req := .sync 1 1 1 [] 0)
    ⟨⟨first, rfl, rfl⟩, by decide, rfl, fun _ _ _ _ => rfl, by decide, rfl⟩
    ⟨⟨rfl, rfl⟩, rfl, rfl, by decide, by unfold SyncAdmitted; decide, by decide⟩
  have y1 := y0.call (k := 1) (i := 1) (req := .sync 1 1 1 [] 0)
    ⟨⟨first, rfl, rfl⟩, by decide, rfl, fun _ _ _ _ => rfl, by decide, rfl⟩
    ⟨⟨rfl, rfl⟩, rfl, rfl, by decide, by unfold SyncAdmitted; decide, by decide⟩
  have y2 := y1.call (k := 2) (i := 1) (req := .sync 1 1 1 [] 0)
    ⟨⟨first, rfl, rfl⟩, by decide, rfl, fun _ _ _ _ => rfl, by decide, rfl⟩
    ⟨⟨rfl, rfl⟩, rfl, rfl, by decide, by unfold SyncAdmitted; decide, by decide⟩
  have assigned := StreamIO.Reachable.extend y2 (Next.assign (e := 1) (payloads := [7, 8]) (r := first) rfl)
  have refusal0 := Next.rejectCapacity (s := stateAt assigned)
    (e := 1) (k := 0) (revision := 1) (reason := .full) (caller := 1) (payloads := [7, 8]) (head := 0)
    rfl ⟨first, rfl, rfl⟩ List.prefix_rfl ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, List.cons_ne_nil _ _, Nat.zero_le _⟩ rfl
  have denied0 := assigned.extend refusal0
  have refusal1 := Next.rejectCapacity (s := stateAt denied0)
    (e := 1) (k := 1) (revision := 1) (reason := .full) (caller := 1) (payloads := [7, 8]) (head := 0)
    rfl ⟨first, rfl, rfl⟩ List.prefix_rfl ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, List.cons_ne_nil _ _, Nat.zero_le _⟩ rfl
  have denied1 := denied0.extend refusal1
  have refusal2 := Next.rejectCapacity (s := stateAt denied1)
    (e := 1) (k := 2) (revision := 1) (reason := .tooLarge) (caller := 1) (payloads := [7, 8]) (head := 0)
    rfl ⟨first, rfl, rfl⟩ List.prefix_rfl ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, List.cons_ne_nil _ _, Nat.zero_le _⟩ rfl
  have denied2 := denied1.extend refusal2
  have result := reuse_after_capacity denied2 rfl (by
    intro k
    have bound := k.isLt
    have cases : k = 0 ∨ k = 1 ∨ k = 2 := by
      simp only [Fin.ext_iff]
      omega
    rcases cases with rfl | rfl | rfl <;> (simp only [stateAt]; decide)) (Nat.le_refl 0) rfl rfl
  obtain ⟨after, reused, facts⟩ := result
  exact ⟨_, _, after, reused, assigned, wire_append_at_empty assigned ⟨first, rfl, rfl⟩ rfl rfl,
    ⟨_, _, refusal0, refusal1, refusal2⟩, facts⟩

theorem capacity_discard_witness :
    ∃ before after reused : State Nat, StreamIO.Reachable before ∧
      (before.pending 1).payloads = [7, 8] ∧ Next before (.discard 1) after ∧
      Next after (.assign 1 [9]) reused ∧ (reused.pending 1).payloads = [9] ∧
      reused.writer.issued 1 = [] := by
  obtain ⟨_, before, after, reused, _, _, _, reach, pending, discarded, assigned, bytes, issued, _⟩ :=
    capacity_reassignment_witness
  exact ⟨before, after, reused, reach, pending, discarded, assigned, bytes, issued⟩

#print axioms automaton_witness
#print axioms capacity_reassignment_witness
#print axioms capacity_discard_witness

end Logkeeper.StreamIOWitness
