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
    ∃ s : State Nat, StreamIO.Reachable s ∧ (s.keeper 0).head = 1 ∧ (s.keeper 0).synced = 2 ∧
      (s.keeper 0).history = prior ∧ (s.keeper 1).history = prior ∧ s.writer.advertised prior := by
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
    ⟨⟨first, rfl, rfl⟩, by decide, rfl, fun _ _ _ => rfl, by decide, rfl⟩
    ⟨⟨rfl, rfl⟩, rfl, rfl, by decide, by unfold SyncAdmitted; decide, by decide, by decide⟩
  have y1 := y0.call (k := 1) (i := 1) (req := .sync 1 1 1 [] 0)
    ⟨⟨first, rfl, rfl⟩, by decide, rfl, fun _ _ _ => rfl, by decide, rfl⟩
    ⟨⟨rfl, rfl⟩, rfl, rfl, by decide, by unfold SyncAdmitted; decide, by decide, by decide⟩
  have i1 := StreamIO.Reachable.extend y1 (Next.issue (e := 1) (payloads := [7]) (r := first) rfl)
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
    ⟨⟨second, rfl, rfl⟩, by decide, rfl, fun _ _ _ => rfl, by decide, rfl⟩
    ⟨⟨rfl, rfl⟩, rfl, rfl, by decide, by unfold SyncAdmitted; decide, by decide, by decide⟩
  have t1 := z0.call (k := 1) (i := 2) (req := .stage 2 1 1 prior)
    ⟨⟨second, rfl, rfl⟩, by decide, List.prefix_rfl, fun _ _ _ => rfl⟩
    ⟨⟨rfl, rfl⟩, rfl, rfl, by decide, by unfold SyncAdmitted; decide⟩
  have z1 := t1.call (k := 1) (i := 2) (req := .sync 2 1 2 [] 0)
    ⟨⟨second, rfl, rfl⟩, by decide, rfl, fun _ _ _ => rfl, by decide, rfl⟩
    ⟨⟨rfl, rfl⟩, rfl, rfl, by decide, by unfold SyncAdmitted; decide, by decide, by decide⟩
  have v0 := StreamIO.Reachable.extend z1 (Next.collectVote (k := 0) (e := 2) (h := prior)
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have v1 := StreamIO.Reachable.extend v0 (Next.collectVote (k := 1) (e := 2) (h := prior) (.head _))
  have cert := StreamIO.Reachable.extend v1 (Next.certify (e := 2) (h := prior) 0 1 (by decide) rfl rfl
    List.prefix_rfl List.prefix_rfl)
  -- The empty Append publishes the inherited head on a keeper with no epoch-2 record.
  have pub := cert.call (k := 0) (i := 2) (req := .publish 2 1)
    ⟨⟨second, rfl, rfl⟩, by decide, Or.inr rfl⟩
    ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, by decide⟩
  exact ⟨_, pub, rfl, rfl, rfl, rfl, Or.inr rfl⟩

#print axioms automaton_witness

end Logkeeper.StreamIOWitness
