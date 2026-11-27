import Logkeeper.JournalRefinement

/-!
Retirement on a certified placement proof (E4, `keeper/repair.rs`
`retire_removed` and `keeper/replicas.rs` `retire_copy`).

A copy that heard from no leader for the repair delay, or that a peer
excluded, asks another keeper for the stream's placement proof: the
committed configuration at a revision and, during a joint change, its
target. `decisions::certifies_exclusion` retires the copy only when the
proof is of the revision the copy was asked to leave and neither half names
the keeper; `retire_copy` also requires the copy's generation to be the one
the request named, so a copy staged again under a new generation stays.

`retired_copy_outside_every_quorum` and `retirement_keeps_every_quorum`
show that the retired copy is never counted by a quorum of the certified
configuration, stable or joint, so retiring it cannot remove a copy a
quorum needs. `retirement_refuses_other_revisions` and
`retirement_refuses_a_restaged_copy` cover the revision and generation
checks.
-/

namespace Logkeeper.ConsensusAdditions.RetireOnProof

open JournalRefinement (Majority)

set_option warningAsError true

abbrev KeeperId := Nat

inductive Configuration where
  | stable (members : List KeeperId)
  | joint (oldMembers newMembers : List KeeperId)
  deriving DecidableEq, Repr

def Configuration.contains : Configuration → KeeperId → Bool
  | .stable members, keeper => members.contains keeper
  | .joint oldMembers newMembers, keeper => oldMembers.contains keeper || newMembers.contains keeper

def Configuration.quorum : Configuration → (KeeperId → Bool) → Prop
  | .stable members, votes => Majority members votes
  | .joint oldMembers newMembers, votes => Majority oldMembers votes ∧ Majority newMembers votes

/-- The placement proof another keeper certifies. -/
structure Proof where
  revision : Nat
  voters : List KeeperId
  joint : Option (List KeeperId)

def Proof.configuration (proof : Proof) : Configuration :=
  match proof.joint with
  | none => .stable proof.voters
  | some target => .joint proof.voters target

/-- `decisions::certifies_exclusion`. -/
def certifiesExclusion (sameRevision namedVoter namedJoint : Bool) : Bool :=
  sameRevision && !namedVoter && !namedJoint

def retires (proof : Proof) (keeper : KeeperId) (revision : Nat) : Bool :=
  certifiesExclusion (proof.revision == revision) (proof.voters.contains keeper)
    (proof.joint.any (fun target => target.contains keeper))

theorem retired_copy_outside_every_quorum {proof : Proof} {keeper : KeeperId} {revision : Nat}
    (retired : retires proof keeper revision = true) :
    proof.configuration.contains keeper = false := by
  unfold retires certifiesExclusion at retired
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at retired
  obtain ⟨⟨_, voter⟩, joint⟩ := retired
  unfold Proof.configuration
  cases target : proof.joint with
  | none => simpa [Configuration.contains] using voter
  | some members =>
      rw [target] at joint
      simp only [Option.any_some] at joint
      simp only [Configuration.contains, voter, joint, Bool.or_self]

private theorem count_without {members : List KeeperId} {keeper : KeeperId}
    (outside : members.contains keeper = false) (votes : KeeperId → Bool) :
    members.countP (fun other => votes other && other != keeper) = members.countP votes := by
  induction members with
  | nil => rfl
  | cons head rest prior =>
      have different : head ≠ keeper := by
        intro same
        subst same
        simp at outside
      have restOutside : rest.contains keeper = false := by
        simp only [List.contains_cons, Bool.or_eq_false_iff] at outside
        exact outside.2
      simp only [List.countP_cons, prior restOutside]
      simp [different]

/-- Removing the retired copy's vote leaves every quorum of the certified
    configuration a quorum, and creates none. -/
theorem retirement_keeps_every_quorum {proof : Proof} {keeper : KeeperId} {revision : Nat}
    (retired : retires proof keeper revision = true) (votes : KeeperId → Bool) :
    proof.configuration.quorum (fun other => votes other && other != keeper) ↔
      proof.configuration.quorum votes := by
  have outside := retired_copy_outside_every_quorum retired
  cases configuration : proof.configuration with
  | stable members =>
      rw [configuration] at outside
      simp only [Configuration.contains] at outside
      simp only [Configuration.quorum, Majority, count_without outside]
  | joint oldMembers newMembers =>
      rw [configuration] at outside
      simp only [Configuration.contains, Bool.or_eq_false_iff] at outside
      simp only [Configuration.quorum, Majority, count_without outside.1, count_without outside.2]

theorem retirement_refuses_other_revisions {proof : Proof} {keeper : KeeperId} {revision : Nat}
    (other : proof.revision ≠ revision) : retires proof keeper revision = false := by
  simp [retires, certifiesExclusion, other]

/-- The local copy: its generation and whether it is detached. Staging a new
    copy of the stream on this keeper takes the next generation. -/
structure Copy where
  generation : Nat
  detached : Bool

def Copy.stage (copy : Copy) : Copy := ⟨copy.generation + 1, false⟩

/-- `retire_copy`: detach only the generation the request named, on a proof
    that certifies the exclusion. -/
def Copy.retire (copy : Copy) (generation : Nat) (proof : Proof) (keeper : KeeperId)
    (revision : Nat) : Copy :=
  if copy.generation = generation ∧ retires proof keeper revision = true then
    { copy with detached := true }
  else copy

theorem retirement_refuses_a_restaged_copy (copy : Copy) (proof : Proof) (keeper : KeeperId)
    (revision : Nat) :
    (copy.stage.retire copy.generation proof keeper revision).detached = false := by
  simp [Copy.stage, Copy.retire]

#print axioms retired_copy_outside_every_quorum
#print axioms retirement_keeps_every_quorum
#print axioms retirement_refuses_other_revisions
#print axioms retirement_refuses_a_restaged_copy

end Logkeeper.ConsensusAdditions.RetireOnProof
