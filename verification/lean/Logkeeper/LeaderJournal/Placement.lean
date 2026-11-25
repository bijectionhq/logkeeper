import Logkeeper.LeaderJournal.Consensus

namespace Logkeeper.LeaderJournal.Placement

open JournalRefinement (Majority distinct_zone_configuration_has_majority_after_loss)

set_option warningAsError true

abbrev Domain := Nat

/-- Authentication and the declared (physically independent) failure domains
    are supplied by an immutable registry of keeper incarnations. -/
structure Registry where
  authenticated : KeeperId → Bool
  domain : KeeperId → Domain

structure Roster (registry : Registry) (members : List KeeperId) : Prop where
  three : members.length = 3
  distinct : members.Nodup
  authenticated : ∀ keeper ∈ members, registry.authenticated keeper = true
  independent : ∀ a ∈ members, ∀ b ∈ members, a ≠ b → registry.domain a ≠ registry.domain b

def Valid (registry : Registry) : Configuration → Prop
  | .stable members => Roster registry members
  | .joint oldMembers newMembers => Roster registry oldMembers ∧ Roster registry newMembers

theorem ack_pair_spans_domains {registry : Registry} {members : List KeeperId}
    (roster : Roster registry members) {a b : KeeperId} (inA : a ∈ members)
    (inB : b ∈ members) (different : a ≠ b) :
    registry.authenticated a = true ∧ registry.authenticated b = true ∧
      registry.domain a ≠ registry.domain b :=
  ⟨roster.authenticated a inA, roster.authenticated b inB, roster.independent a inA b inB different⟩

def survives (registry : Registry) (lost : Domain) (eligible : KeeperId → Bool) (keeper : KeeperId) :
    Bool :=
  decide (registry.domain keeper ≠ lost) && eligible keeper

theorem roster_survives_one_domain {registry : Registry} {members : List KeeperId}
    (roster : Roster registry members) (lost : Domain) (eligible : KeeperId → Bool)
    (otherwiseEligible : ∀ keeper ∈ members, registry.domain keeper ≠ lost → eligible keeper = true) :
    Majority members (survives registry lost eligible) := by
  have same :
      members.countP (survives registry lost eligible) =
        members.countP (fun keeper => decide (registry.domain keeper ≠ lost)) := by
    apply List.countP_congr
    intro keeper member
    simp only [survives, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨And.left, fun different => ⟨different, otherwiseEligible keeper member different⟩⟩
  unfold Majority
  rw [same]
  have length := roster.three
  match members with
  | a :: b :: c :: rest =>
    have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at length; omega)
    subst rest
    have distinct := roster.distinct
    simp [List.nodup_cons] at distinct
    exact distinct_zone_configuration_has_majority_after_loss registry.domain lost a b c
      (roster.independent a (by simp) b (by simp) distinct.1.1)
      (roster.independent a (by simp) c (by simp) distinct.1.2)
      (roster.independent b (by simp) c (by simp) distinct.2)
  | [] | [_] | [_, _] => simp at length

theorem configuration_survives_one_domain {registry : Registry} {configuration : Configuration}
    (valid : Valid registry configuration) (lost : Domain) (eligible : KeeperId → Bool)
    (otherwiseEligible : ∀ keeper, configuration.contains keeper = true →
      registry.domain keeper ≠ lost → eligible keeper = true) :
    configuration.quorum (survives registry lost eligible) := by
  cases configuration with
  | stable members =>
    exact roster_survives_one_domain valid lost eligible
      (fun keeper member => otherwiseEligible keeper (List.contains_iff_mem.mpr member))
  | joint oldMembers newMembers =>
    exact ⟨roster_survives_one_domain valid.1 lost eligible (fun keeper member =>
        otherwiseEligible keeper (by simp [Configuration.contains, member])),
      roster_survives_one_domain valid.2 lost eligible (fun keeper member =>
        otherwiseEligible keeper (by simp [Configuration.contains, member]))⟩

/-- The installation checks genesis and each roster newly put into use by the
    core. Unchanged rosters reuse the same registry evidence. -/
inductive Trace [DecidableEq Application] (registry : Registry) (members : List KeeperId) :
    State Application → Prop
  | initial : Roster registry members → Trace registry members (LeaderJournal.initial members)
  | next {before after} : Trace registry members before → LeaderJournal.Step before after →
      Valid registry after.effectiveConfiguration → Trace registry members after

theorem Trace.refines [DecidableEq Application] {registry : Registry} {members : List KeeperId}
    {s : State Application} (trace : Trace registry members s) : Reachable members s := by
  induction trace with
  | initial valid =>
    exact ⟨valid.distinct, fun empty => by have count := valid.three; simp [empty] at count, .nil _⟩
  | next _ step _ before =>
    exact ⟨before.1, before.2.1, .snoc before.2.2 step⟩

theorem Trace.configuration_valid [DecidableEq Application] {registry : Registry}
    {members : List KeeperId} {s : State Application} (trace : Trace registry members s) :
    Valid registry s.configuration ∧ Valid registry s.effectiveConfiguration := by
  induction trace with
  | initial valid => exact ⟨valid, valid⟩
  | next _ step effective before =>
    refine ⟨?_, effective⟩
    cases step with
    | commit _ _ _ _ _ _ configuration _ _ =>
      change Valid registry (configurationAt _ _) at effective ⊢
      rw [configuration]
      exact effective
    | _ => exact before.1

theorem deployed_quorum_after_domain_loss [DecidableEq Application] {registry : Registry}
    {members : List KeeperId} {s : State Application} (trace : Trace registry members s)
    (lost : Domain) (otherwiseEligible : ∀ keeper, s.configuration.contains keeper = true →
      registry.domain keeper ≠ lost → s.online keeper = true) :
    s.configuration.quorum (survives registry lost s.online) ∧
      s.responds (survives registry lost s.online) := by
  refine ⟨configuration_survives_one_domain trace.configuration_valid.1 lost s.online otherwiseEligible, ?_⟩
  intro keeper vote
  exact (Bool.and_eq_true_iff.mp vote).2

#print axioms ack_pair_spans_domains
#print axioms Trace.refines
#print axioms Trace.configuration_valid
#print axioms deployed_quorum_after_domain_loss

end Logkeeper.LeaderJournal.Placement
