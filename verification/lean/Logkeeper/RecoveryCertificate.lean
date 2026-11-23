/-
A recovery certificate over opaque application dependencies.

Logkeeper orders opaque records. The application supplies its dependency
keys and an independently stated read relation for a selection. The journal
publishes a certificate only when its enumeration equals those reads and every
enumerated key has an exact held physical version that survives each credible
fault. Study 110 of the Logkeeper design is the source of this interface.
-/

namespace Logkeeper.RecoveryCertificate

structure PhysicalVersion where
  providerNamespace : Nat
  path : Nat
  generation : Nat
  deriving DecidableEq

structure Scope where
  lineage : Nat
  orderedCut : Nat
  plan : Nat
  deriving DecidableEq

structure Grant (Key : Type) where
  scope : Scope
  key : Key
  physical : PhysicalVersion
  deriving DecidableEq

def Binds {Key : Type} (scope : Scope) (key : Key) (physical : PhysicalVersion) (grant : Grant Key) : Prop :=
  grant.scope = scope ∧ grant.key = key ∧ grant.physical = physical

theorem a_grant_binds_the_containing_physical_generation {Key : Type}
    (scope : Scope) (key : Key) (physical : PhysicalVersion) (grant : Grant Key)
    (bound : Binds scope key physical grant) :
    grant.physical = physical :=
  bound.2.2

theorem relocated_members_need_custody_of_their_new_physical_version {Key : Type}
    (scope : Scope) (key : Key) (original replacement : PhysicalVersion) (grant : Grant Key)
    (different : replacement ≠ original)
    (granted : Binds scope key original grant) :
    ¬ Binds scope key replacement grant := by
  intro substituted
  exact different ((a_grant_binds_the_containing_physical_generation scope key replacement grant substituted).symm.trans
    (a_grant_binds_the_containing_physical_generation scope key original grant granted))

theorem two_members_of_one_pack_cannot_prove_independent_domains {Key Zone : Type}
    (zoneOf : PhysicalVersion → Zone) (first second : Grant Key)
    (pack : first.physical = second.physical) :
    zoneOf first.physical = zoneOf second.physical :=
  congrArg zoneOf pack

/-- The application's dependency enumeration and its independent read relation. -/
structure Dependencies (Selection Key : Type) where
  keys : Selection → List Key
  reads : Selection → Key → Prop
  exact : ∀ selected key, key ∈ keys selected ↔ reads selected key

/-- Every enumerated key has an exact held version that survives each credible fault. -/
def Ready {Selection Key Failure : Type} (dependencies : Dependencies Selection Key)
    (survives : PhysicalVersion → Failure → Prop)
    (inventory : Key → PhysicalVersion → Prop) (grants : Grant Key → Prop)
    (scope : Scope) (selected : Selection) (credible : Failure → Prop) : Prop :=
  ∀ key ∈ dependencies.keys selected, ∀ fault, credible fault →
    ∃ physical, inventory key physical ∧ survives physical fault ∧
      ∃ grant, grants grant ∧ Binds scope key physical grant

theorem every_application_read_has_exact_held_coverage {Selection Key Failure : Type}
    (dependencies : Dependencies Selection Key) (survives : PhysicalVersion → Failure → Prop)
    (inventory : Key → PhysicalVersion → Prop) (grants : Grant Key → Prop)
    (scope : Scope) (selected : Selection) (credible : Failure → Prop)
    (ready : Ready dependencies survives inventory grants scope selected credible)
    (key : Key) (reads : dependencies.reads selected key) (fault : Failure) (allowed : credible fault) :
    ∃ physical, inventory key physical ∧ survives physical fault ∧
      ∃ grant, grants grant ∧ Binds scope key physical grant :=
  ready key ((dependencies.exact selected key).mpr reads) fault allowed

/-- One-AZ placement refines the per-failure provider contract. -/
def ZoneReady {Selection Key Zone : Type} (dependencies : Dependencies Selection Key)
    (zoneOf : PhysicalVersion → Zone)
    (inventory : Key → PhysicalVersion → Prop) (grants : Grant Key → Prop)
    (scope : Scope) (selected : Selection) (credible : Zone → Prop) : Prop :=
  ∀ key ∈ dependencies.keys selected, ∀ lost, credible lost →
    ∃ zone, zone ≠ lost ∧ ∃ physical, inventory key physical ∧ zoneOf physical = zone ∧
      ∃ grant, grants grant ∧ Binds scope key physical grant

theorem zone_placement_refines_the_provider_contract {Selection Key Zone : Type}
    (dependencies : Dependencies Selection Key) (zoneOf : PhysicalVersion → Zone)
    (inventory : Key → PhysicalVersion → Prop) (grants : Grant Key → Prop)
    (scope : Scope) (selected : Selection) (credible : Zone → Prop)
    (ready : ZoneReady dependencies zoneOf inventory grants scope selected credible) :
    Ready dependencies (fun version lost => zoneOf version ≠ lost) inventory grants scope selected credible := by
  intro key listed lost allowed
  obtain ⟨zone, survives, physical, present, placed, granted⟩ := ready key listed lost allowed
  exact ⟨physical, present, fun same => survives (placed.symm.trans same), granted⟩

/-- A certificate whose enumeration only over-approximates the reads still covers them. -/
theorem a_superset_enumeration_still_covers_every_read {Selection Key Failure : Type}
    (keys : Selection → List Key) (reads : Selection → Key → Prop)
    (covers : ∀ selected key, reads selected key → key ∈ keys selected)
    (survives : PhysicalVersion → Failure → Prop)
    (inventory : Key → PhysicalVersion → Prop) (grants : Grant Key → Prop)
    (scope : Scope) (selected : Selection) (credible : Failure → Prop)
    (ready : ∀ key ∈ keys selected, ∀ fault, credible fault →
      ∃ physical, inventory key physical ∧ survives physical fault ∧
        ∃ grant, grants grant ∧ Binds scope key physical grant)
    (key : Key) (read : reads selected key) (fault : Failure) (allowed : credible fault) :
    ∃ physical, inventory key physical ∧ survives physical fault ∧
      ∃ grant, grants grant ∧ Binds scope key physical grant :=
  ready key (covers selected key read) fault allowed

#print axioms a_grant_binds_the_containing_physical_generation
#print axioms relocated_members_need_custody_of_their_new_physical_version
#print axioms two_members_of_one_pack_cannot_prove_independent_domains
#print axioms every_application_read_has_exact_held_coverage
#print axioms zone_placement_refines_the_provider_contract
#print axioms a_superset_enumeration_still_covers_every_read

end Logkeeper.RecoveryCertificate
