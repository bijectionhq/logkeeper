import Logkeeper.DurableAcceptor

namespace Logkeeper.StreamJournal

open PrefixAgreement
open JournalRefinement (Majority majorities_overlap)

set_option warningAsError true

abbrev KeeperId := Fin 3
def ensemble : List KeeperId := [0, 1, 2]

structure Record (Payload : Type) where
  epoch : Nat
  payload : Payload
  deriving DecidableEq

abbrev History (Payload : Type) := List (Record Payload)

def empty : Vote (Record Payload) := ⟨0, []⟩
def boot : DurableAcceptor.State (Record Payload) :=
  DurableAcceptor.acceptVote DurableAcceptor.initial empty

theorem boot_reachable : DurableAcceptor.Reachable (boot : DurableAcceptor.State (Record Payload)) :=
  .extend .initial (.accept empty (Nat.le_refl 0) (by simp [DurableAcceptor.initial]))

structure Keeper (Payload : Type) where
  durable : DurableAcceptor.State (Record Payload)
  identity : Nat
  created : Bool
  deleted : Bool
  head : Nat
  floor : Nat
  /-- An incomplete Sync's floor and history. Only a complete Sync makes them visible. -/
  staging : Option (Nat × History Payload)

def initial : Keeper Payload := ⟨boot, 0, false, false, 0, 1, none⟩

def Keeper.promised (k : Keeper Payload) : Nat := k.durable.promised
def Keeper.latest (k : Keeper Payload) : Vote (Record Payload) := k.durable.latest.getD empty
def Keeper.synced (k : Keeper Payload) : Nat := k.latest.ballot
def Keeper.history (k : Keeper Payload) : History Payload := k.latest.history
def Keeper.tail (k : Keeper Payload) : Nat := k.history.length
def Keeper.live (k : Keeper Payload) : Prop := k.created = true ∧ k.deleted = false

def SealAllowed (k : Keeper Payload) (epoch identity : Nat) : Prop :=
  k.promised < epoch ∨ (k.promised = epoch ∧ k.identity = identity)

def Synced (k : Keeper Payload) (epoch : Nat) : Prop :=
  k.promised = epoch ∧ k.synced = epoch

def MayAppend (k : Keeper Payload) (epoch : Nat) : Prop := Synced k epoch

def MayTrim (k : Keeper Payload) (epoch through : Nat) : Prop :=
  Synced k epoch ∧ through ≤ k.head

def SameCommitted (k : Keeper Payload) (history : History Payload) : Prop :=
  k.head ≤ history.length ∧ history.take k.head = k.history.take k.head

/-- The history an incomplete Sync builds on: the staged history, or else the visible one. -/
def Keeper.image (k : Keeper Payload) : History Payload := (k.staging.map Prod.snd).getD k.history

/-- A staged floor persists until the Sync completes. -/
def Keeper.syncFloor (k : Keeper Payload) (floor : Nat) : Nat :=
  (k.staging.map fun staged => max staged.1 floor).getD floor

/-- A transfer replaces the image from `start`. A start at the floor can skip trimmed positions,
    whose ghost records come from the writer's seed. -/
def syncImage (k : Keeper Payload) (seed : History Payload) (floor start : Nat)
    (records : History Payload) : History Payload :=
  (if start = k.syncFloor floor then seed.take (start - 1) else k.image.take (start - 1)) ++ records

/-- The keeper-side admission of a Sync chunk, shared by incomplete and complete chunks. -/
def SyncAdmitted (k : Keeper Payload) (floor start : Nat) : Prop :=
  0 < k.syncFloor floor ∧ k.syncFloor floor ≤ start ∧ k.floor ≤ start ∧ k.head < start ∧
    (start ≤ k.image.length + 1 ∨ start = k.syncFloor floor)

def sealKeeper (k : Keeper Payload) (epoch identity : Nat) : Keeper Payload :=
  if k.promised = epoch then k
  else { k with durable := DurableAcceptor.promise k.durable epoch, identity, staging := none }

def accept (k : Keeper Payload) (epoch : Nat) (history : History Payload) : Keeper Payload :=
  { k with durable := DurableAcceptor.acceptVote k.durable ⟨epoch, history⟩, staging := none }

def deleteKeeper (k : Keeper Payload) (deleting : Bool) : Keeper Payload :=
  if deleting then { k with deleted := true } else k

structure Round (Payload : Type) where
  identity : Nat
  first : KeeperId
  second : KeeperId
  distinct : first ≠ second
  report : KeeperId → Vote (Record Payload)

def Round.sealed (r : Round Payload) (k : KeeperId) : Bool :=
  decide (k = r.first ∨ k = r.second)

def recoveryEpoch (vote : Vote (Record Payload)) : Nat := vote.ballot

def RecoveryLE (left right : Vote (Record Payload)) : Prop :=
  recoveryEpoch left ≤ recoveryEpoch right ∧
  (recoveryEpoch left = recoveryEpoch right → left.history.length ≤ right.history.length)

instance (left right : Vote (Record Payload)) : Decidable (RecoveryLE left right) :=
  inferInstanceAs (Decidable (_ ≤ _ ∧ (_ = _ → _ ≤ _)))

theorem recovery_rank_is_synced_then_tail (left right : Vote (Record Payload)) :
    RecoveryLE left right ↔ RankLE left right := by
  rfl -- recovery key

def Round.source (r : Round Payload) : KeeperId :=
  if RecoveryLE (r.report r.first) (r.report r.second) then r.second else r.first

def Round.winner (r : Round Payload) : Vote (Record Payload) := r.report r.source

structure Writer (Payload : Type) where
  round : Nat → Option (Round Payload)
  issued : Nat → History Payload
  advertised : History Payload → Prop

def Writer.seed (w : Writer Payload) (epoch : Nat) : History Payload :=
  ((w.round epoch).map Round.winner).elim [] Vote.history

def Writer.owns (w : Writer Payload) (k : Keeper Payload) (epoch : Nat) : Prop :=
  ∃ r, w.round epoch = some r ∧ r.identity = k.identity

def stamp (epoch : Nat) (payloads : List Payload) : History Payload :=
  payloads.map (Record.mk epoch)

/-- One step per durable keeper effect of the shipped rules. Writer-side premises
    (`owns`, the seed and `advertised`) are discharged by the I/O automaton. -/
inductive Step (w : Writer Payload) : Keeper Payload → Keeper Payload → Prop
  | create {k} : k.deleted = false → Step w k { k with created := true }
  | sealKeeper {k epoch identity} : k.live → SealAllowed k epoch identity →
      Step w k (sealKeeper k epoch identity)
  | syncPart {k epoch floor start records} : k.live → k.promised = epoch → w.owns k epoch →
      k.synced ≠ epoch → SyncAdmitted k floor start →
      Step w k { k with staging := some (k.syncFloor floor,
        syncImage k (w.seed epoch) floor start records) }
  | sync {k epoch floor start records head} : k.live → k.promised = epoch → w.owns k epoch →
      SyncAdmitted k floor start →
      syncImage k (w.seed epoch) floor start records = w.seed epoch →
      (k.synced = epoch → k.history = w.seed epoch) → w.seed epoch <+: w.issued epoch →
      k.head ≤ head → head ≤ (w.seed epoch).length → k.syncFloor floor ≤ head + 1 →
      w.advertised ((w.seed epoch).take head) →
      Step w k { accept k epoch (w.seed epoch) with
        head, floor := max k.floor (k.syncFloor floor) }
  | installFloor {k epoch head} : k.live → MayAppend k epoch → w.owns k epoch →
      k.floor ≤ head → w.seed epoch <+: k.history → k.history <+: w.issued epoch →
      head ≤ (w.issued epoch).length → w.advertised ((w.issued epoch).take head) →
      Step w k { accept k epoch ((w.issued epoch).take (max k.tail head)) with
        head := max k.head head, floor := head + 1 }
  | append {k epoch payloads head} : k.live → MayAppend k epoch → w.owns k epoch →
      payloads ≠ [] → w.seed epoch <+: k.history →
      k.history ++ stamp epoch payloads <+: w.issued epoch →
      head ≤ k.tail + payloads.length →
      w.advertised ((k.history ++ stamp epoch payloads).take head) →
      Step w k { accept k epoch (k.history ++ stamp epoch payloads) with head := max k.head head }
  /-- An empty Append or an identical retained retry publishes a head within the tail. -/
  | publish {k epoch head} : k.live → MayAppend k epoch → w.owns k epoch →
      head ≤ k.tail → w.advertised (k.history.take head) →
      Step w k { k with head := max k.head head }
  | trim {k epoch through} : k.live → w.owns k epoch → MayTrim k epoch through →
      Step w k { k with floor := max k.floor (through + 1) }
  | check {k} : k.live → Step w k k
  | read {k} : k.live → Step w k k
  | delete {k} : Step w k (deleteKeeper k true)

inductive Reachable (w : Writer Payload) : Keeper Payload → Prop
  | initial : Reachable w initial
  | extend : Reachable w k → Step w k next → Reachable w next

theorem append_requires_sync {k : Keeper Payload} {epoch : Nat}
    (admitted : MayAppend k epoch) : k.synced = epoch := by
  exact admitted.2 -- synced guard

theorem seal_tie_has_same_identity {k : Keeper Payload} {epoch identity : Nat}
    (admitted : SealAllowed k epoch identity) (same : k.promised = epoch) :
    k.identity = identity := by
  rcases admitted with higher | tied
  · omega
  · exact tied.2 -- identity guard

theorem trim_below_head {k : Keeper Payload} {epoch through : Nat}
    (admitted : MayTrim k epoch through) : through ≤ k.head := by
  exact admitted.2 -- trim guard

private theorem accept_extension_is_durable_step {k : Keeper Payload} {epoch : Nat}
    {history : History Payload} (promised : k.promised = epoch) (synced : k.synced = epoch)
    (longer : k.history.length ≤ history.length) :
    DurableAcceptor.Step k.durable (DurableAcceptor.acceptVote k.durable ⟨epoch, history⟩) := by
  refine .accept _ (Nat.le_of_eq promised) ?_
  intro old latest
  have key : old = k.latest := by simp [Keeper.latest, latest]
  have ballot := (show old.ballot = k.synced from congrArg Vote.ballot key)
  have length := (show old.history.length = k.tail from congrArg (·.history.length) key)
  exact ⟨Nat.le_of_eq (ballot.trans synced), fun _ => length ▸ longer⟩

theorem keeper_step_refines_durable_acceptor {w : Writer Payload} {k next : Keeper Payload}
    (sound : DurableAcceptor.Sound k.durable) (step : Step w k next) : DurableAcceptor.Step k.durable next.durable := by
  cases step with
  | sealKeeper _ allowed =>
      unfold sealKeeper
      split
      · exact .restart
      · rename_i differs
        rcases allowed with higher | tied
        · exact .prepare _ higher
        · exact (differs tied.1).elim
  | sync _ promised _ _ _ same _ _ _ _ _ =>
      refine .accept _ (Nat.le_of_eq promised) ?_
      intro old latest
      have key : old = k.latest := by simp [Keeper.latest, latest]
      have ballot := (show old.ballot = k.synced from congrArg Vote.ballot key)
      have history := (show old.history = k.history from congrArg Vote.history key)
      refine ⟨?_, ?_⟩
      · exact Nat.le_trans (sound.latestRecorded old latest).2 (Nat.le_of_eq promised)
      · intro equal
        simp [history, same (ballot.symm.trans equal)]
  | installFloor _ admitted _ _ _ issued _ _ =>
      refine accept_extension_is_durable_step admitted.1 (append_requires_sync admitted) ?_
      simp only [List.length_take]
      exact Nat.le_min_of_le_of_le (Nat.le_max_left _ _) issued.length_le
  | append _ admitted _ _ _ _ _ _ =>
      exact accept_extension_is_durable_step admitted.1 (append_requires_sync admitted) (by simp)
  | _ => exact .restart

theorem reachable_keeper_refines_durable_acceptor {w : Writer Payload} {k : Keeper Payload}
    (reached : Reachable w k) : DurableAcceptor.Reachable k.durable := by
  induction reached with
  | initial => exact boot_reachable
  | extend _ step prior =>
      exact .extend prior (keeper_step_refines_durable_acceptor
        (DurableAcceptor.reachable_replies_cover_every_lower_vote prior) step)

theorem keeper_bounds {w : Writer Payload} {k : Keeper Payload} (reached : Reachable w k) :
    k.head ≤ k.tail ∧ 1 ≤ k.floor ∧ k.floor ≤ k.head + 1 := by
  induction reached with
  | initial => exact ⟨Nat.zero_le _, Nat.le_refl _, Nat.le_refl _⟩
  | @extend before _ _ step ih =>
      cases step with
      | sealKeeper _ _ =>
          unfold sealKeeper
          split <;> exact ih
      | @sync epoch floor _ _ head _ _ _ admitted _ _ _ raises within covered _ =>
          change head ≤ (w.seed epoch).length ∧ 1 ≤ max before.floor (before.syncFloor floor) ∧
            max before.floor (before.syncFloor floor) ≤ head + 1
          refine ⟨within, Nat.le_trans ih.2.1 (Nat.le_max_left _ _), ?_⟩
          exact Nat.max_le_of_le_of_le (Nat.le_trans ih.2.2 (Nat.add_le_add_right raises 1)) covered
      | @installFloor epoch head _ _ _ _ _ issued _ _ =>
          change max before.head head ≤ ((w.issued epoch).take (max before.tail head)).length ∧
            1 ≤ head + 1 ∧ head + 1 ≤ max before.head head + 1
          simp only [List.length_take]
          have long : before.tail ≤ (w.issued epoch).length := issued.length_le
          refine ⟨?_, by omega, by omega⟩
          have := ih.1
          omega
      | @append epoch payloads head _ _ _ _ _ _ bounded _ =>
          change max before.head head ≤ (before.history ++ stamp epoch payloads).length ∧
            1 ≤ before.floor ∧ before.floor ≤ max before.head head + 1
          simp only [List.length_append, stamp, List.length_map]
          have := ih.1
          have := ih.2.2
          refine ⟨?_, ih.2.1, by omega⟩
          change max before.head head ≤ before.tail + payloads.length
          omega
      | publish _ _ _ bounded _ =>
          exact ⟨Nat.max_le_of_le_of_le ih.1 bounded, ih.2.1,
            Nat.le_trans ih.2.2 (Nat.add_le_add_right (Nat.le_max_left _ _) 1)⟩
      | trim _ _ bounded =>
          exact ⟨ih.1, Nat.le_trans ih.2.1 (Nat.le_max_left _ _),
            Nat.max_le_of_le_of_le ih.2.2 (Nat.add_le_add_right (trim_below_head bounded) 1)⟩
      | delete =>
          unfold deleteKeeper
          exact ih
      | _ => exact ih

theorem two_of_three_is_majority (a b : KeeperId) (distinct : a ≠ b) :
    Majority ensemble (fun k => decide (k = a ∨ k = b)) := by
  exact (by decide : ∀ a b : KeeperId, a ≠ b →
    Majority ensemble (fun k => decide (k = a ∨ k = b))) a b distinct

theorem seal_source_is_a_signer (r : Round Payload) : r.sealed r.source = true := by
  unfold Round.source
  split <;> simp [Round.sealed]

theorem seal_winner_dominates (r : Round Payload) (k : KeeperId) (signed : r.sealed k = true) :
    RankLE (r.report k) r.winner := by
  have comparable : ¬ RankLE (r.report r.first) (r.report r.second) →
      RankLE (r.report r.second) (r.report r.first) := by
    unfold RankLE
    omega
  simp only [Round.sealed, decide_eq_true_eq] at signed
  unfold Round.winner Round.source
  split
  · rename_i ranked
    rcases signed with rfl | rfl
    · exact (recovery_rank_is_synced_then_tail _ _).mp ranked
    · exact rank_refl _
  · rename_i ranked
    rcases signed with rfl | rfl
    · exact rank_refl _
    · exact comparable (fun le => ranked ((recovery_rank_is_synced_then_tail _ _).mpr le))

def Covers (vote : Vote (Record Payload)) (epoch : Nat) (history : History Payload) : Prop :=
  vote.ballot = epoch ∧ history <+: vote.history

def QuorumAccepted (keepers : KeeperId → Keeper Payload) (epoch : Nat)
    (history : History Payload) : Prop :=
  ∃ ack, Majority ensemble ack ∧
    ∀ k ∈ ensemble, ack k = true →
      ∃ held, (keepers k).durable.votes ⟨epoch, held⟩ ∧ history <+: held

/-- A completed election records the first durable Seal snapshots from its two signers.
    The retry of an already elected identity does not replace a snapshot. -/
structure Execution (Payload : Type) where
  writer : Writer Payload
  keeper : KeeperId → Keeper Payload
  reached : ∀ k, Reachable writer (keeper k)
  reserved : writer.round 0 = none
  initiallyEmpty : writer.issued 0 = []
  emptyAdvertised : writer.advertised []
  advertisedChosen : ∀ history, writer.advertised history →
    ∃ epoch, QuorumAccepted keeper epoch history
  captured : ∀ epoch r, writer.round epoch = some r → ∀ k, r.sealed k = true →
    (keeper k).durable.replies epoch = some (some (r.report k))

def Execution.ledger (x : Execution Payload) : Ledger KeeperId (Record Payload) where
  members := ensemble
  active epoch := epoch = 0 ∨ (x.writer.round epoch).isSome = true
  prepared epoch k := if epoch = 0 then true else (x.writer.round epoch).elim false (·.sealed k)
  report epoch k := (x.writer.round epoch).map (·.report k)
  selected epoch := (x.writer.round epoch).map Round.winner
  issued := x.writer.issued
  voted k := (x.keeper k).durable.votes

theorem vote_follows_writer {w : Writer Payload} {k : Keeper Payload}
    (reached : Reachable w k) (reserved : w.round 0 = none) (initiallyEmpty : w.issued 0 = [])
    {vote : Vote (Record Payload)} (voted : k.durable.votes vote) :
    (vote.ballot = 0 ∨ (w.round vote.ballot).isSome = true) ∧
      w.seed vote.ballot <+: vote.history ∧ vote.history <+: w.issued vote.ballot := by
  induction reached with
  | initial =>
      have eq : vote = empty := by simpa [initial, boot, DurableAcceptor.acceptVote,
        DurableAcceptor.initial] using voted
      subst vote
      simp [empty, Writer.seed, reserved, initiallyEmpty]
  | extend _ step ih =>
      cases step with
      | sealKeeper _ _ =>
          apply ih
          unfold sealKeeper at voted
          split at voted <;> exact voted
      | sync _ _ owns _ _ _ issued _ _ _ _ =>
          rcases voted with prior | rfl
          · exact ih prior
          · obtain ⟨r, elected, _⟩ := owns
            exact ⟨Or.inr (by simp [elected]), List.prefix_rfl, issued⟩
      | installFloor _ _ owns _ seed history _ _ =>
          rcases voted with prior | rfl
          · exact ih prior
          · obtain ⟨r, elected, _⟩ := owns
            refine ⟨Or.inr (by simp [elected]), seed.trans ?_, List.take_prefix _ _⟩
            exact List.prefix_take_iff.mpr ⟨history, Nat.le_max_left _ _⟩
      | append _ _ owns _ seed issued _ _ =>
          rcases voted with prior | rfl
          · exact ih prior
          · obtain ⟨r, elected, _⟩ := owns
            exact ⟨Or.inr (by simp [elected]), seed.trans (by simp), issued⟩
      | delete =>
          apply ih
          unfold deleteKeeper at voted
          exact voted
      | _ => exact ih voted

private theorem captured_vote {x : Execution Payload} {epoch : Nat} {r : Round Payload}
    (elected : x.writer.round epoch = some r) {k : KeeperId} (signs : r.sealed k = true) :
    (x.keeper k).durable.votes (r.report k) ∧ (r.report k).ballot < epoch := by
  have sound := DurableAcceptor.reachable_replies_cover_every_lower_vote
    (reachable_keeper_refines_durable_acceptor (x.reached k))
  exact (sound.repliesSound epoch _ (x.captured epoch r elected k signs)).2.1 _ rfl

theorem execution_refines_prefix_agreement (x : Execution Payload) : Rules x.ledger := by
  constructor
  · constructor
    · intro epoch active
      change epoch = 0 ∨ (x.writer.round epoch).isSome = true at active
      rcases active with rfl | active
      · change Majority ensemble (fun _ => true)
        decide
      · cases elected : x.writer.round epoch with
        | none => simp [elected] at active
        | some r =>
            have positive : epoch ≠ 0 := by
              intro zero
              subst epoch
              simp [x.reserved] at elected
            simpa [Execution.ledger, positive, elected, Round.sealed] using
              two_of_three_is_majority r.first r.second r.distinct
    · intro epoch k observed _ _ prepared reported
      cases elected : x.writer.round epoch with
      | none => simp [Execution.ledger, elected] at reported
      | some r =>
          have positive : epoch ≠ 0 := by
            intro zero
            subst epoch
            simp [x.reserved] at elected
          have signs : r.sealed k = true := by simpa [Execution.ledger, positive, elected] using prepared
          have exactReport : r.report k = observed := by simpa [Execution.ledger, elected] using reported
          have source := seal_source_is_a_signer r
          have faithful := captured_vote (x := x) elected source
          refine ⟨r.source, r.winner, ?_, ?_, ?_, ?_, faithful.1, faithful.2, ?_⟩
          · change r.source ∈ ensemble
            have all : ∀ i : KeeperId, i ∈ ensemble := by decide
            exact all _
          · simpa [Execution.ledger, positive, elected] using source
          · simp [Execution.ledger, elected, Round.winner]
          · simp [Execution.ledger, elected]
          · exact exactReport ▸ seal_winner_dominates r k signs
    · intro k vote voted
      exact vote_follows_writer (x.reached k) x.reserved x.initiallyEmpty voted
  · intro epoch k _ prepared vote voted lower
    have positive : epoch ≠ 0 := by omega
    cases elected : x.writer.round epoch with
    | none => simp [Execution.ledger, positive, elected] at prepared
    | some r =>
        have signs : r.sealed k = true := by simpa [Execution.ledger, positive, elected] using prepared
        have sound := DurableAcceptor.reachable_replies_cover_every_lower_vote
          (reachable_keeper_refines_durable_acceptor (x.reached k))
        obtain ⟨observed, exactReport, ranked⟩ :=
          (sound.repliesSound epoch _ (x.captured epoch r elected k signs)).2.2 vote voted lower
        exact ⟨observed, by simpa [Execution.ledger, elected] using exactReport, ranked⟩

/-- An acknowledgement is a durable accept of a prefix at the writer's epoch.
    Delivery can be lost without retracting the accept. -/
def Acknowledged (x : Execution Payload) (epoch : Nat) (history : History Payload) : Prop :=
  QuorumAccepted x.keeper epoch history

theorem quorum_acknowledgements_choose (x : Execution Payload) {epoch : Nat} {history : History Payload}
    (acks : Acknowledged x epoch history) : Chosen x.ledger epoch history := by
  obtain ⟨ack, majority, held⟩ := acks
  exact ⟨ack, majority, fun k member voted =>
    let ⟨h, hs, contains⟩ := held k member voted
    ⟨⟨epoch, h⟩, hs, rfl, contains⟩⟩

/-- The logical cut stores a ghost prefix. Physical retention starts at floor. -/
def retained (history : History Payload) (floor : Nat) := history.drop (floor - 1)

theorem committed_contiguous_and_irrevocable (x : Execution Payload)
    {oldEpoch epoch floor : Nat} {old current : History Payload}
    (oldCut : Chosen x.ledger oldEpoch old) (currentCut : Chosen x.ledger epoch current)
    (grows : old.length ≤ current.length) :
    (retained current floor).length = current.length + 1 - max floor 1 ∧
    retained old floor <+: retained current floor := by
  have agrees := every_chosen_prefix_agrees (execution_refines_prefix_agreement x) oldCut currentCut
  have prefixes : old <+: current := by
    rcases agrees with forward | reverse
    · exact forward
    · exact (reverse.eq_of_length_le grows) ▸ List.prefix_rfl
  constructor
  · simp only [retained, List.length_drop]
    omega
  · obtain ⟨tail, rfl⟩ := prefixes
    unfold retained
    by_cases fits : floor - 1 ≤ old.length
    · rw [List.drop_append_of_le_length fits]
      exact ⟨tail, rfl⟩
    · simp [List.drop_eq_nil_of_le (by omega : old.length ≤ floor - 1)]

theorem seal_fences_and_covers_acknowledged_appends (x : Execution Payload)
    {oldEpoch epoch : Nat} {history : History Payload} {r : Round Payload}
    (elected : x.writer.round epoch = some r) (lower : oldEpoch < epoch)
    (oldAck : Acknowledged x oldEpoch history) :
    history <+: r.winner.history := by
  have active : x.ledger.active epoch := Or.inr (by simp [elected])
  have inherited := later_ballot_inherits_chosen_prefix (execution_refines_prefix_agreement x)
    (quorum_acknowledgements_choose x oldAck) epoch lower active
  simpa [PrefixAgreement.seed, Execution.ledger, elected] using inherited

theorem late_lower_epoch_cannot_extend_after_seal (x : Execution Payload)
    {oldEpoch epoch head : Nat} {r : Round Payload} {history : History Payload}
    (elected : x.writer.round epoch = some r) (lower : oldEpoch < epoch)
    (sealReturned : r.winner.history.length ≤ head)
    (lateAck : Acknowledged x oldEpoch history) :
    history.length ≤ head :=
  Nat.le_trans (seal_fences_and_covers_acknowledged_appends x elected lower lateAck).length_le sealReturned

theorem take_of_prefix {short long : History Payload} {n : Nat}
    (prefixed : short <+: long) (within : n ≤ short.length) : short.take n = long.take n := by
  obtain ⟨rest, rfl⟩ := prefixed
  exact (List.take_append_of_le_length within).symm

theorem keeper_head_was_advertised {w : Writer Payload} {k : Keeper Payload}
    (emptyAdvertised : w.advertised []) (reached : Reachable w k) :
    w.advertised (k.history.take k.head) := by
  induction reached with
  | initial => exact emptyAdvertised
  | @extend before _ prior step ih =>
      cases step with
      | sealKeeper _ _ =>
          unfold sealKeeper
          split <;> exact ih
      | sync _ _ _ _ _ _ _ _ _ _ advertised => exact advertised
      | @installFloor epoch head _ _ _ _ _ history _ advertised =>
          change w.advertised (((w.issued epoch).take (max before.tail head)).take (max before.head head))
          rw [List.take_take]
          by_cases newer : before.head ≤ head
          · rw [Nat.max_eq_right newer, Nat.min_eq_left (Nat.le_max_right _ _)]
            exact advertised
          · have bounded := (keeper_bounds prior).1
            rw [Nat.max_eq_left (by omega), Nat.min_eq_left (by omega),
              ← take_of_prefix history bounded]
            exact ih
      | @append epoch payloads head _ _ _ _ _ _ _ advertised =>
          change w.advertised ((before.history ++ stamp epoch payloads).take (max before.head head))
          by_cases newer : before.head ≤ head
          · rw [Nat.max_eq_right newer]
            exact advertised
          · rw [Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge newer)),
                List.take_append_of_le_length (keeper_bounds prior).1]
            exact ih
      | @publish _ head _ _ _ _ advertised =>
          change w.advertised (before.history.take (max before.head head))
          by_cases newer : before.head ≤ head
          · rw [Nat.max_eq_right newer]
            exact advertised
          · rw [Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge newer))]
            exact ih
      | delete =>
          unfold deleteKeeper
          exact ih
      | _ => exact ih

theorem reachable_keeper_head_is_chosen (x : Execution Payload) (k : KeeperId) :
    let view := x.keeper k
    ∃ epoch, Chosen x.ledger epoch (view.history.take view.head) := by
  obtain ⟨epoch, certified⟩ := x.advertisedChosen _
    (keeper_head_was_advertised x.emptyAdvertised (x.reached k))
  exact ⟨epoch, quorum_acknowledgements_choose x certified⟩

structure Page (Payload : Type) where
  floor : Nat
  head : Nat
  records : History Payload

def readPage (k : Keeper Payload) (start maxRecords : Nat) : Option (Page Payload) :=
  if start < k.floor then none
  else some ⟨k.floor, k.head, ((k.history.take k.head).drop (start - 1)).take maxRecords⟩

/-- A single keeper's retained floor suffices, even when another keeper has trimmed further. -/
theorem read_returns_exact_committed_records (x : Execution Payload)
    (keeper : KeeperId) {epoch start maxRecords : Nat} {current : History Payload}
    (committed : Chosen x.ledger epoch current) (known : (x.keeper keeper).head ≤ current.length)
    (retainedFrom : (x.keeper keeper).floor ≤ start) :
    let k := x.keeper keeper
    readPage k start maxRecords = some
      ⟨k.floor, k.head, ((current.take k.head).drop (start - 1)).take maxRecords⟩ := by
  let k := x.keeper keeper
  have bounded := (keeper_bounds (x.reached keeper)).1
  obtain ⟨e, certified⟩ := reachable_keeper_head_is_chosen x keeper
  have length : (k.history.take k.head).length = k.head := by
    simp [Nat.min_eq_left (show k.head ≤ k.history.length from bounded)]
  have agrees := every_chosen_prefix_agrees (execution_refines_prefix_agreement x) certified committed
  have retainedCut : k.history.take k.head <+: current := by
    rcases agrees with forward | backward
    · exact forward
    · exact (backward.eq_of_length_le (length.symm ▸ known)) ▸ List.prefix_rfl
  have cut : current.take k.head = k.history.take k.head := by
    obtain ⟨tail, exactCut⟩ := retainedCut
    exact exactCut ▸ List.take_left' length
  change readPage k start maxRecords = some
    ⟨k.floor, k.head, ((current.take k.head).drop (start - 1)).take maxRecords⟩
  rw [cut]
  unfold readPage
  exact ite_eq_right (Nat.not_lt_of_ge retainedFrom) -- read uses head

inductive AppendResult where
  | append | retry | conflict | trimmed | fenced
  deriving DecidableEq

def appendAt [DecidableEq Payload] (history : History Payload) (floor identity epoch caller request lsn : Nat)
    (payload : Payload) : AppendResult :=
  if request ≠ epoch ∨ caller ≠ identity then .fenced
  else if lsn < floor then .trimmed
  else if lsn = history.length + 1 then .append
  else if history[lsn - 1]? = some ⟨request, payload⟩ then .retry
  else .conflict

theorem append_is_conditional_and_idempotent [DecidableEq Payload] (history : History Payload)
    {floor identity epoch caller request lsn : Nat} {payload : Payload} :
    (appendAt history floor identity epoch caller request lsn payload = .append ↔
      request = epoch ∧ caller = identity ∧ floor ≤ lsn ∧ lsn = history.length + 1) ∧
    (appendAt history floor identity epoch caller request lsn payload = .retry ↔
      request = epoch ∧ caller = identity ∧ floor ≤ lsn ∧
      history[lsn - 1]? = some ⟨request, payload⟩) := by
  have noNext : lsn = history.length + 1 → history[lsn - 1]? ≠ some ⟨request, payload⟩ := by
    intro equal
    simp [equal]
  unfold appendAt
  by_cases e : request = epoch <;> by_cases h : caller = identity <;>
    by_cases f : lsn < floor <;> by_cases n : lsn = history.length + 1 <;>
    by_cases r : history[lsn - 1]? = some ⟨request, payload⟩ <;>
    simp_all [Nat.not_lt, Nat.not_lt_of_ge]


structure CheckView where
  promised : Nat
  synced : Nat
  tail : Nat
  head : Nat

def check (k : Keeper Payload) : CheckView := ⟨k.promised, k.synced, k.tail, k.head⟩

structure Invocation where
  started : Nat
  replied : Nat

structure CheckRound where
  epoch : Nat
  opened : Nat
  answered : KeeperId → Bool
  sampled : KeeperId → Nat
  view : KeeperId → CheckView

def Fresh (call : Invocation) (round : CheckRound) : Prop :=
  call.started ≤ round.opened

structure Confirmed (call : Invocation) (round : CheckRound) : Prop where
  fresh : Fresh call round
  beforeReply : round.opened ≤ call.replied
  quorum : Majority ensemble round.answered
  samples : ∀ k ∈ ensemble, round.answered k = true →
    round.opened ≤ round.sampled k ∧ round.sampled k ≤ call.replied ∧
      (round.view k).promised = round.epoch ∧ (round.view k).synced = round.epoch

theorem confirmed_round_is_fresh {call : Invocation} {round : CheckRound}
    (confirmed : Confirmed call round) : call.started ≤ round.opened := by
  exact confirmed.fresh -- fresh round guard

/-- The head cuts of a logical record-by-record execution. Times are event indices. -/
structure HeadTrace where
  headAt : Nat → Nat
  monotone : ∀ earlier later, earlier ≤ later → headAt earlier ≤ headAt later
  unit : ∀ time, headAt (time + 1) ≤ headAt time + 1

/-- Study 29's read-index cut argument, specialized to LSNs. -/
private theorem commit_cut_in_window (trace : HeadTrace) {first last result : Nat}
    (ordered : first ≤ last) (lower : trace.headAt first ≤ result)
    (upper : result ≤ trace.headAt last) :
    ∃ point, first ≤ point ∧ point ≤ last ∧ trace.headAt point = result := by
  induction last with
  | zero =>
      have equal : first = 0 := by omega
      subst first
      exact ⟨0, Nat.le_refl _, Nat.le_refl _, Nat.le_antisymm lower upper⟩
  | succ previous prior =>
      by_cases earlier : first ≤ previous ∧ result ≤ trace.headAt previous
      · obtain ⟨point, within, before, cut⟩ := prior earlier.1 earlier.2
        exact ⟨point, within, Nat.le_trans before (Nat.le_succ _), cut⟩
      · refine ⟨previous + 1, ordered, Nat.le_refl _, ?_⟩
        have unit := trace.unit previous
        rcases Nat.lt_or_ge previous first with after | before
        · have atEnd : first = previous + 1 := by omega
          subst first
          omega
        · have tooShort : trace.headAt previous < result := by omega
          omega

/-- A ready writer has installed the opening cut on a quorum at its epoch.
    That prefix remains present at later eligible checks in the same epoch. -/
def OpeningCut (trace : HeadTrace) (round : CheckRound) : Prop :=
  ∃ copies, Majority ensemble copies ∧
    ∀ k ∈ ensemble, copies k = true → round.answered k = true →
      trace.headAt round.opened ≤ (round.view k).tail

/-- Keeper timelines use protocol steps or idle events. Check replies name their
    exact event, and the opening head has a durable ballot-specific quorum. -/
structure KeeperTrace (writer : Writer Payload) where
  image : Nat → KeeperId → Keeper Payload
  reached : ∀ time keeper, Reachable writer (image time keeper)
  next : ∀ time keeper, Step writer (image time keeper) (image (time + 1) keeper) ∨
    image time keeper = image (time + 1) keeper

theorem durable_step_preserves_vote {before after : DurableAcceptor.State (Record Payload)}
    (step : DurableAcceptor.Step before after) {vote : Vote (Record Payload)}
    (voted : before.votes vote) : after.votes vote := by
  cases step with
  | accept => exact Or.inl voted
  | prepare => exact voted
  | restart => exact voted

private theorem votes_persist {writer : Writer Payload} (stores : KeeperTrace writer)
    {first last : Nat} {k : KeeperId} {vote : Vote (Record Payload)}
    (ordered : first ≤ last) (voted : (stores.image first k).durable.votes vote) :
    (stores.image last k).durable.votes vote := by
  induction last with
  | zero =>
      have equal : first = 0 := by omega
      exact equal ▸ voted
  | succ previous prior =>
      by_cases before : first ≤ previous
      · have previousVote := prior before
        rcases stores.next previous k with step | idle
        · have sound := DurableAcceptor.reachable_replies_cover_every_lower_vote
            (reachable_keeper_refines_durable_acceptor (stores.reached previous k))
          exact durable_step_preserves_vote (keeper_step_refines_durable_acceptor sound step) previousVote
        · exact idle ▸ previousVote
      · have equal : first = previous + 1 := by omega
        exact equal ▸ voted

theorem opening_cut_from_durable_copies {writer : Writer Payload} (stores : KeeperTrace writer)
    (trace : HeadTrace) {call : Invocation} {round : CheckRound}
    (confirmed : Confirmed call round)
    (observes : ∀ k ∈ ensemble, round.answered k = true →
      round.view k = check (stores.image (round.sampled k) k))
    (openingQuorum : ∃ copies, Majority ensemble copies ∧
      ∀ k ∈ ensemble, copies k = true → ∃ held : History Payload,
        (stores.image round.opened k).durable.votes ⟨round.epoch, held⟩ ∧
        trace.headAt round.opened ≤ held.length) :
    OpeningCut trace round := by
  obtain ⟨copies, quorum, basis⟩ := openingQuorum
  refine ⟨copies, quorum, ?_⟩
  intro k member copy answered
  obtain ⟨held, voted, openingEnd⟩ := basis k member copy
  obtain ⟨afterOpen, _, _, synced⟩ := confirmed.samples k member answered
  let sample := stores.image (round.sampled k) k
  have exactView := observes k member answered
  have persists := votes_persist stores afterOpen voted
  have sound := DurableAcceptor.reachable_replies_cover_every_lower_vote
    (reachable_keeper_refines_durable_acceptor (stores.reached (round.sampled k) k))
  obtain ⟨observed, saved, ranked⟩ := sound.dominates _ persists
  have latest : sample.latest = observed := by simp [sample, Keeper.latest, saved]
  have same : round.epoch = observed.ballot := by
    rw [exactView] at synced
    change sample.latest.ballot = round.epoch at synced
    rw [latest] at synced
    exact synced.symm
  rw [exactView]
  change trace.headAt round.opened ≤ sample.latest.history.length
  rw [latest]
  exact Nat.le_trans openingEnd (ranked.2 same)

def SamplesCovered (round : CheckRound) (lsn : Nat) : Prop :=
  ∀ k ∈ ensemble, round.answered k = true → (round.view k).tail ≤ lsn

theorem head_linearizable (trace : HeadTrace) {call : Invocation} {round : CheckRound}
    {result priorAck : Nat} (confirmed : Confirmed call round)
    (durable : OpeningCut trace round) (covers : SamplesCovered round result)
    (chosen : result ≤ trace.headAt call.replied)
    (acknowledged : priorAck ≤ trace.headAt call.started) :
    priorAck ≤ result ∧ ∃ point,
      call.started ≤ point ∧ point ≤ call.replied ∧ trace.headAt point = result := by
  obtain ⟨copies, enough, installed⟩ := durable
  obtain ⟨k, member, copy, answered⟩ :=
    majorities_overlap ensemble copies round.answered enough confirmed.quorum
  have lower := Nat.le_trans (installed k member copy answered) (covers k member answered)
  have fresh := confirmed_round_is_fresh confirmed
  obtain ⟨point, afterOpen, beforeReply, exactCut⟩ :=
    commit_cut_in_window trace confirmed.beforeReply lower chosen
  exact ⟨Nat.le_trans (Nat.le_trans acknowledged (trace.monotone _ _ fresh)) lower,
    point, Nat.le_trans fresh afterOpen, beforeReply, exactCut⟩

theorem non_writer_head_linearizable (trace : HeadTrace)
    {call : Invocation} {round : CheckRound} {result priorAck : Nat}
    (confirmed : Confirmed call round) (durable : OpeningCut trace round)
    (maximum : SamplesCovered round result)
    (commitQuorum : Majority ensemble (fun k => round.answered k && decide (result ≤ (round.view k).head)))
    (sound : ∀ k ∈ ensemble, round.answered k = true →
      (round.view k).head ≤ trace.headAt (round.sampled k))
    (acknowledged : priorAck ≤ trace.headAt call.started) :
    priorAck ≤ result ∧ ∃ point,
      call.started ≤ point ∧ point ≤ call.replied ∧ trace.headAt point = result := by
  obtain ⟨k, member, heard, committed⟩ := majorities_overlap ensemble round.answered
    (fun k => round.answered k && decide (result ≤ (round.view k).head)) confirmed.quorum commitQuorum
  have localCommit : result ≤ (round.view k).head := by simpa [heard] using committed
  have beforeReply := (confirmed.samples k member heard).2.1
  have upper := Nat.le_trans localCommit
    (Nat.le_trans (sound k member heard) (trace.monotone _ _ beforeReply))
  exact head_linearizable trace confirmed durable maximum upper acknowledged

theorem tombstone_is_terminal {w : Writer Payload} {k next : Keeper Payload}
    (step : Step w k next) (deleted : k.deleted = true) : next.deleted = true := by
  cases step with
  | create notDeleted => simp [deleted] at notDeleted
  | sealKeeper _ _ =>
      unfold sealKeeper
      split <;> exact deleted
  | delete => rfl
  | _ => exact deleted

private def exampleRound : Round Nat := ⟨0, 0, 1, by decide, fun _ => empty⟩
private def exampleWriter : Writer Nat where
  round e := if e = 1 then some exampleRound else none
  issued e := if e = 1 then [⟨1, 7⟩] else []
  advertised h := h = []
private def exampleCreated : Keeper Nat := { initial with created := true }
private def exampleSealed : Keeper Nat := sealKeeper exampleCreated 1 0
private def exampleSynced : Keeper Nat :=
  { accept exampleSealed 1 [] with head := 0, floor := max exampleSealed.floor (exampleSealed.syncFloor 1) }
private def exampleAccepted : Keeper Nat :=
  { accept exampleSynced 1 (exampleSynced.history ++ stamp 1 [7]) with head := max exampleSynced.head 0 }

private theorem example_reached : Reachable exampleWriter exampleAccepted := by
  have created : Reachable exampleWriter exampleCreated := .extend .initial (.create rfl)
  have sealed : Reachable exampleWriter exampleSealed :=
    .extend created (.sealKeeper ⟨rfl, rfl⟩ (Or.inl (by decide)))
  have ownsSeal : exampleWriter.owns exampleSealed 1 := ⟨exampleRound, rfl, rfl⟩
  have synced : Reachable exampleWriter exampleSynced :=
    .extend sealed (.sync (epoch := 1) (floor := 1) (start := 1) (records := []) (head := 0)
      ⟨rfl,rfl⟩ rfl ownsSeal (by unfold SyncAdmitted; decide) rfl (fun _ => rfl)
      (by decide) (Nat.le_refl _) (by decide) (by decide) rfl)
  have ownsSync : exampleWriter.owns exampleSynced 1 := ⟨exampleRound, rfl, rfl⟩
  have admitted : MayAppend exampleSynced 1 := by
    unfold MayAppend
    try unfold Synced
    decide
  exact .extend synced (.append (payloads := [7]) (head := 0) ⟨rfl,rfl⟩ admitted ownsSync
    (List.cons_ne_nil _ _) (by decide) (by decide) (by decide) rfl)

private def exampleExecution : Execution Nat where
  writer := exampleWriter
  keeper k := if k = 2 then initial else exampleAccepted
  reached k := by split <;> first | exact .initial | exact example_reached
  reserved := rfl
  initiallyEmpty := rfl
  emptyAdvertised := rfl
  advertisedChosen history h := by
    change history = [] at h
    subst history
    refine ⟨0, fun _ => true, by decide, ?_⟩
    intro k _ _
    refine ⟨[], ?_, List.prefix_rfl⟩
    change (if k = 2 then initial else exampleAccepted).durable.votes _
    split
    · exact Or.inr rfl
    · exact Or.inl (Or.inl (Or.inr rfl))
  captured epoch r elected k signed := by
    have epochOne : epoch = 1 := by
      by_cases one : epoch = 1
      · exact one
      · simp [exampleWriter, one] at elected
    subst epoch
    have equal : exampleRound = r := Option.some.inj elected
    subst r
    have notThird : k ≠ 2 := by
      intro third
      subst k
      exact (by decide : exampleRound.sealed 2 ≠ true) signed
    simp [notThird]
    rfl

theorem reachable_two_keeper_commit :
    ∃ x : Execution Nat, Acknowledged x 1 [⟨1, 7⟩] ∧
      (x.keeper 2).tail = 0 := by
  refine ⟨exampleExecution, ?_, rfl⟩
  refine ⟨exampleRound.sealed, two_of_three_is_majority 0 1 (by decide), ?_⟩
  intro k _ voted
  have notThird : k ≠ 2 := by
    intro third
    subst k
    exact (by decide : exampleRound.sealed 2 ≠ true) voted
  refine ⟨[⟨1, 7⟩], ?_, List.prefix_rfl⟩
  simp only [exampleExecution, ite_eq_right notThird]
  exact Or.inr rfl

#print axioms append_requires_sync
#print axioms seal_tie_has_same_identity
#print axioms trim_below_head
#print axioms keeper_bounds
#print axioms reachable_keeper_refines_durable_acceptor
#print axioms recovery_rank_is_synced_then_tail
#print axioms seal_winner_dominates
#print axioms execution_refines_prefix_agreement
#print axioms quorum_acknowledgements_choose
#print axioms committed_contiguous_and_irrevocable
#print axioms seal_fences_and_covers_acknowledged_appends
#print axioms late_lower_epoch_cannot_extend_after_seal
#print axioms reachable_keeper_head_is_chosen
#print axioms read_returns_exact_committed_records
#print axioms append_is_conditional_and_idempotent
#print axioms confirmed_round_is_fresh
#print axioms opening_cut_from_durable_copies
#print axioms head_linearizable
#print axioms non_writer_head_linearizable
#print axioms tombstone_is_terminal
#print axioms reachable_two_keeper_commit

end Logkeeper.StreamJournal
