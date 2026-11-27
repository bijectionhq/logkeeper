/-!
The replicated catalog's first-claim-wins rule (design section H,
`keeper/catalog_stream.rs`).

The catalog is a consensus stream whose state machine folds its committed
log. `Claim(stream, genesis)` records the genesis when the stream has none
and otherwise leaves the recorded one; its reply carries the genesis the
stream holds after it applies. Raft gives every catalog voter a prefix of
one committed log, and a checkpoint replaces a prefix by its fold.

`first_claim_wins` identifies the genesis of every stream as the first
committed claim for it. `at_most_one_genesis_per_stream` shows every claim
reply for a stream names that same genesis, `replicas_agree` that replicas
holding prefixes of the committed log never disagree on a stream they both
know, and `checkpoint_then_suffix` that restoring a checkpoint and replaying
the suffix reaches the same catalog. The single-keeper catalog's
put-if-absent is `LeaderJournal.Bootstrap.bind`; this module lifts it to the
replicated log.
-/

namespace Logkeeper.ConsensusAdditions.CatalogClaim

set_option warningAsError true

structure Genesis where
  incarnation : Nat
  voters : List Nat
  deriving DecidableEq, Repr

inductive Command where
  | claim (stream : Nat) (genesis : Genesis)
  /-- Stages, contacts and other records leave the geneses alone. -/
  | other
  deriving DecidableEq, Repr

abbrev Catalog := Nat → Option Genesis

def empty : Catalog := fun _ => none

def apply (catalog : Catalog) : Command → Catalog
  | .claim stream genesis =>
      match catalog stream with
      | some _ => catalog
      | none => fun other => if other = stream then some genesis else catalog other
  | .other => catalog

/-- The genesis a claim's reply carries. -/
def reply (catalog : Catalog) (stream : Nat) (genesis : Genesis) : Genesis :=
  (catalog stream).getD genesis

def fold (start : Catalog) (log : List Command) : Catalog := log.foldl apply start

def firstClaim (stream : Nat) : List Command → Option Genesis
  | [] => none
  | .claim claimed genesis :: rest => if claimed = stream then some genesis else firstClaim stream rest
  | .other :: rest => firstClaim stream rest

theorem apply_keeps (catalog : Catalog) (command : Command) {stream : Nat} {genesis : Genesis}
    (held : catalog stream = some genesis) : apply catalog command stream = some genesis := by
  cases command with
  | other => exact held
  | claim claimed proposed =>
      simp only [apply]
      cases current : catalog claimed with
      | some _ => exact held
      | none =>
          have different : stream ≠ claimed := fun same => by
            subst same
            rw [held] at current
            cases current
          simp [different, held]

theorem fold_from (start : Catalog) (log : List Command) (stream : Nat) :
    fold start log stream = (start stream).or (firstClaim stream log) := by
  induction log generalizing start with
  | nil => simp [fold, firstClaim]
  | cons command rest prior =>
      simp only [fold, List.foldl_cons] at prior ⊢
      rw [prior]
      cases command with
      | other => rfl
      | claim claimed genesis =>
          simp only [apply, firstClaim]
          cases current : start claimed with
          | some held =>
              by_cases same : claimed = stream
              · subst same
                simp [current]
              · simp [same]
          | none =>
              by_cases same : claimed = stream
              · subst same
                simp [current]
              · have : stream ≠ claimed := Ne.symm same
                simp [same, this]

/-- The genesis a stream holds is the first committed claim for it. -/
theorem first_claim_wins (log : List Command) (stream : Nat) :
    fold empty log stream = firstClaim stream log := by
  rw [fold_from]
  rfl

theorem claimed_genesis_is_permanent {start : Catalog} {log : List Command} {stream : Nat}
    {genesis : Genesis} (held : fold start log stream = some genesis) (later : List Command) :
    fold start (log ++ later) stream = some genesis := by
  simp only [fold, List.foldl_append] at held ⊢
  induction later generalizing start log with
  | nil => exact held
  | cons command rest prior =>
      simp only [List.foldl_cons]
      have next := apply_keeps (log.foldl apply start) command held
      exact prior (log := []) (start := apply (log.foldl apply start) command) next

/-- Every committed claim's reply names the genesis the stream holds at the
    end of the log, so all replies for one stream agree. -/
theorem claim_reply_is_final (before after : List Command) (stream : Nat) (genesis : Genesis) :
    some (reply (fold empty before) stream genesis) =
      fold empty (before ++ Command.claim stream genesis :: after) stream := by
  have applied : fold empty (before ++ [Command.claim stream genesis]) stream =
      some (reply (fold empty before) stream genesis) := by
    simp only [fold, List.foldl_append, List.foldl_cons, List.foldl_nil, reply]
    cases current : List.foldl apply empty before stream with
    | some held => simp [apply, current]
    | none => simp [apply, current]
  have := claimed_genesis_is_permanent applied after
  rw [List.append_assoc] at this
  exact this.symm

/-- Two claim replies for one stream in one committed log name the same
    genesis, whichever claim came first. -/
theorem at_most_one_genesis_per_stream (before middle after : List Command) (stream : Nat)
    (a b : Genesis) :
    reply (fold empty before) stream a =
      reply (fold empty (before ++ Command.claim stream a :: middle)) stream b := by
  have first := claim_reply_is_final before (middle ++ Command.claim stream b :: after) stream a
  have second := claim_reply_is_final (before ++ Command.claim stream a :: middle) after stream b
  have joined : before ++ Command.claim stream a :: (middle ++ Command.claim stream b :: after) =
      (before ++ Command.claim stream a :: middle) ++ Command.claim stream b :: after := by
    simp
  rw [joined] at first
  exact Option.some.inj (first.trans second.symm)

/-- Replicas hold prefixes of one committed log, so a stream known to a
    lagging replica has the same genesis on every more advanced one. -/
theorem replicas_agree {short long : List Command} (lagging : short <+: long) {stream : Nat}
    {genesis : Genesis} (known : fold empty short stream = some genesis) :
    fold empty long stream = some genesis := by
  obtain ⟨later, rfl⟩ := lagging
  exact claimed_genesis_is_permanent known later

/-- A checkpoint is the fold of the prefix it replaces. -/
theorem checkpoint_then_suffix (start : Catalog) (compacted suffix : List Command) :
    fold (fold start compacted) suffix = fold start (compacted ++ suffix) := by
  simp [fold, List.foldl_append]

#print axioms first_claim_wins
#print axioms claimed_genesis_is_permanent
#print axioms claim_reply_is_final
#print axioms at_most_one_genesis_per_stream
#print axioms replicas_agree
#print axioms checkpoint_then_suffix

end Logkeeper.ConsensusAdditions.CatalogClaim
