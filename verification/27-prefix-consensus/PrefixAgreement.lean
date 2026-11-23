import JournalRefinement

set_option warningAsError true

namespace PrefixAgreement

structure Vote (Command : Type) where
  ballot : Nat
  history : List Command

def RankLE (earlier later : Vote Command) : Prop :=
  earlier.ballot ≤ later.ballot ∧
  (earlier.ballot = later.ballot → earlier.history.length ≤ later.history.length)

theorem rank_refl (vote : Vote Command) : RankLE vote vote :=
  ⟨Nat.le_refl _, fun _ => Nat.le_refl _⟩

theorem rank_trans {first second third : Vote Command}
    (firstLE : RankLE first second) (secondLE : RankLE second third) :
    RankLE first third := by
  refine ⟨Nat.le_trans firstLE.1 secondLE.1, ?_⟩
  intro equal
  have firstBallot := firstLE.1
  have secondBallot := secondLE.1
  exact Nat.le_trans (firstLE.2 (by omega)) (secondLE.2 (by omega))

structure Ledger (Voter Command : Type) where
  members : List Voter
  active : Nat → Prop
  prepared : Nat → Voter → Bool
  report : Nat → Voter → Option (Vote Command)
  selected : Nat → Option (Vote Command)
  issued : Nat → List Command
  voted : Voter → Vote Command → Prop

def seed (ledger : Ledger Voter Command) (ballot : Nat) : List Command :=
  (ledger.selected ballot).elim [] Vote.history

def WinnerDominates (observed winner : Vote Command) : Prop :=
  RankLE observed winner

def ReplyCoverage (ledger : Ledger Voter Command) : Prop :=
  ∀ ballot voter, voter ∈ ledger.members → ledger.prepared ballot voter = true →
    ∀ vote, ledger.voted voter vote → vote.ballot < ballot →
      ∃ observed, ledger.report ballot voter = some observed ∧ RankLE vote observed

structure BallotRules (ledger : Ledger Voter Command) : Prop where
  prepares : ∀ ballot, ledger.active ballot →
    JournalRefinement.Majority ledger.members (ledger.prepared ballot)
  winner : ∀ ballot voter observed, ledger.active ballot → voter ∈ ledger.members →
    ledger.prepared ballot voter = true → ledger.report ballot voter = some observed →
    ∃ source best, source ∈ ledger.members ∧ ledger.prepared ballot source = true ∧
      ledger.report ballot source = some best ∧ ledger.selected ballot = some best ∧
      ledger.voted source best ∧ best.ballot < ballot ∧ WinnerDominates observed best
  chain : ∀ voter vote, ledger.voted voter vote →
    ledger.active vote.ballot ∧ seed ledger vote.ballot <+: vote.history ∧
      vote.history <+: ledger.issued vote.ballot

structure Rules (ledger : Ledger Voter Command) : Prop extends BallotRules ledger where
  replyCoverage : ReplyCoverage ledger

def Chosen (ledger : Ledger Voter Command) (ballot : Nat) (history : List Command) : Prop :=
  ∃ voters, JournalRefinement.Majority ledger.members voters ∧
    ∀ voter ∈ ledger.members, voters voter = true →
      ∃ vote, ledger.voted voter vote ∧ vote.ballot = ballot ∧ history <+: vote.history

theorem chosen_is_prefix_of_issued {ledger : Ledger Voter Command} (rules : Rules ledger)
    {ballot : Nat} {history : List Command} (chosen : Chosen ledger ballot history) :
    history <+: ledger.issued ballot := by
  obtain ⟨votes, majority, evidence⟩ := chosen
  obtain ⟨voter, member, voted, _⟩ :=
    JournalRefinement.majorities_overlap ledger.members votes votes majority majority
  obtain ⟨vote, supported, same, contains⟩ := evidence voter member voted
  exact contains.trans (same ▸ (rules.chain voter vote supported).2.2)

theorem later_ballot_inherits_chosen_prefix {ledger : Ledger Voter Command} (rules : Rules ledger)
    {lower : Nat} {history : List Command} (chosen : Chosen ledger lower history) :
    ∀ ballot, lower < ballot → ledger.active ballot → history <+: seed ledger ballot := by
  intro ballot
  induction ballot using Nat.strongRecOn with
  | ind ballot prior =>
      intro later active
      obtain ⟨writeQuorum, writeMajority, supported⟩ := chosen
      obtain ⟨voter, member, voted, promised⟩ :=
        JournalRefinement.majorities_overlap ledger.members writeQuorum (ledger.prepared ballot)
          writeMajority (rules.prepares ballot active)
      obtain ⟨vote, accepted, atLower, prefixProof⟩ := supported voter member voted
      obtain ⟨observed, reply, covers⟩ :=
        rules.replyCoverage ballot voter member promised vote accepted (atLower.symm ▸ later)
      obtain ⟨source, best, _, _, _, selected, held, bestEarlier, dominates⟩ :=
        rules.winner ballot voter observed active member promised reply
      have winnerRank : RankLE observed best := by
        exact dominates
      have originalRank := rank_trans covers winnerRank
      have hasVote := rules.chain source best held
      have lowerOrSame : lower ≤ best.ballot := atLower ▸ originalRank.1
      have seedIsBest : seed ledger ballot = best.history := by simp [seed, selected]
      rw [seedIsBest]
      by_cases equal : lower = best.ballot
      · have same : vote.ballot = best.ballot := atLower.trans equal
        have sameChain : vote.history <+: ledger.issued best.ballot :=
          same ▸ (rules.chain voter vote accepted).2.2
        exact prefixProof.trans (List.prefix_of_prefix_length_le sameChain hasVote.2.2
          (originalRank.2 same))
      · have strictlyLater : lower < best.ballot := by omega
        exact (prior best.ballot bestEarlier strictlyLater hasVote.1).trans hasVote.2.1

theorem different_ballots_preserve_exact_order {ledger : Ledger Voter Command} (rules : Rules ledger)
    {older newer : Nat} {left right : List Command}
    (oldChoice : Chosen ledger older left) (newChoice : Chosen ledger newer right)
    (later : older < newer) : left <+: right ∨ right <+: left := by
  obtain ⟨votes, majority, accepts⟩ := newChoice
  obtain ⟨voter, member, voted, _⟩ :=
    JournalRefinement.majorities_overlap ledger.members votes votes majority majority
  obtain ⟨v, hasVote, same, rightInVote⟩ := accepts voter member voted
  have active := (rules.chain voter v hasVote).1
  have inherits := later_ballot_inherits_chosen_prefix rules oldChoice newer later (same ▸ active)
  have leftInVote := inherits.trans (same ▸ (rules.chain voter v hasVote).2.1)
  exact List.prefix_or_prefix_of_prefix leftInVote rightInVote

theorem every_chosen_prefix_agrees {ledger : Ledger Voter Command} (rules : Rules ledger)
    {first second : Nat} {left right : List Command}
    (oldChoice : Chosen ledger first left) (newChoice : Chosen ledger second right) :
    left <+: right ∨ right <+: left := by
  rcases Nat.lt_trichotomy first second with lower | equal | higher
  · exact different_ballots_preserve_exact_order rules oldChoice newChoice lower
  · exact List.prefix_or_prefix_of_prefix (chosen_is_prefix_of_issued rules oldChoice)
      (equal.symm ▸ chosen_is_prefix_of_issued rules newChoice)
  · exact (different_ballots_preserve_exact_order rules newChoice oldChoice higher).symm

theorem any_two_certificates_agree_at_position {ledger : Ledger Voter Command}
    (rules : Rules ledger) {first second : Nat} {left right : List Command}
    (firstChoice : Chosen ledger first left) (secondChoice : Chosen ledger second right)
    {position : Nat} {x y : Command} (firstValue : left[position]? = some x)
    (secondValue : right[position]? = some y) : x = y := by
  have at_shared_position {xs ys : List Command} {a b : Command} (order : xs <+: ys)
      (xAt : xs[position]? = some a) (yAt : ys[position]? = some b) : a = b := by
    obtain ⟨more, rfl⟩ := order
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp xAt).1, xAt] at yAt
    exact Option.some.inj yAt
  rcases every_chosen_prefix_agrees rules firstChoice secondChoice with order | order
  · exact at_shared_position order firstValue secondValue
  · exact (at_shared_position order secondValue firstValue).symm

def learn (known certified : List Command) : List Command :=
  if known.length ≤ certified.length then certified else known

theorem delivery_extends_the_learned_prefix {ledger : Ledger Voter Command} (rules : Rules ledger)
    {knownBallot newBallot : Nat} {known certified : List Command}
    (knownChoice : Chosen ledger knownBallot known) (arrived : Chosen ledger newBallot certified) :
    known <+: learn known certified ∧ certified <+: learn known certified := by
  rcases every_chosen_prefix_agrees rules knownChoice arrived with shorter | longer
  · rw [learn, ite_eq_left shorter.length_le]
    exact ⟨shorter, List.prefix_rfl⟩
  · by_cases tied : known.length ≤ certified.length
    · rw [learn, ite_eq_left tied, longer.eq_of_length_le tied]
      exact ⟨List.prefix_rfl, List.prefix_rfl⟩
    · rw [learn, ite_eq_right tied]
      exact ⟨List.prefix_rfl, longer⟩

#print axioms rank_refl
#print axioms rank_trans
#print axioms chosen_is_prefix_of_issued
#print axioms later_ballot_inherits_chosen_prefix
#print axioms different_ballots_preserve_exact_order
#print axioms every_chosen_prefix_agrees
#print axioms any_two_certificates_agree_at_position
#print axioms delivery_extends_the_learned_prefix

end PrefixAgreement
