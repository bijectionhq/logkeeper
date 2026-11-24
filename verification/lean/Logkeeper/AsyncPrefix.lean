import Logkeeper.PrefixTrace

namespace Logkeeper.AsyncPrefix

open PrefixAgreement DurableAcceptor JournalRefinement PrefixTrace

set_option warningAsError true

abbrev Voter := Nat
abbrev Ballot := Nat
abbrev Value := Vote Nat

def update (f : Nat → α) (key : Nat) (value : α) : Nat → α :=
  fun k => if k = key then value else f k

structure Preparation where
  voters : List Voter
  report : Voter → Option Value
  winner : Option Value

def Preparation.seed (prep : Preparation) : History :=
  prep.winner.elim [] Vote.history

/-- The successful recovery fold selects an observed maximum. A ballot names
a single issued image, so an equal-ballot tie has the same history. -/
def Ranked (prep : Preparation) (ballot : Ballot) : Prop :=
  (∀ best, prep.winner = some best →
    best.ballot < ballot ∧ ∃ source ∈ prep.voters, prep.report source = some best) ∧
  ∀ voter ∈ prep.voters, ∀ observed, prep.report voter = some observed →
    ∃ best, prep.winner = some best ∧ WinnerDominates observed best

theorem recovery_dominates_observed {prep : Preparation} {ballot : Ballot}
    (ranked : Ranked prep ballot) {voter : Voter} {observed : Value}
    (counted : voter ∈ prep.voters) (report : prep.report voter = some observed) :
    ∃ best, prep.winner = some best ∧ WinnerDominates observed best := by
  exact ranked.2 voter counted observed report

def chooseBase (current candidate : Option Value) : Except Unit (Option Value) :=
  match current, candidate with
  | none, next => .ok next
  | known, none => .ok known
  | some known, some next =>
    if known.ballot < next.ballot then .ok (some next)
    else if next.ballot < known.ballot then .ok (some known)
    else if known.history = next.history then .ok (some known)
    else .error ()

theorem recovery_pair_keeps_rank {current candidate best : Option Value}
    (folded : chooseBase current candidate = .ok best) :
    (∀ observed, some observed = current ∨ some observed = candidate →
      ∃ winner, best = some winner ∧ WinnerDominates observed winner) ∧
    (∀ winner, best = some winner → best = current ∨ best = candidate) := by
  rcases current with _ | current <;> rcases candidate with _ | candidate
  all_goals simp [chooseBase] at folded
  · subst best
    simp
  · subst best
    simp [WinnerDominates, RankLE]
  · subst best
    simp [WinnerDominates, RankLE]
  · split at folded
    next newer =>
      simp at folded
      subst best
      constructor
      · intro observed seen
        rcases seen with equal | equal <;> cases equal
        · exact ⟨candidate, rfl, Nat.le_of_lt newer, fun eq => by omega⟩
        · exact ⟨candidate, rfl, rank_refl candidate⟩
      · exact fun _ _ => Or.inr rfl
    next notNewer =>
      split at folded
      next older =>
        simp at folded
        subst best
        constructor
        · intro observed seen
          rcases seen with equal | equal <;> cases equal
          · exact ⟨current, rfl, rank_refl current⟩
          · exact ⟨current, rfl, Nat.le_of_lt older, fun eq => by omega⟩
        · exact fun _ _ => Or.inl rfl
      next notOlder =>
        split at folded
        next histories =>
          simp at folded
          subst best
          constructor
          · intro observed seen
            rcases seen with equal | equal <;> cases equal
            · exact ⟨current, rfl, rank_refl current⟩
            · exact ⟨current, rfl, by omega, fun _ => by simp [histories]⟩
          · exact fun _ _ => Or.inl rfl
        next => contradiction

/-- Successful outcomes of the coordinator's fold in response order. -/
inductive RecoveryFold : List (Option Value) → Option Value → Prop
  | empty : RecoveryFold [] none
  | push {seen best reply winner} :
      RecoveryFold seen best → chooseBase best reply = .ok winner →
      RecoveryFold (reply :: seen) winner

theorem fold_sources_and_dominates {seen : List (Option Value)} {winner : Option Value}
    (run : RecoveryFold seen winner) :
    (∀ best, winner = some best → some best ∈ seen) ∧
    (∀ observed, some observed ∈ seen →
      ∃ best, winner = some best ∧ WinnerDominates observed best) := by
  induction run with
  | empty => simp
  | @push seen prior reply winner _ next ih =>
    obtain ⟨dominates, source⟩ := recovery_pair_keeps_rank next
    constructor
    · intro best chosen
      rcases source best chosen with used | new
      · exact List.mem_cons_of_mem _ (ih.1 _ (used.symm.trans chosen))
      · exact List.mem_cons.mpr (Or.inl (chosen.symm.trans new))
    · intro observed present
      rcases List.mem_cons.mp present with newest | older
      · exact dominates observed (Or.inr newest)
      · obtain ⟨previous, kept, lifts⟩ := ih.2 observed older
        obtain ⟨best, picked, above⟩ := dominates previous (Or.inl kept.symm)
        exact ⟨best, picked, rank_trans lifts above⟩

theorem fold_is_ranked {prep : Preparation} {ballot : Ballot}
    (folded : RecoveryFold (prep.voters.map prep.report) prep.winner)
    (earlier : ∀ v ∈ prep.voters, ∀ vote, prep.report v = some vote → vote.ballot < ballot) :
    Ranked prep ballot := by
  obtain ⟨source, dominates⟩ := fold_sources_and_dominates folded
  constructor
  · intro best chosen
    obtain ⟨v, present, reported⟩ := List.mem_map.mp (source best chosen)
    exact ⟨earlier v present best reported, v, present, reported⟩
  · intro v present observed reported
    exact dominates observed (List.mem_map.mpr ⟨v, present, reported⟩)

#print axioms recovery_pair_keeps_rank
#print axioms fold_is_ranked

def AcceptGuard (floor ballot : Ballot) : Prop :=
  AcceptAtPromise floor ballot

theorem native_accept_requires_exact_promise {floor ballot : Ballot}
    (admitted : AcceptGuard floor ballot) : floor ≠ 0 ∧ floor = ballot := by
  exact admitted

def ExactQuorum (members voters : List Voter) : Prop :=
  majorityCheck members voters = true

theorem certificate_requires_distinct_voters {members voters : List Voter}
    (quorum : ExactQuorum members voters) : voters.Nodup := by
  exact ((majorityCheck_spec _ _).mp quorum).1

structure Proposal where
  image : Nat
  history : History
  readBack : Bool
  deriving DecidableEq

structure Core where
  media : Voter → DurableAcceptor.State Nat
  prepared : Ballot → Option Preparation
  issued : Ballot → Option Proposal

def initial : Core :=
  ⟨fun _ => DurableAcceptor.initial, fun _ => none, fun _ => none⟩

def ledger (members : List Voter) (s : Core) : Ledger Voter Nat where
  members := members
  active := fun ballot => (s.prepared ballot).isSome
  prepared := fun ballot voter => (s.prepared ballot).any (·.voters.contains voter)
  report := fun ballot voter => (s.prepared ballot).bind (·.report voter)
  selected := fun ballot => (s.prepared ballot).bind (·.winner)
  issued := fun ballot =>
    (s.issued ballot).elim ((s.prepared ballot).elim [] Preparation.seed) (·.history)
  voted := fun voter => (s.media voter).votes

/-- The saved prepare snapshot remains valid when newer operations reach the
same voter. -/
def BoundReports (s : Core) (ballot : Ballot) (prep : Preparation) : Prop :=
  ∀ voter ∈ prep.voters, (s.media voter).replies ballot = some (prep.report voter)

def ExtendsSeed (prep : Preparation) (proposal : Proposal) : Prop :=
  prep.seed <+: proposal.history ∧ proposal.history.length ≤ prep.seed.length + 1

inductive Step (members : List Voter) : Core → Core → Prop
  | savePromise {s} (voter ballot : Nat) (nonzero : ballot ≠ 0)
      (admitted : PrepareAdmitted (s.media voter).promised ballot) :
      Step members s { s with media := update s.media voter (prepareOrRetry (s.media voter) ballot) }
  | prepareQuorum {s} (ballot : Ballot) (prep : Preparation)
      (fresh : s.prepared ballot = none) (quorum : ExactQuorum members prep.voters)
      (reports : BoundReports s ballot prep) (ranked : Ranked prep ballot) :
      Step members s { s with prepared := update s.prepared ballot (some prep) }
  | issue {s} (ballot : Ballot) (prep : Preparation) (proposal : Proposal)
      (prepared : s.prepared ballot = some prep) (fresh : s.issued ballot = none)
      (extendsSeed : ExtendsSeed prep proposal) :
      Step members s { s with issued := update s.issued ballot (some proposal) }
  | saveAccept {s} (voter ballot : Nat) (proposal : Proposal)
      (issued : s.issued ballot = some proposal)
      (admitted : AcceptGuard (s.media voter).promised ballot) :
      Step members s { s with media := update s.media voter (acceptVote (s.media voter) ⟨ballot, proposal.history⟩) }
  | stutter {s} : Step members s s

private theorem update_preserves_some {f : Nat → Option α} {key k : Nat}
    {old new : α} (fresh : f key = none) (lookup : f k = some old) :
    update f key (some new) k = some old := by
  by_cases equal : k = key
  · subst k
    simp [fresh] at lookup
  · simpa [update, equal] using lookup

theorem saved_reply_persists {s t : DurableAcceptor.State Nat}
    (reached : DurableAcceptor.Reachable s) (step : DurableAcceptor.Step s t)
    (saved : s.replies ballot = some report) : t.replies ballot = some report := by
  cases step with
  | accept => exact saved
  | restart => exact saved
  | prepare b newer =>
    have prior := ((reachable_replies_cover_every_lower_vote reached).repliesSound ballot report saved).1
    have different : ballot ≠ b := by omega
    simpa [DurableAcceptor.promise, different] using saved

structure Valid (members : List Voter) (s : Core) : Prop where
  mediaReached : ∀ voter, DurableAcceptor.Reachable (s.media voter)
  prepared : ∀ ballot prep, s.prepared ballot = some prep →
    ExactQuorum members prep.voters ∧ BoundReports s ballot prep ∧ Ranked prep ballot
  issued : ∀ ballot proposal, s.issued ballot = some proposal →
    ∃ prep, s.prepared ballot = some prep ∧ prep.seed <+: proposal.history
  votes : ∀ voter vote, (s.media voter).votes vote →
    ∃ proposal, s.issued vote.ballot = some proposal ∧ proposal.history = vote.history

theorem initial_valid : Valid members initial := by
  constructor
  · exact fun _ => .initial
  · simp [initial]
  · simp [initial]
  · simp [initial, DurableAcceptor.initial]

/-- Reserved repaired-media ballot. The synthetic preparation at this
ballot records no replies from an earlier ballot and casts no vote. A
repaired voter casts its bootstrap vote only when installation takes effect. -/
def bootstrapBallot : Ballot := ballotRank 1 1

def bootstrapPreparation (members : List Voter) : Preparation :=
  ⟨members, fun _ => none, none⟩

def bootstrap (members : List Voter) (base : Proposal) : Core :=
  ⟨fun _ => DurableAcceptor.promise DurableAcceptor.initial bootstrapBallot,
    update (fun _ => none) bootstrapBallot (some (bootstrapPreparation members)),
    update (fun _ => none) bootstrapBallot (some base)⟩

theorem bootstrap_valid (quorum : ExactQuorum members members) :
    Valid members (bootstrap members base) := by
  constructor
  · intro voter
    exact .extend .initial (.prepare bootstrapBallot (by decide))
  · intro ballot prep found
    by_cases atBase : ballot = bootstrapBallot
    · subst ballot
      simp [bootstrap, update] at found
      subst prep
      exact ⟨quorum, by simp [BoundReports, bootstrap, DurableAcceptor.promise, DurableAcceptor.initial, bootstrapPreparation],
        by simp [Ranked, bootstrapPreparation]⟩
    · simp [bootstrap, update, atBase] at found
  · intro ballot proposal found
    by_cases atBase : ballot = bootstrapBallot
    · subst ballot
      simp [bootstrap, update] at found
      exact ⟨bootstrapPreparation members, by simp [bootstrap, update], List.nil_prefix⟩
    · simp [bootstrap, update, atBase] at found
  · simp [bootstrap, DurableAcceptor.promise, DurableAcceptor.initial]

private theorem accept_keeps_rank {s : Core} {members : List Voter} (valid : Valid members s)
    {proposal : Proposal} (issued : s.issued ballot = some proposal)
    (admitted : AcceptGuard (s.media voter).promised ballot)
    (found : (s.media voter).latest = some old) : RankLE old ⟨ballot, proposal.history⟩ := by
  have media := reachable_replies_cover_every_lower_vote (valid.mediaReached voter)
  obtain ⟨voted, floor⟩ := media.latestRecorded old found
  have atPromise := (native_accept_requires_exact_promise admitted).2
  refine ⟨Nat.le_trans floor (Nat.le_of_eq atPromise), ?_⟩
  change (old.ballot = ballot → old.history.length ≤ proposal.history.length)
  intro equal
  obtain ⟨other, exactIssue, history⟩ := valid.votes voter old voted
  rw [equal, issued] at exactIssue
  cases exactIssue
  simp [history]

theorem step_refines_media {members : List Voter} {before after : Core}
    (valid : Valid members before) (step : Step members before after) (voter : Voter) :
    DurableAcceptor.Step (before.media voter) (after.media voter) := by
  cases step with
  | savePromise target ballot _ admitted =>
    by_cases equal : voter = target
    · subst voter
      simpa [update] using prepare_or_retry_is_step admitted
    · simpa [update, equal] using DurableAcceptor.Step.restart (state := before.media voter)
  | saveAccept target ballot proposal issued admitted =>
    by_cases equal : voter = target
    · subst voter
      simpa [update] using accept_at_promise_is_step ⟨
        ballot, proposal.history⟩ admitted (fun _ => accept_keeps_rank valid issued admitted)
    · simpa [update, equal] using DurableAcceptor.Step.restart (state := before.media voter)
  | prepareQuorum | issue | stutter => exact .restart

theorem step_preserves_valid {members : List Voter} {before after : Core}
    (valid : Valid members before) (step : Step members before after) :
    Valid members after := by
  have mediaStep := step_refines_media valid step
  refine ⟨fun v => .extend (valid.mediaReached v) (mediaStep v), ?_, ?_, ?_⟩
  · have keep {prep : Preparation} {ballot : Ballot}
        (reports : BoundReports before ballot prep) : BoundReports after ballot prep :=
      fun v mem => saved_reply_persists (valid.mediaReached v) (mediaStep v) (reports v mem)
    intro ballot prep found
    cases step with
    | prepareQuorum b p fresh quorum reports ranked =>
      by_cases equal : ballot = b
      · subst ballot
        simp [update] at found
        subst prep
        exact ⟨quorum, keep reports, ranked⟩
      · exact valid.prepared ballot prep (by simpa [update, equal] using found)
    | savePromise | saveAccept =>
      obtain ⟨quorum, reports, ranked⟩ := valid.prepared ballot prep found
      exact ⟨quorum, keep reports, ranked⟩
    | issue | stutter => exact valid.prepared ballot prep found
  · intro ballot proposal found
    cases step with
    | prepareQuorum b p fresh _ _ _ =>
      obtain ⟨prep, reported, extendsSeed⟩ := valid.issued ballot proposal found
      exact ⟨prep, update_preserves_some fresh reported, extendsSeed⟩
    | issue b p candidate prepared fresh extendsSeed =>
      by_cases equal : ballot = b
      · subst ballot
        simp [update] at found
        subst proposal
        exact ⟨p, prepared, extendsSeed.1⟩
      · exact valid.issued ballot proposal (by simpa [update, equal] using found)
    | savePromise | saveAccept | stutter => exact valid.issued ballot proposal found
  · intro v vote observed
    cases step with
    | savePromise target ballot _ _ =>
      by_cases equal : v = target
      · subst v
        apply valid.votes target vote
        by_cases retry : (before.media target).promised = ballot
        · simpa [update, prepareOrRetry, retry] using observed
        · simpa [update, prepareOrRetry, retry, DurableAcceptor.promise] using observed
      · exact valid.votes v vote (by simpa [update, equal] using observed)
    | saveAccept target ballot proposal issued admitted =>
      by_cases equal : v = target
      · subst v
        simp [update, acceptVote] at observed
        rcases observed with old | rfl
        · exact valid.votes target vote old
        · exact ⟨proposal, issued, rfl⟩
      · exact valid.votes v vote (by simpa [update, equal] using observed)
    | issue b p candidate prepared fresh extendsSeed =>
      obtain ⟨proposal, reported, eq⟩ := valid.votes v vote observed
      exact ⟨proposal, update_preserves_some fresh reported, eq⟩
    | prepareQuorum | stutter => exact valid.votes v vote observed

theorem valid_supplies_rules {members : List Voter} {s : Core} (valid : Valid members s) :
    Rules (ledger members s) := by
  constructor
  · constructor
    · intro ballot active
      cases found : s.prepared ballot with
      | none => simp [ledger, found] at active
      | some prep =>
        have majority := ((majorityCheck_spec _ _).mp (valid.prepared ballot prep found).1).2.2
        simpa only [ledger, found, Option.any_some] using majority
    · intro ballot voter observed active member counted reported
      cases found : s.prepared ballot with
      | none => simp [ledger, found] at active
      | some prep =>
        have voted : voter ∈ prep.voters := by simpa [ledger, found] using counted
        have report : prep.report voter = some observed := by simpa [ledger, found] using reported
        obtain ⟨quorum, bound, ranked⟩ := valid.prepared ballot prep found
        obtain ⟨best, selected, dominates⟩ := recovery_dominates_observed ranked voted report
        obtain ⟨earlier, source, present, fromSource⟩ := ranked.1 best selected
        have exactReply := reachable_replies_cover_every_lower_vote (valid.mediaReached source)
        have accepted := (exactReply.repliesSound ballot (prep.report source) (bound source present)).2.1
          best fromSource
        have configured := ((majorityCheck_spec _ _).mp quorum).2.1 source present
        exact ⟨source, best, configured, by simpa [ledger, found] using present,
          by simpa [ledger, found] using fromSource, by simpa [ledger, found] using selected,
          accepted.1, earlier, dominates⟩
    · intro voter vote voted
      obtain ⟨proposal, issued, eq⟩ := valid.votes voter vote voted
      obtain ⟨prep, prepared, extendsSeed⟩ := valid.issued vote.ballot proposal issued
      refine ⟨by simp [ledger, prepared], ?_, ?_⟩
      · simpa [seed, ledger, prepared, ← eq, Preparation.seed] using extendsSeed
      · simp [ledger, issued, eq, List.prefix_rfl]
  · apply durable_acceptor_traces_supply_quorum_reply_coverage s.media
    · exact fun v _ => valid.mediaReached v
    · exact fun _ _ _ voted => voted
    · intro voter _ ballot counted
      cases found : s.prepared ballot with
      | none => simp [ledger, found] at counted
      | some prep =>
        have present : voter ∈ prep.voters := by simpa [ledger, found] using counted
        simpa [ledger, found] using (valid.prepared ballot prep found).2.1 voter present

theorem vote_persists (step : Step members before after)
    (voted : (before.media voter).votes vote) : (after.media voter).votes vote := by
  cases step with
  | savePromise target ballot _ _ =>
    by_cases equal : voter = target
    · subst voter
      by_cases retry : (before.media target).promised = ballot <;>
        simpa [update, prepareOrRetry, DurableAcceptor.promise, retry] using voted
    · simpa [update, equal] using voted
  | saveAccept target ballot proposal _ _ =>
    by_cases equal : voter = target
    · subst voter
      simpa [update, acceptVote] using (Or.inl voted :
        (before.media target).votes vote ∨ vote = ⟨ballot, proposal.history⟩)
    · simpa [update, equal] using voted
  | _ => exact voted

theorem issue_persists (step : Step members before after)
    (issued : before.issued ballot = some proposal) : after.issued ballot = some proposal := by
  cases step with
  | issue _ _ _ _ fresh _ => exact update_preserves_some fresh issued
  | _ => exact issued

theorem choice_persists (step : Step members before after)
    (choice : Chosen (ledger members before) ballot history) :
    Chosen (ledger members after) ballot history := by
  obtain ⟨quorum, majority, evidence⟩ := choice
  refine ⟨quorum, majority, ?_⟩
  intro v member counted
  obtain ⟨vote, voted, exactBallot, contains⟩ := evidence v member counted
  exact ⟨vote, vote_persists step voted, exactBallot, contains⟩

/-- PrefixAgreement gives a ledger of evidence and state predicates. These
are its append-only evidence updates. Transitions whose observable evidence
is unchanged are stutters. -/
inductive LedgerStep : Ledger Voter Nat → Ledger Voter Nat → Prop
  | openBallot {l} (b : Ballot) (prep : Preparation) :
      LedgerStep l { l with
        active := update l.active b True
        prepared := update l.prepared b (fun v => prep.voters.contains v)
        report := update l.report b prep.report
        selected := update l.selected b prep.winner
        issued := update l.issued b prep.seed }
  | issue {l} (b : Ballot) (history : History) :
      LedgerStep l { l with issued := update l.issued b history }
  | vote {l} (v : Voter) (vote : Value) :
      LedgerStep l { l with voted := update l.voted v (fun earlier => l.voted v earlier ∨ earlier = vote) }
  | stutter {l} : LedgerStep l l

theorem step_refines_ledger (valid : Valid members before) (step : Step members before after) :
    LedgerStep (ledger members before) (ledger members after) := by
  cases step with
  | prepareQuorum b prep fresh _ _ _ =>
    have unissued : before.issued b = none := by
      cases h : before.issued b with
      | none => rfl
      | some p =>
        obtain ⟨_, prepared, _⟩ := valid.issued b p h
        rw [fresh] at prepared
        contradiction
    have changed : ledger members { before with prepared := update before.prepared b (some prep) } =
        { ledger members before with
          active := update (ledger members before).active b True
          prepared := update (ledger members before).prepared b (fun v => prep.voters.contains v)
          report := update (ledger members before).report b prep.report
          selected := update (ledger members before).selected b prep.winner
          issued := update (ledger members before).issued b prep.seed } := by
      simp only [ledger, Ledger.mk.injEq, true_and]
      repeat' first | exact True.intro | apply And.intro | funext k; by_cases eq : k = b <;> simp [update, eq, unissued]
    rw [changed]
    exact .openBallot b prep
  | issue b prep proposal _ _ _ =>
    have changed : (fun k => (update before.issued b (some proposal) k).elim
        ((before.prepared k).elim [] Preparation.seed) Proposal.history) =
        update (ledger members before).issued b proposal.history := by
      funext k
      by_cases eq : k = b <;> simp [update, ledger, eq]
    have ref := LedgerStep.issue (l := ledger members before) b proposal.history
    simpa only [ledger, changed] using ref
  | saveAccept v b p _ _ =>
    have changed : (fun k => (update before.media v (acceptVote (before.media v)
        ⟨b, p.history⟩) k).votes) =
        update (ledger members before).voted v
          (fun vote => (before.media v).votes vote ∨ vote = ⟨b, p.history⟩) := by
      funext k
      by_cases eq : k = v <;> simp [update, ledger, acceptVote, eq]
    have ref := LedgerStep.vote (l := ledger members before) v ⟨b, p.history⟩
    simpa only [ledger, changed] using ref
  | savePromise v b _ _ =>
    have unchanged : (fun k => (update before.media v (prepareOrRetry (before.media v) b) k).votes)
        = (fun k => (before.media k).votes) := by
      funext k
      by_cases atVoter : k = v
      · by_cases retry : (before.media v).promised = b <;>
          simp [update, atVoter, prepareOrRetry, retry, DurableAcceptor.promise]
      · simp [update, atVoter]
    simpa only [ledger, unchanged] using (LedgerStep.stutter (l := ledger members before))
  | stutter => exact .stutter

#print axioms step_refines_ledger
#print axioms choice_persists

#print axioms step_refines_media
#print axioms step_preserves_valid
#print axioms valid_supplies_rules

end Logkeeper.AsyncPrefix
