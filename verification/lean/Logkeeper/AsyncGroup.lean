import Logkeeper.AsyncPrefix
import Logkeeper.OrderedGuards

namespace Logkeeper.AsyncGroup

open AsyncPrefix PrefixAgreement DurableAcceptor PrefixTrace JournalRefinement

set_option warningAsError true

inductive Operation where
  | choose | recover | compact | repairSeed
  deriving DecidableEq

inductive Request where
  | prepare (ballot : Ballot)
  | accept (ballot : Ballot) (proposal : Proposal)
  deriving DecidableEq

def Request.ballot : Request → Ballot
  | .prepare ballot | .accept ballot _ => ballot

inductive Packet where
  | call (voter : Voter) (request : Request)
  /- A usable promise refers to the immutable saved snapshot at (voter, ballot).
  A retry reporting an accept at its own ballot takes the rejection path. -/
  | promise (voter : Voter) (ballot : Ballot) (hasAccepted : Bool)
  | vote (voter : Voter) (ballot image : Nat) (readBack mirrored : Bool)
  | reject (voter : Voter) (ballot : Ballot) (newer : Bool)
  deriving DecidableEq

inductive WireEffect where
  | connect | magic | kind | group | voter | round | nonce | flag | len | body
  | digest | selectedSlot | generation | flush | timeout
  deriving DecidableEq

/-- Independent cursors for the sending and receiving futures. Connection
admission and ordered, exact byte decoding are transport premises. -/
structure Wire where
  packet : Packet
  send : List WireEffect
  receive : List WireEffect
  deriving DecidableEq

def Wire.begin (p : Packet) : Wire :=
  let fields : List WireEffect := match p with
    | .call _ (.prepare _) => [.magic, .kind, .group, .round, .nonce]
    | .call _ (.accept ..) => [.magic, .kind, .group, .round, .nonce, .flag, .len, .body]
    | .promise _ _ false => [.magic, .kind, .voter, .round, .nonce, .flag]
    | .promise _ _ true => [.magic, .kind, .voter, .round, .nonce, .flag, .round, .nonce, .len, .body]
    | .vote .. => [.magic, .kind, .voter, .round, .nonce, .digest, .flag, .selectedSlot,
                   .generation, .digest, .generation, .digest]
    | .reject _ _ false => [.magic, .kind, .voter, .round, .nonce]
    | .reject _ _ true => [.magic, .kind, .voter, .round, .nonce, .round, .nonce]
  let connect : List WireEffect := match p with
    | .call .. => [.connect]
    | _ => []
  ⟨p, connect ++ fields ++ [.flush], fields ++ [.timeout]⟩

def Wire.done (p : Packet) : Wire := ⟨p, [], []⟩

inductive DiskEffect where
  | lock | seekBody | writeBody | clearTail | seekHeader | writeHeader | fileSync
  | seekSlot | readHeader | readBody | authenticate | select | directorySync
  | openReservation | writeReservation | syncReservation
  deriving DecidableEq

def writeSlot : List DiskEffect := [.seekBody, .writeBody, .clearTail, .seekHeader, .writeHeader]
def readSlot : List DiskEffect := [.seekSlot, .readHeader, .readBody, .authenticate]
def reopen : List DiskEffect := [.lock] ++ readSlot ++ readSlot ++ [.select, .fileSync, .directorySync]

/-- The image is the normalized successor base. Its byte identity is opaque
to the protocol; the history is the logical replay projection. -/
structure RepairArtifact where
  source : Nat
  target : Nat
  image : Nat
  history : History
  deriving DecidableEq

def RepairArtifact.proposal (artifact : RepairArtifact) : Proposal :=
  ⟨artifact.image, artifact.history, false⟩

def installEffects : List DiskEffect :=
  [.lock, .openReservation] ++ readSlot ++ readSlot ++ [.select] ++
    writeSlot ++ [.fileSync] ++ writeSlot ++ [.fileSync, .directorySync,
    .writeReservation, .syncReservation]

inductive VoterMode where
  | ready
  | uninstalled
  | installing (remaining : List DiskEffect)
  | first (request : Request) (remaining : List DiskEffect)
  | mirror (reply : Packet) (remaining : List DiskEffect)
  | offline (candidate : Option Request)
  | reopening (candidate : Option Request) (remaining : List DiskEffect)
  deriving DecidableEq

def crashCandidate : VoterMode → Option Request
  | .first request [] => some request
  | .offline candidate | .reopening candidate _ => candidate
  | _ => none

inductive Phase where
  | preparing | prepared | accepting | confirmed | closed
  deriving DecidableEq

structure Round where
  operation : Operation
  peers : List Voter
  phase : Phase := .preparing
  promises : List Voter := []
  votes : List Voter := []
  deriving DecidableEq

structure State where
  core : Core
  rounds : Ballot → Option Round
  voters : Voter → VoterMode
  net : List Wire
  scope : Nat
  repair : Option RepairArtifact
  sealOf : History → Option Nat

def State.initial (scope : Nat := 0) (sealOf : History → Option Nat := fun _ => none) : State :=
  ⟨AsyncPrefix.initial, fun _ => none, fun _ => .ready, [], scope, none, sealOf⟩

def State.seeded (members : List Voter) (seed : RepairArtifact)
    (sealOf : History → Option Nat) : State :=
  ⟨bootstrap members seed.proposal,
    update (fun _ => none) bootstrapBallot (some ⟨.recover, [], .closed, [], []⟩),
    fun _ => .uninstalled, [], seed.target, some seed, sealOf⟩

def State.withRound (s : State) (ballot : Ballot) (round : Round) : State :=
  { s with rounds := update s.rounds ballot (some round) }

def CanStart (members : List Voter) (s : State) (voter : Voter) : Request → Prop
  | .prepare b => voter ∈ members ∧ b ≠ 0 ∧ PrepareAdmitted (s.core.media voter).promised b
  | .accept b p => voter ∈ members ∧ s.core.issued b = some p ∧
      AcceptGuard (s.core.media voter).promised b

/-- First slot stabilization is the abstract effect, even if mirroring or the
calling future subsequently fails. The immutable issued image also discharges
the equal-ballot divergence check for an authenticated call. -/
def promisePacket (voter : Voter) (b : Ballot) (prior : DurableAcceptor.State Nat) : Packet :=
  if prior.latest.any (fun vote => b ≤ vote.ballot) then .reject voter b false
  else .promise voter b prior.latest.isSome

inductive Save (members : List Voter) (s : State) (voter : Voter) :
    Request → Core → Packet → List DiskEffect → Prop
  | promise (b : Ballot) (nonzero : b ≠ 0)
      (admitted : PrepareAdmitted (s.core.media voter).promised b) :
      Save members s voter (.prepare b)
        { s.core with media := update s.core.media voter (prepareOrRetry (s.core.media voter) b) }
        (promisePacket voter b (s.core.media voter)) (writeSlot ++ [.fileSync])
  | accept (b : Ballot) (p : Proposal) (issued : s.core.issued b = some p)
      (admitted : AcceptGuard (s.core.media voter).promised b) :
      Save members s voter (.accept b p)
        { s.core with media := update s.core.media voter (acceptVote (s.core.media voter) ⟨b, p.history⟩) }
        (.vote voter b p.image p.readBack true)
        (writeSlot ++ [.fileSync] ++ if p.readBack then readSlot ++ readSlot else [])

theorem save_refines {s : State} {core : Core}
    (effect : Save members s voter request core reply effects) : AsyncPrefix.Step members s.core core := by
  cases effect with
  | promise b nonzero admitted => exact .savePromise voter b nonzero admitted
  | accept b p issued admitted => exact .saveAccept voter b p issued admitted

/-- An exact configured quorum, formed from a single reply per expected
future, with the reply bound to its ballot, image, mirrors and read-back flag. -/
def MatchesVote (expected : Voter) (ballot : Ballot) (p : Proposal) (packet : Packet) : Prop :=
  packet = .vote expected ballot p.image p.readBack true

inductive Action where
  | start (ballot : Ballot) | replace (old new : Ballot)
  | send (packet : Packet) | wireSend (effect : WireEffect) | wireReceive (effect : WireEffect)
  | localDelivery | dropPacket | duplicate | refuse | delay
  | startJob (voter : Voter) | disk (voter : Voter) (effect : DiskEffect)
  | reply (voter : Voter) | collect (ballot : Ballot) (voter : Voter)
  | prepared (ballot : Ballot) | issue (ballot : Ballot)
  | certificate (ballot : Ballot) (history : History)
  | coordinatorCrash (ballot : Ballot) | finish (ballot : Ballot)
  | voterCrash (voter : Voter) | restart (voter : Voter)
  | exportSeed (ballot : Ballot) (seed : RepairArtifact)
  | beginInstall (voter : Voter) | installed (voter : Voter)
  deriving DecidableEq

inductive Step (members : List Voter) : State → Action → State → Prop
  | start {s} (ballot : Ballot) (r : Round)
      (fresh : s.rounds ballot = none) (nonzero : ballot ≠ 0)
      (empty : r = ⟨r.operation, r.peers, .preparing, [], []⟩)
      (peers : ExactQuorum members r.peers) :
      Step members s (.start ballot) (s.withRound ballot r)
  | replace {s} (old new : Ballot) (prior r : Round)
      (present : s.rounds old = some prior) (fresh : s.rounds new = none)
      (newer : old < new) (empty : r = ⟨r.operation, r.peers, .preparing, [], []⟩)
      (peers : ExactQuorum members r.peers) :
      Step members s (.replace old new)
        ((s.withRound old { prior with phase := .closed }).withRound new r)
  | sendPrepare {s} (voter : Voter) (ballot : Ballot) (r : Round)
      (round : s.rounds ballot = some r) (phase : r.phase = .preparing) (peer : voter ∈ r.peers) :
      Step members s (.send (.call voter (.prepare ballot)))
        { s with net := Wire.begin (.call voter (.prepare ballot)) :: s.net }
  | sendAccept {s} (voter : Voter) (ballot : Ballot) (r : Round) (p : Proposal)
      (round : s.rounds ballot = some r) (phase : r.phase = .accepting)
      (promised : voter ∈ r.promises) (issued : s.core.issued ballot = some p) :
      Step members s (.send (.call voter (.accept ballot p)))
        { s with net := Wire.begin (.call voter (.accept ballot p)) :: s.net }
  | wireSend {s} (p : Packet) (a : WireEffect) (out inbox : List WireEffect)
      (available : (⟨p, a :: out, inbox⟩ : Wire) ∈ s.net) :
      Step members s (.wireSend a) { s with net := ⟨p, out, inbox⟩ :: s.net.erase ⟨p, a :: out, inbox⟩ }
  | wireReceive {s} (p : Packet) (a : WireEffect) (out inbox : List WireEffect)
      (available : (⟨p, out, a :: inbox⟩ : Wire) ∈ s.net)
      (written : inbox.length + 1 ≤ out.length → a = .timeout) :
      Step members s (.wireReceive a) { s with net := ⟨p, out, inbox⟩ :: s.net.erase ⟨p, out, a :: inbox⟩ }
  | localDelivery {s} (p : Packet) (available : Wire.begin p ∈ s.net) :
      Step members s .localDelivery
        { s with net := Wire.done p :: s.net.erase (Wire.begin p) }
  | dropPacket {s} (w : Wire) (available : w ∈ s.net) :
      Step members s .dropPacket { s with net := s.net.erase w }
  | duplicate {s} (w : Wire) (available : w ∈ s.net) :
      Step members s .duplicate { s with net := Wire.begin w.packet :: s.net }
  | delay {s} : Step members s .delay s
  | refuse {s} (w : Wire) (available : w ∈ s.net) :
      Step members s .refuse { s with net := s.net.erase w }
  | startJob {s} (voter : Voter) (request : Request)
      (available : Wire.done (.call voter request) ∈ s.net)
      (ready : s.voters voter = .ready) (admitted : CanStart members s voter request) :
      Step members s (.startJob voter) { s with
        voters := update s.voters voter (.first request writeSlot)
        net := s.net.erase (Wire.done (.call voter request)) }
  | firstWrite {s} (voter : Voter) (request : Request) (a : DiskEffect) (rest : List DiskEffect)
      (work : s.voters voter = .first request (a :: rest)) :
      Step members s (.disk voter a) { s with voters := update s.voters voter (.first request rest) }
  | firstSync {s} (voter : Voter) (request : Request) (core : Core) (reply : Packet)
      (effects : List DiskEffect) (work : s.voters voter = .first request [])
      (saved : Save members s voter request core reply effects) :
      Step members s (.disk voter .fileSync) { s with
        core := core
        voters := update s.voters voter (.mirror reply effects) }
  | mirrorEffect {s} (voter : Voter) (reply : Packet) (a : DiskEffect) (rest : List DiskEffect)
      (work : s.voters voter = .mirror reply (a :: rest)) :
      Step members s (.disk voter a) { s with voters := update s.voters voter (.mirror reply rest) }
  | reply {s} (voter : Voter) (reply : Packet) (done : s.voters voter = .mirror reply []) :
      Step members s (.reply voter) { s with
        voters := update s.voters voter .ready
        net := Wire.begin reply :: s.net }
  | collectPromise {s} (voter : Voter) (ballot : Ballot) (r : Round)
      (report : Option Value) (round : s.rounds ballot = some r) (phase : r.phase = .preparing)
      (peer : voter ∈ r.peers) (new : voter ∉ r.promises)
      (faithful : (s.core.media voter).replies ballot = some report)
      (packet : Wire.done (.promise voter ballot report.isSome) ∈ s.net) :
      Step members s (.collect ballot voter)
        { s.withRound ballot { r with promises := voter :: r.promises } with
          net := s.net.erase (Wire.done (.promise voter ballot report.isSome)) }
  | prepared {s} (ballot : Ballot) (r : Round) (prep : Preparation)
      (round : s.rounds ballot = some r) (phase : r.phase = .preparing)
      (taken : prep.voters = r.promises) (fresh : s.core.prepared ballot = none)
      (quorum : ExactQuorum members prep.voters)
      (reports : BoundReports s.core ballot prep)
      (ranked : RecoveryFold (prep.voters.map prep.report) prep.winner)
      (earlier : ∀ v ∈ prep.voters, ∀ vote, prep.report v = some vote → vote.ballot < ballot) :
      Step members s (.prepared ballot)
        { s.withRound ballot { r with phase := .prepared } with
          core := { s.core with prepared := update s.core.prepared ballot (some prep) } }
  | issue {s} (ballot : Ballot) (r : Round) (prep : Preparation) (p : Proposal)
      (round : s.rounds ballot = some r) (phase : r.phase = .prepared)
      (prepared : s.core.prepared ballot = some prep) (fresh : s.core.issued ballot = none)
      (extendsSeed : ExtendsSeed prep p) (replay : r.operation ≠ .choose → p.history = prep.seed)
      (nonempty : p.history ≠ []) (unsealed : p.history ≠ prep.seed → OrderedCohort.may_extend (s.sealOf prep.seed)) :
      Step members s (.issue ballot)
        { s.withRound ballot { r with phase := .accepting } with
          core := { s.core with issued := update s.core.issued ballot (some p) } }
  | collectVote {s} (voter : Voter) (ballot : Ballot) (r : Round) (p : Proposal) (packet : Packet)
      (round : s.rounds ballot = some r) (phase : r.phase = .accepting)
      (promised : voter ∈ r.promises) (new : voter ∉ r.votes)
      (issued : s.core.issued ballot = some p) (bound : MatchesVote voter ballot p packet)
      (received : Wire.done packet ∈ s.net) :
      Step members s (.collect ballot voter)
        { s.withRound ballot { r with votes := voter :: r.votes } with
          net := s.net.erase (Wire.done packet) }
  | certificate {s} (ballot : Ballot) (r : Round) (p : Proposal)
      (round : s.rounds ballot = some r) (phase : r.phase = .accepting)
      (issued : s.core.issued ballot = some p) (quorum : ExactQuorum members r.votes) :
      Step members s (.certificate ballot p.history) (s.withRound ballot { r with phase := .confirmed })
  | coordinatorCrash {s} (ballot : Ballot) (r : Round) (round : s.rounds ballot = some r) :
      Step members s (.coordinatorCrash ballot) (s.withRound ballot { r with phase := .closed })
  | finish {s} (ballot : Ballot) (r : Round) (round : s.rounds ballot = some r)
      (output : r.phase = .confirmed ∨ (r.phase = .prepared ∧ r.operation ≠ .choose ∧
        ∃ prep, s.core.prepared ballot = some prep ∧ prep.seed = [])) :
      Step members s (.finish ballot) (s.withRound ballot { r with phase := .closed })
  | exportSeed {s} (ballot : Ballot) (r : Round) (p : Proposal) (target image : Nat)
      (round : s.rounds ballot = some r) (phase : r.phase = .confirmed)
      (repair : r.operation = .repairSeed) (issued : s.core.issued ballot = some p)
      (quorum : ExactQuorum members r.votes) (named : OrderedCohort.matches_chosen_seal (s.sealOf p.history) target)
      (successor : target ≠ s.scope) :
      Step members s (.exportSeed ballot ⟨s.scope, target, image, p.history⟩)
        (s.withRound ballot { r with phase := .closed })
  | beginInstall {s} (v : Voter) (authorized received : RepairArtifact)
      (member : v ∈ members) (uninstalled : s.voters v = .uninstalled)
      (expected : s.repair = some authorized) (exactImage : ExactImage authorized received) :
      Step members s (.beginInstall v) { s with voters := update s.voters v (.installing installEffects) }
  | installEffect {s} (v : Voter) (effect : DiskEffect) (rest : List DiskEffect)
      (work : s.voters v = .installing (effect :: rest)) :
      Step members s (.disk v effect) { s with voters := update s.voters v (.installing rest) }
  | finishInstall {s} (v : Voter) (base : Proposal)
      (finished : s.voters v = .installing [])
      (issued : s.core.issued bootstrapBallot = some base)
      (floor : AcceptGuard (s.core.media v).promised bootstrapBallot) :
      Step members s (.installed v)
        { s with voters := update s.voters v .ready
                 core := { s.core with media := update s.core.media v (acceptVote (s.core.media v) ⟨bootstrapBallot, base.history⟩) } }
  | crashInstall {s} (v : Voter) (remaining : List DiskEffect)
      (installing : s.voters v = .installing remaining ∨ s.voters v = .uninstalled) :
      Step members s (.voterCrash v) { s with voters := update s.voters v .uninstalled }
  | voterCrash {s} (voter : Voter) (installed : s.voters voter ≠ .uninstalled)
      (noInstall : ∀ todo, s.voters voter ≠ .installing todo) :
      Step members s (.voterCrash voter)
        { s with voters := update s.voters voter (.offline (crashCandidate (s.voters voter))) }
  | beginRestart {s} (voter : Voter) (candidate : Option Request)
      (offline : s.voters voter = .offline candidate) :
      Step members s (.restart voter) { s with voters := update s.voters voter (.reopening candidate reopen) }
  | reopenEffect {s} (voter : Voter) (candidate : Option Request) (a : DiskEffect) (rest : List DiskEffect)
      (work : s.voters voter = .reopening candidate (a :: rest)) :
      Step members s (.disk voter a) { s with voters := update s.voters voter (.reopening candidate rest) }
  | reopenPrior {s} (voter : Voter) (candidate : Option Request)
      (checked : s.voters voter = .reopening candidate []) :
      Step members s (.restart voter) { s with voters := update s.voters voter .ready }
  | reopenCandidate {s} (voter : Voter) (request : Request) (core : Core) (reply : Packet)
      (effects : List DiskEffect) (checked : s.voters voter = .reopening (some request) [])
      (saved : Save members s voter request core reply effects) :
      Step members s (.restart voter) { s with core := core, voters := update s.voters voter .ready }

theorem step_refines_core (step : Step members before action after) :
    AsyncPrefix.Step members before.core after.core := by
  cases step with
  | prepared b _ prep _ _ _ fresh quorum reports folded earlier =>
    exact .prepareQuorum b prep fresh quorum reports (fold_is_ranked folded earlier)
  | issue b _ prep p _ _ prepared fresh extendsSeed _ _ _ =>
    exact .issue b prep p prepared fresh extendsSeed
  | finishInstall v base _ issued floor => exact .saveAccept v bootstrapBallot base issued floor
  | firstSync _ _ _ _ _ _ saved | reopenCandidate _ _ _ _ _ _ saved => exact save_refines saved
  | _ => exact .stutter

def abstractLedger (members : List Voter) (s : State) : Ledger Voter Nat := ledger members s.core

def abstractAcceptor (s : State) (voter : Voter) : DurableAcceptor.State Nat := s.core.media voter

inductive Reachable (members : List Voter) : State → Prop
  | initial {scope sealOf} (distinct : members.Nodup) : Reachable members (State.initial scope sealOf)
  | seeded {seed sealOf} (distinct : members.Nodup) (roster : ExactQuorum members members)
      (successor : seed.source ≠ seed.target) :
      Reachable members (State.seeded members seed sealOf)
  | extend : Reachable members before → Step members before action after → Reachable members after

/-- Successful vote packets originate in the durable effect and can only
be moved or copied by transport. -/
def PacketEvidence (c : Core) : Packet → Prop
  | .vote voter ballot image readBack mirrored =>
      ∃ p, c.issued ballot = some p ∧ p.image = image ∧ p.readBack = readBack ∧
        mirrored = true ∧ (c.media voter).votes ⟨ballot, p.history⟩
  | _ => True

private theorem packet_persists (step : AsyncPrefix.Step members before after)
    (evidence : PacketEvidence before packet) : PacketEvidence after packet := by
  cases packet <;> try exact True.intro
  obtain ⟨p, issued, image, readBack, mirrored, voted⟩ := evidence
  exact ⟨p, issue_persists step issued, image, readBack, mirrored, vote_persists step voted⟩

private theorem save_creates_packet_evidence {s : State}
    (save : Save members s voter request core reply effects) : PacketEvidence core reply := by
  cases save with
  | promise b _ _ => unfold promisePacket; split <;> exact True.intro
  | accept b p issued _ => exact ⟨p, issued, rfl, rfl, rfl, by simp [update, acceptVote]⟩

def NetworkEvidence (s : State) : Prop :=
  ∀ w ∈ s.net, PacketEvidence s.core w.packet

def PendingEvidence (s : State) : Prop :=
  ∀ v p todo, s.voters v = .mirror p todo → PacketEvidence s.core p

private theorem modes_keep_evidence {s : State} {next : VoterMode} {c : Core}
    (old : PendingEvidence s) (core : AsyncPrefix.Step members s.core c)
    (new : ∀ p todo, next = .mirror p todo → PacketEvidence c p) :
    PendingEvidence { s with voters := update s.voters voter next, core := c } := by
  intro v p todo mode
  by_cases eq : v = voter
  · exact new p todo (by simpa [update, eq] using mode)
  · exact packet_persists core (old v p todo (by simpa [update, eq] using mode))

private theorem transit {s : State} {w : Wire} (old : NetworkEvidence s) (available : w ∈ s.net)
    (same : w.packet = next.packet) :
    NetworkEvidence { s with net := next :: s.net.erase w } := by
  intro observed present
  rcases List.mem_cons.mp present with rfl | retained
  · exact same ▸ old w available
  · exact old observed (List.mem_of_mem_erase retained)

private theorem add_packet {s : State} (old : NetworkEvidence s)
    (valid : PacketEvidence s.core w.packet) : NetworkEvidence { s with net := w :: s.net } := by
  intro observed present
  rcases List.mem_cons.mp present with rfl | retained
  · exact valid
  · exact old observed retained

private theorem erase_packet {s : State} (old : NetworkEvidence s) :
    NetworkEvidence { s with net := s.net.erase w } :=
  fun x mem => old x (List.mem_of_mem_erase mem)

private theorem pending_preserved (step : Step members before action after)
    (prior : PendingEvidence before) : PendingEvidence after := by
  have core := step_refines_core step
  cases step <;> try (exact fun v p todo mode => packet_persists core (prior v p todo mode))
  case mirrorEffect v p a rest work =>
    apply modes_keep_evidence prior core
    intro packet todo eq
    cases eq
    exact prior v p (a :: rest) work
  case firstSync v request c reply effects work saved =>
    apply modes_keep_evidence prior core
    intro p todo eq
    cases eq
    exact save_creates_packet_evidence saved
  all_goals apply modes_keep_evidence prior core; intro p todo impossible; cases impossible

private theorem network_preserved (step : Step members before action after)
    (pending : PendingEvidence before) (prior : NetworkEvidence before) : NetworkEvidence after := by
  have core := step_refines_core step
  cases step <;> first
    | exact fun w present => packet_persists core (prior w present)
    | exact add_packet prior True.intro
    | exact erase_packet prior
    | skip
  case wireSend p a out inbox available => exact transit prior available rfl
  case wireReceive p a out inbox available written => exact transit prior available rfl
  case localDelivery p available => exact transit prior available rfl
  case duplicate w available => exact add_packet prior (prior w available)
  case reply v p done => exact add_packet prior (pending v p [] done)

def CountedEvidence (s : State) : Prop :=
  ∀ b r, s.rounds b = some r → ∀ v ∈ r.votes,
    ∃ p, s.core.issued b = some p ∧ (s.core.media v).votes ⟨b, p.history⟩

private theorem rounds_keep_evidence {s : State} {r : Round} {b : Ballot} {c : Core}
    (old : CountedEvidence s) (core : AsyncPrefix.Step members s.core c)
    (new : ∀ v ∈ r.votes, ∃ p, c.issued b = some p ∧ (c.media v).votes ⟨b, p.history⟩) :
    CountedEvidence { s.withRound b r with core := c } := by
  intro ballot round lookup voter present
  by_cases same : ballot = b
  · subst ballot
    simp [State.withRound, update] at lookup
    subst round
    exact new voter present
  · obtain ⟨p, issued, voted⟩ := old ballot round
      (by simpa [State.withRound, update, same] using lookup) voter present
    exact ⟨p, issue_persists core issued, vote_persists core voted⟩

private theorem counted_preserved (step : Step members before action after)
    (packets : NetworkEvidence before) (prior : CountedEvidence before) : CountedEvidence after := by
  have core := step_refines_core step
  have preserved := fun b r lookup v present =>
    Exists.elim (prior b r lookup v present) (fun p ⟨issued, voted⟩ =>
      Exists.intro p (And.intro (issue_persists core issued) (vote_persists core voted)))
  cases step <;> try exact preserved
  case start b r fresh nonzero empty peers =>
    apply rounds_keep_evidence prior core
    intro v counted
    rw [empty] at counted
    exact False.elim (List.not_mem_nil counted)
  case replace old new priorRound r occupied fresh newer empty peers =>
    have retired := rounds_keep_evidence (b := old) (r := { priorRound with phase := .closed })
      prior (AsyncPrefix.Step.stutter (members := members))
      (fun v mem => prior _ priorRound occupied v mem)
    apply rounds_keep_evidence retired core
    intro v counted
    rw [empty] at counted
    exact False.elim (List.not_mem_nil counted)
  case collectVote voter ballot r p packet round phase promised new issued bound received =>
    apply rounds_keep_evidence prior core
    intro v counted
    rcases List.mem_cons.mp counted with rfl | older
    · have evidence := packets (Wire.done packet) received
      change PacketEvidence _ packet at evidence
      rw [bound] at evidence
      obtain ⟨other, original, _, _, _, voted⟩ := evidence
      rw [issued] at original
      cases original
      exact ⟨p, issued, voted⟩
    · exact prior ballot r round v older
  case collectPromise v b r report lookup phase peer new faithful packet =>
    exact rounds_keep_evidence prior core (preserved b r lookup)
  case prepared b r prep lookup phase taken fresh quorum reports folded earlier =>
    exact rounds_keep_evidence prior core (preserved b r lookup)
  case issue b r prep p lookup phase prepared fresh extendsSeed replay nonempty unsealed =>
    exact rounds_keep_evidence prior core (preserved b r lookup)
  case certificate b r p lookup phase issued quorum =>
    exact rounds_keep_evidence prior core (preserved b r lookup)
  case exportSeed b r p target image lookup phase repair issued quorum named successor =>
    exact rounds_keep_evidence prior core (preserved b r lookup)
  case coordinatorCrash b r lookup =>
    exact rounds_keep_evidence prior core (preserved b r lookup)
  case finish b r lookup output =>
    exact rounds_keep_evidence prior core (preserved b r lookup)

structure IOEvidence (s : State) : Prop where
  pending : PendingEvidence s
  network : NetworkEvidence s
  counted : CountedEvidence s

theorem io_evidence (run : Reachable members s) : IOEvidence s := by
  induction run with
  | initial => exact ⟨by simp [PendingEvidence, State.initial], by simp [NetworkEvidence, State.initial],
      by simp [CountedEvidence, State.initial]⟩
  | seeded =>
    exact ⟨by simp [PendingEvidence, State.seeded], by simp [NetworkEvidence, State.seeded], by
      intro b r received v counted
      by_cases isBase : b = bootstrapBallot
      · subst b
        simp [State.seeded, update] at received
        subst r
        simp at counted
      · simp [State.seeded, update, isBase] at received⟩
  | extend _ step ih =>
    exact ⟨pending_preserved step ih.pending, network_preserved step ih.pending ih.network,
      counted_preserved step ih.network ih.counted⟩

theorem reached_valid (run : Reachable members s) : Valid members s.core := by
  induction run with
  | initial => exact initial_valid
  | seeded _ quorum _ => exact bootstrap_valid quorum
  | extend _ step prior => exact step_preserves_valid prior (step_refines_core step)

theorem step_refines_acceptor (run : Reachable members before) (step : Step members before action after)
    (voter : Voter) : DurableAcceptor.Step (abstractAcceptor before voter) (abstractAcceptor after voter) :=
  step_refines_media (reached_valid run) (step_refines_core step) voter

theorem step_projects_ledger (run : Reachable members before) (step : Step members before action after) :
    LedgerStep (abstractLedger members before) (abstractLedger members after) :=
  step_refines_ledger (reached_valid run) (step_refines_core step)

theorem choice_survives_step (step : Step members before action after)
    (chosen : Chosen (abstractLedger members before) ballot history) :
    Chosen (abstractLedger members after) ballot history :=
  choice_persists (step_refines_core step) chosen

theorem reached_rules (run : Reachable members s) : Rules (abstractLedger members s) :=
  valid_supplies_rules (reached_valid run)

theorem a_closed_round_cannot_count_a_reply (step : Step members before (.collect ballot voter) after)
    (round : before.rounds ballot = some closed) (phase : closed.phase = .closed) : False := by
  cases step with
  | collectPromise v b r report lookedUp preparing _ _ _ _ =>
    rw [round] at lookedUp
    cases lookedUp
    simp [phase] at preparing
  | collectVote v b r p packet lookedUp accepting _ _ _ _ _ =>
    rw [round] at lookedUp
    cases lookedUp
    simp [phase] at accepting

theorem exact_certificate_is_chosen (run : Reachable members before)
    (step : Step members before (.certificate ballot history) after) :
    Chosen (abstractLedger members after) ballot history := by
  cases step with
  | certificate ballot r p round _ issued quorum =>
    apply checked_certificate_is_chosen r.votes
    · exact quorum
    · intro v mem
      obtain ⟨other, found, voted⟩ := (io_evidence run).counted ballot r round v mem
      rw [issued] at found
      cases found
      exact voted

theorem chosen_prefixes_compatible (run : Reachable members s)
    (first : Chosen (abstractLedger members s) a left) (second : Chosen (abstractLedger members s) b right) :
    left <+: right ∨ right <+: left :=
  every_chosen_prefix_agrees (reached_rules run) first second

theorem one_choice_per_position (run : Reachable members s)
    (first : Chosen (abstractLedger members s) a left) (second : Chosen (abstractLedger members s) b right)
    {position command other : Nat}
    (x : left[position]? = some command) (y : right[position]? = some other) : command = other :=
  any_two_certificates_agree_at_position (reached_rules run) first second x y

theorem later_recovery_preserves_chosen_prefix (run : Reachable members s)
    (chosen : Chosen (abstractLedger members s) old history) (newer : old < new)
    (prepared : s.core.prepared new = some prep) : history <+: prep.seed := by
  have inherits := later_ballot_inherits_chosen_prefix (reached_rules run) chosen new newer
    (by simp [abstractLedger, ledger, prepared])
  simpa [seed, abstractLedger, ledger, prepared, Preparation.seed] using inherits

theorem exported_seed_is_chosen (run : Reachable members before)
    (step : Step members before (.exportSeed ballot artifact) after) :
    Chosen (abstractLedger members before) ballot artifact.history := by
  cases step with
  | exportSeed b r p target image lookup _ _ issued quorum _ _ =>
    apply checked_certificate_is_chosen r.votes
    · exact quorum
    · intro v present
      obtain ⟨other, found, voted⟩ := (io_evidence run).counted ballot r lookup v present
      rw [issued] at found
      cases found
      exact voted

theorem repair_issue_is_exact {artifact : RepairArtifact} (run : Reachable members s)
    (repair : s.repair = some artifact) : s.core.issued bootstrapBallot = some artifact.proposal := by
  induction run with
  | initial => simp [State.initial] at repair
  | seeded =>
    simp [State.seeded] at repair
    subst artifact
    simp [State.seeded, bootstrap, update]
  | @extend before action after _ step ih =>
    have same : after.repair = before.repair := by cases step <;> rfl
    exact issue_persists (step_refines_core step) (ih (same ▸ repair))

theorem install_casts_exact_vote {artifact : RepairArtifact} (run : Reachable members before)
    (step : Step members before (.installed voter) after) (repair : before.repair = some artifact) :
    (abstractAcceptor after voter).votes ⟨bootstrapBallot, artifact.history⟩ := by
  have known := repair_issue_is_exact run repair
  cases step with
  | finishInstall v base _ issued _ =>
    rw [issued] at known
    cases known
    simp [abstractAcceptor, update, acceptVote, RepairArtifact.proposal]

theorem later_recovery_keeps_exported_history
    (source : Reachable sourceMembers before)
    (exported : Step sourceMembers before (.exportSeed sealBallot artifact) after)
    (destination : Reachable destinationMembers s) (repair : s.repair = some artifact)
    (prior : Chosen (abstractLedger sourceMembers before) earlier history) (older : earlier < sealBallot)
    (installed : List Voter) (quorum : ExactQuorum destinationMembers installed)
    (votes : ∀ v ∈ installed, ∃ h, (abstractAcceptor s v).votes ⟨bootstrapBallot, h⟩)
    (prepared : s.core.prepared ballot = some prep) (later : bootstrapBallot < ballot) :
    history <+: prep.seed := by
  have exactBase := repair_issue_is_exact destination repair
  have validDestination := reached_valid destination
  have bootstrapChoice : Chosen (abstractLedger destinationMembers s) bootstrapBallot artifact.history := by
    apply checked_certificate_is_chosen installed
    · exact quorum
    · intro v present
      obtain ⟨h, voted⟩ := votes v present
      obtain ⟨p, issued, sameHistory⟩ := validDestination.votes v ⟨bootstrapBallot, h⟩ voted
      change s.core.issued bootstrapBallot = some p at issued
      rw [exactBase] at issued
      cases issued
      change artifact.proposal.history = h at sameHistory
      rw [← sameHistory] at voted
      exact voted
  have inherits := later_recovery_preserves_chosen_prefix destination bootstrapChoice later prepared
  cases exported with
  | exportSeed b r p target image lookup _ _ issued _ _ _ =>
    have valid := reached_valid source
    obtain ⟨oldPrep, active, extendsSeed⟩ := valid.issued sealBallot p issued
    have priorInSeed := later_recovery_preserves_chosen_prefix source prior older active
    exact priorInSeed.trans (extendsSeed.trans inherits)

#print axioms io_evidence
#print axioms step_refines_core
#print axioms step_refines_acceptor
#print axioms step_projects_ledger
#print axioms choice_survives_step
#print axioms a_closed_round_cannot_count_a_reply
#print axioms exact_certificate_is_chosen
#print axioms chosen_prefixes_compatible
#print axioms one_choice_per_position
#print axioms later_recovery_preserves_chosen_prefix
#print axioms exported_seed_is_chosen
#print axioms install_casts_exact_vote
#print axioms later_recovery_keeps_exported_history

end Logkeeper.AsyncGroup
