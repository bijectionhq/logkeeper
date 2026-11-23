import CoreReference

set_option warningAsError true

namespace CorePrograms

open CoreReference (stream)
open ChosenReplay (Image Rules Frame Command Applied)

def lineage : ChosenReplay.Lineage := ⟨7, 1⟩
def first : Kernel.Writer := ⟨⟨1, 1⟩, 1, 10⟩
def successor : Kernel.Writer := ⟨first.placement, 2, 11⟩
def grant : ChosenReplay.Grant Unit := ⟨9, first, ()⟩
def entry : Kernel.Entry Nat := ⟨1, 42⟩

def initial : Image 1 Nat :=
  ⟨⟨⟨Kernel.initial first, ⟨0, fun _ => none⟩, none, none⟩, 0⟩, ⟨fun _ => none, fun _ => 0⟩⟩

structure PaidFixture (rules : Rules 1 Nat Unit) : Prop where
  grant : rules.grant lineage CorePrograms.grant
  owner : rules.append.owner 9 = 7
  bytes : rules.append.regional.layout.bytes 9 = 2
  costFirst : rules.append.cost 42 = 1
  recoveryRoom : 1 ≤ (rules.append.regional.limits 7).recovery
  retentionRoom : 1 ≤ (rules.append.regional.limits 7).retained

def frame (position : Nat) (command : Command 1 Nat Unit) : Frame 1 Nat Unit :=
  ⟨lineage, position, command⟩

def append (writer : Kernel.Writer) (lsn offset payload : Nat) : Command 1 Nat Unit :=
  .append ⟨9, writer, lsn, offset, payload, ()⟩

def direct (command : OrderedApplication.Command Nat) : Command 1 Nat Unit :=
  .source (.stream command)

def start : List (Frame 1 Nat Unit) :=
  [frame 1 (.install grant), frame 2 (append first 0 0 42)]

def committed : Image 1 Nat :=
  ⟨⟨{initial.source.core with stream := {stream initial with history := [entry]}}, 2⟩,
    ⟨fun v => if v = 9 then some ⟨7, first.placement, 1, 1⟩ else none,
     fun s => if s = 7 then 9 else 0⟩⟩

def bootReplies : List (Applied 1 Nat Unit) :=
  [⟨frame 1 (.install grant), .accepted⟩,
   ⟨frame 2 (append first 0 0 42), .stream (.appended 0 entry)⟩]

private theorem replayNext (rules : Rules 1 Nat Unit) (before after : Image 1 Nat)
    (position : Nat) (command : Command 1 Nat Unit) (reply : UnifiedSource.Reply Nat)
    (next : position = before.source.position + 1)
    (effect : ChosenReplay.decide rules lineage before (frame position command) = (after, reply))
    (rest : List (Frame 1 Nat Unit)) :
    ChosenReplay.replay rules lineage before (frame position command :: rest) =
      (ChosenReplay.replay rules lineage after rest).map (fun tail => (tail.1, ⟨frame position command, reply⟩ :: tail.2)) := by
  have current : ChosenReplay.eligibleFrame lineage before (frame position command) := ⟨rfl, next⟩
  simp only [ChosenReplay.replay, ite_eq_left current, effect]

private def alter (before : Image 1 Nat) (newStream : Kernel.State Nat) : Image 1 Nat :=
  { before with source := ⟨{before.source.core with stream := newStream}, before.source.position + 1⟩ }

private theorem runRoutine (rules : Rules 1 Nat Unit) (before : Image 1 Nat) {position : Nat}
    {command : OrderedApplication.Command Nat} {state : Kernel.State Nat} {reply : OrderedApplication.Outcome Nat}
    (routine : UnifiedSource.Routine command)
    (effect : OrderedApplication.decideCommand (rules.append.regional.limits lineage.stream)
      (stream before) command = (state, reply))
    (history : state.history = (stream before).history) :
    ChosenReplay.decide rules lineage before (frame position (direct command)) =
      (alter before state, .stream reply) := by
  change OrderedApplication.decideCommand (rules.append.regional.limits lineage.stream)
    before.source.core.stream command = (state, reply) at effect
  change state.history = before.source.core.stream.history at history
  simp [ChosenReplay.decide, frame, direct, UnifiedSource.decide, routine, effect, history, alter]

private def opened : Image 1 Nat := ChosenReplay.installWindow lineage initial grant

private def appendResult (outcome : FundedAppend.Source 1 Nat × FundedAppend.Book × UnifiedSource.Reply Nat) :
    Image 1 Nat × UnifiedSource.Reply Nat :=
  (⟨outcome.1, outcome.2.1⟩, outcome.2.2)

theorem a_funded_install_and_append_return_the_exact_record (rules : Rules 1 Nat Unit)
    (paid : PaidFixture rules) :
    ChosenReplay.replay rules lineage initial start = some (committed, bootReplies) := by
  have grantAllowed : ChosenReplay.InstallAllowed rules lineage initial grant :=
    ⟨paid.grant, paid.owner, by decide, rfl, rfl⟩
  have installs : ChosenReplay.decide rules lineage initial (frame 1 (.install grant)) = (opened, .accepted) := by
    simp [ChosenReplay.decide, frame, grantAllowed, opened]
  let request : FundedAppend.Request Nat Unit := ⟨9, first, 0, 0, 42, ()⟩
  let current : FundedAppend.Window := ⟨7, first.placement, 0, 0⟩
  have room : OrderedApplication.AppendAllowed (rules.append.regional.limits lineage.stream)
      (stream opened) first 0 := by
    exact ⟨rfl, rfl, paid.recoveryRoom, paid.retentionRoom⟩
  have installed : opened.book.windows request.version = some current := by
    simp [opened, ChosenReplay.installWindow, initial, grant, SnapshotAdmission.setSlot, current, request, lineage,
      Kernel.initial]
  have allowed : FundedAppend.LocalChecks (ChosenReplay.frameRules rules (frame 2 (append first 0 0 42)))
      lineage.stream opened.source opened.book current request := by
    refine ⟨rfl, ?_, rfl, rfl, rfl, ?_, ?_, ⟨rfl, rfl⟩, room⟩
    · simp [opened, ChosenReplay.installWindow, initial, grant, SnapshotAdmission.setSlot, request, lineage]
    · change 0 < rules.append.cost 42
      rw [paid.costFirst]
      decide
    · change 0 + rules.append.cost 42 ≤ rules.append.regional.layout.bytes 9
      rw [paid.costFirst, paid.bytes]
      decide
  have appends : ChosenReplay.decide rules lineage opened (frame 2 (append first 0 0 42)) =
      (committed, .stream (.appended 0 entry)) := by
    have evaluated := FundedAppend.eligible_append_uses_the_original_ordered_reducer installed allowed
    change appendResult (FundedAppend.decide (ChosenReplay.frameRules rules (frame 2 (append first 0 0 42)))
      lineage.stream opened.source opened.book request) = _
    rw [evaluated]
    have verified : OrderedApplication.AppendAllowed (rules.append.regional.limits 7)
        {authority := .active first} first 0 := room
    simp [opened, initial, ChosenReplay.installWindow, ChosenReplay.advancePosition,
      grant, request, lineage, committed, entry, stream, Kernel.initial,
      FundedAppend.advanceWindow, FundedAppend.appendCommand, UnifiedSource.replay, UnifiedSource.decide,
      UnifiedSource.Routine, OrderedApplication.decideCommand, verified, paid.costFirst, appendResult,
      ChosenReplay.frameRules, current]
    refine ⟨⟨rfl, ?_, rfl⟩, rfl⟩
    funext query
    by_cases same : query = 9 <;> simp [SnapshotAdmission.setSlot, same]
  simp only [start]
  rw [replayNext rules initial opened 1 (.install grant) .accepted rfl installs,
    replayNext rules opened committed 2 (append first 0 0 42) (.stream (.appended 0 entry)) rfl appends]
  rfl

def fenced : Image 1 Nat :=
  alter (alter committed (stream committed)) {stream committed with authority := .active successor}

theorem a_read_and_higher_epoch_fence_preserve_the_committed_cut (rules : Rules 1 Nat Unit) :
    ChosenReplay.replay rules lineage committed
      [frame 3 (direct (.read first 700)), frame 4 (direct (.fence first successor))] =
      some (fenced,
       [⟨frame 3 (direct (.read first 700)), .stream (.readCut 700 1)⟩,
        ⟨frame 4 (direct (.fence first successor)), .stream (.installed 1)⟩]) := by
  let observed := alter committed (stream committed)
  have reads := runRoutine rules committed (position := 3) (command := .read first 700)
    (state := stream committed) (reply := .readCut 700 1) trivial
    (by simp [OrderedApplication.decideCommand, Kernel.barrier, stream, committed, initial, Kernel.initial]) rfl
  have fences := runRoutine rules observed (position := 4) (command := .fence first successor)
    (state := stream fenced) (reply := .installed 1) trivial
    (by simp [OrderedApplication.decideCommand, observed, fenced, alter, stream, committed, initial,
      Kernel.initial, first, successor]) rfl
  rw [replayNext rules committed observed 3 _ _ rfl reads,
    replayNext rules observed fenced 4 _ _ rfl fences]
  rfl

theorem a_delayed_writer_is_refused_in_the_funded_window (rules : Rules 1 Nat Unit) :
    ChosenReplay.decide rules lineage fenced (frame 5 (append first 1 1 43)) =
      (alter fenced (stream fenced), .refused) := by
  let request : FundedAppend.Request Nat Unit := ⟨9, first, 1, 1, 43, ()⟩
  let current : FundedAppend.Window := ⟨7, first.placement, 1, 1⟩
  have stored : fenced.book.windows request.version = some current := by rfl
  have stale : ¬ FundedAppend.LocalChecks (ChosenReplay.frameRules rules (frame 5 (append first 1 1 43)))
      lineage.stream fenced.source fenced.book current request := by
    intro approves
    have owner := approves.streamAllowed.1
    change Kernel.Authority.active successor = Kernel.Authority.active first at owner
    simp [successor, first] at owner
  change appendResult (FundedAppend.decide (ChosenReplay.frameRules rules (frame 5 (append first 1 1 43)))
    lineage.stream fenced.source fenced.book request) = _
  simp [FundedAppend.decide, stored, stale, alter, stream, appendResult]

theorem retirement_and_later_barrier_share_the_same_replay (rules : Rules 1 Nat Unit) :
    ∃ final replies, ChosenReplay.replay rules lineage fenced
      [frame 5 (append first 1 1 43), frame 6 (.source (.retire successor)),
       frame 7 (direct (.read successor 701))] = some (final, replies) ∧
    (stream final).authority = .retired ∧ (stream final).history = [entry] ∧ (stream final).firstRetained = 0 ∧
    replies.map Applied.reply = [.refused, .accepted, .stream .refused] := by
  let afterDelay := alter fenced (stream fenced)
  let retired := alter afterDelay {stream afterDelay with authority := .retired}
  have shuts : ChosenReplay.decide rules lineage afterDelay (frame 6 (.source (.retire successor))) =
      (retired, .accepted) := by
    simp [ChosenReplay.decide, frame, retired, afterDelay, fenced, stream, alter, committed, initial, UnifiedSource.decide]
  have reads := runRoutine rules retired (position := 7) (command := .read successor 701)
    (state := stream retired) (reply := .refused) trivial
    (by simp [OrderedApplication.decideCommand, Kernel.barrier, retired, alter, stream]) rfl
  refine ⟨alter retired (stream retired),
    [⟨frame 5 (append first 1 1 43), .refused⟩, ⟨frame 6 (.source (.retire successor)), .accepted⟩,
     ⟨frame 7 (direct (.read successor 701)), .stream .refused⟩],
    ?_, rfl, rfl, rfl, rfl⟩
  rw [replayNext rules fenced afterDelay 5 _ _ rfl (a_delayed_writer_is_refused_in_the_funded_window rules),
    replayNext rules afterDelay retired 6 _ _ rfl shuts, replayNext rules retired _ 7 _ _ rfl reads]
  rfl

theorem one_replay_runs_the_funded_writer_lifecycle (rules : Rules 1 Nat Unit) (paid : PaidFixture rules) :
    ∃ final records, ChosenReplay.replay rules lineage initial
      (start ++ ([frame 3 (direct (.read first 700)), frame 4 (direct (.fence first successor))] ++
        [frame 5 (append first 1 1 43), frame 6 (.source (.retire successor)),
         frame 7 (direct (.read successor 701))])) = some (final, records) ∧
      (stream final).authority = .retired ∧ Kernel.MatchesReceipt (stream final) 0 entry ∧
      records.map Applied.reply =
        [.accepted, .stream (.appended 0 entry), .stream (.readCut 700 1), .stream (.installed 1),
         .refused, .accepted, .stream .refused] := by
  have boot := a_funded_install_and_append_return_the_exact_record rules paid
  have fences := a_read_and_higher_epoch_fence_preserve_the_committed_cut rules
  obtain ⟨final, closing, closed, terminal, history, retained, replies⟩ :=
    retirement_and_later_barrier_share_the_same_replay rules
  refine ⟨final, bootReplies ++ ([⟨frame 3 (direct (.read first 700)), .stream (.readCut 700 1)⟩,
    ⟨frame 4 (direct (.fence first successor)), .stream (.installed 1)⟩] ++ closing), ?_, terminal, ?_, ?_⟩
  · rw [ChosenReplay.replay_after_a_certified_prefix _ _ _ _ _ _ boot,
      ChosenReplay.replay_after_a_certified_prefix _ _ _ _ _ _ fences, closed]
    rfl
  · exact ⟨by simp [Kernel.RecoverableAt, retained], by rw [history]; rfl⟩
  · simp [bootReplies, replies]

def published : Image 1 Nat :=
  alter committed {stream committed with checkpointEnd := 1}

def prepared : Image 1 Nat :=
  alter published {stream published with
    replayIssued := 1
    replays := Kernel.replaceReplay (stream published).replays 1 (.prepared 0)}

def held : Image 1 Nat :=
  alter prepared {stream prepared with replays := Kernel.replaceReplay (stream prepared).replays 1 (.holding 0)}

def cleared : Image 1 Nat :=
  alter (alter held (stream held)) {stream held with replays := Kernel.replaceReplay (stream held).replays 1 .unused}

def trimmed : Image 1 Nat :=
  alter (alter cleared (stream cleared)) {stream cleared with firstRetained := 1}

def replayTail : List (Frame 1 Nat Unit) :=
  [frame 3 (direct (.checkpoint first 1)),
   frame 4 (direct (.prepareReplay first 0)), frame 5 (direct (.admitReplay first 1 0)),
   frame 6 (direct (.trim first 1)), frame 7 (direct (.releaseReplay 1)),
   frame 8 (direct (.admitReplay first 1 0)), frame 9 (direct (.trim first 1))]

def replayReplies : List (UnifiedSource.Reply Nat) :=
  [.stream (.installed 1), .stream (.replayPrepared 1), .stream .replayChanged,
    .stream .refused, .stream .replayChanged, .stream .refused, .stream (.installed 1)]

theorem publish_hold_refuse_release_and_trim_share_one_ordered_program (rules : Rules 1 Nat Unit) :
    ∃ results, ChosenReplay.replay rules lineage committed replayTail = some (trimmed, results) ∧
      results.map Applied.reply = replayReplies ∧
      ChosenReplay.replay rules lineage committed (replayTail.take 3) =
        some (held, List.zipWith Applied.mk (replayTail.take 3) (replayReplies.take 3)) := by
  have publishes := runRoutine rules committed (position := 3) (command := .checkpoint first 1)
    (state := stream published) (reply := .installed 1) trivial
    (by simp [OrderedApplication.decideCommand, published, alter, stream, committed, initial, Kernel.initial]) rfl
  have reserves := runRoutine rules published (position := 4) (command := .prepareReplay first 0)
    (state := stream prepared) (reply := .replayPrepared 1) trivial
    (by simp [OrderedApplication.decideCommand, prepared, published, alter, stream, committed, initial, Kernel.initial]) rfl
  have admits := runRoutine rules prepared (position := 5) (command := .admitReplay first 1 0)
    (state := stream held) (reply := .replayChanged) trivial
    (by simp [OrderedApplication.decideCommand, held, prepared, published, alter, stream, committed, initial,
      Kernel.initial, Kernel.replaceReplay]) rfl
  have pinned : ¬ ∀ id lsn, (stream held).replays id = .holding lsn → 1 ≤ lsn := by
    intro trims
    exact Nat.not_succ_le_zero 0 (trims 1 0 rfl)
  have refuses := runRoutine rules held (position := 6) (command := .trim first 1)
    (state := stream held) (reply := .refused) trivial
    (by simp only [OrderedApplication.decideCommand]; split
        next conditions => exact False.elim (pinned conditions.2.2.2)
        next => rfl) rfl
  have releases := runRoutine rules (alter held (stream held)) (position := 7) (command := .releaseReplay 1)
    (state := stream cleared) (reply := .replayChanged) trivial
    (by simp [OrderedApplication.decideCommand, cleared, held, prepared, published, alter, stream, committed,
      initial, Kernel.initial]) rfl
  have delayed := runRoutine rules cleared (position := 8) (command := .admitReplay first 1 0)
    (state := stream cleared) (reply := .refused) trivial
    (by simp [OrderedApplication.decideCommand, cleared, alter, stream, Kernel.replaceReplay]) rfl
  have noHold : ∀ id lsn, (stream cleared).replays id = .holding lsn → 1 ≤ lsn := by
    intro id lsn holds
    by_cases exactId : id = 1 <;>
      simp [cleared, held, prepared, published, alter, stream, committed, initial, Kernel.initial,
        Kernel.replaceReplay, exactId] at holds
  have trim := runRoutine rules (alter cleared (stream cleared)) (position := 9) (command := .trim first 1)
    (state := stream trimmed) (reply := .installed 1) trivial
    (by
      have eligible : (stream cleared).authority = .active first ∧
          (stream cleared).firstRetained ≤ 1 ∧ 1 ≤ (stream cleared).checkpointEnd ∧
          (∀ id lsn, (stream cleared).replays id = .holding lsn → 1 ≤ lsn) :=
        ⟨rfl, by decide, by decide, noHold⟩
      simp only [OrderedApplication.decideCommand]
      rw [show stream (alter cleared (stream cleared)) = stream cleared from rfl, ite_eq_left eligible]
      rfl) rfl
  refine ⟨List.zipWith Applied.mk replayTail replayReplies, ?_, rfl, ?_⟩
  · simp only [replayTail]
    rw [replayNext rules committed published 3 _ _ rfl publishes,
      replayNext rules published prepared 4 _ _ rfl reserves,
      replayNext rules prepared held 5 _ _ rfl admits,
      replayNext rules held (alter held (stream held)) 6 _ _ rfl refuses,
      replayNext rules (alter held (stream held)) cleared 7 _ _ rfl releases,
      replayNext rules cleared (alter cleared (stream cleared)) 8 _ _ rfl delayed,
      replayNext rules (alter cleared (stream cleared)) trimmed 9 _ _ rfl trim]
    rfl
  · change ChosenReplay.replay rules lineage committed
      [frame 3 _, frame 4 _, frame 5 _] = _
    rw [replayNext rules committed published 3 _ _ rfl publishes,
      replayNext rules published prepared 4 _ _ rfl reserves,
      replayNext rules prepared held 5 _ _ rfl admits]
    rfl

#print axioms a_funded_install_and_append_return_the_exact_record
#print axioms a_read_and_higher_epoch_fence_preserve_the_committed_cut
#print axioms a_delayed_writer_is_refused_in_the_funded_window
#print axioms retirement_and_later_barrier_share_the_same_replay
#print axioms one_replay_runs_the_funded_writer_lifecycle
#print axioms publish_hold_refuse_release_and_trim_share_one_ordered_program

end CorePrograms
