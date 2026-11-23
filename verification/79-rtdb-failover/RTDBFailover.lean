import RankedJointReplay
import StableGrant

set_option warningAsError true

namespace RTDBFailover

open ChosenReplay (Lineage)
open JointSource (Command Frame Image Rules)
open UnifiedSource (Reply)

variable {width slots : Nat} {Payload Ticket Voter : Type}

structure Route where
  lineage : Lineage
  placement : Kernel.Placement
  deriving DecidableEq

def Names (route : Route) (lineage : Lineage) (writer : Kernel.Writer) : Prop :=
  route.lineage = lineage ∧ route.placement = writer.placement

noncomputable def claim (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (route : Route) (authenticate : Route → Prop)
    (old new : Kernel.Writer) (ticket : Ticket) : Image slots Payload × Reply Payload := by
  classical
  exact if authenticate route ∧ Names route lineage old then
    JointSource.decide rules lineage image (.replaceWriter old new ticket)
  else (image, .refused)

structure Invocation where
  lineage : Lineage
  writer : Kernel.Writer
  nonce : Nat
  deriving DecidableEq

structure Barrier where
  invocation : Invocation
  position : Nat
  cut : Nat

noncomputable def acceptBarrier (pending : Invocation) (reply : Barrier)
    (authenticate : Barrier → Prop) (available : Invocation → Nat → Prop) : Option Nat := by
  classical
  exact if authenticate reply ∧ reply.invocation = pending ∧ available pending reply.cut then some reply.cut else none

def fromCurrent (lineage : Lineage) (image : Image slots Payload) (command : Command slots Payload Ticket) :
    Frame slots Payload Ticket :=
  ⟨lineage, image.source.source.position + 1, command⟩

def view (image : Image slots Payload) : ReceiptReplay.View slots Payload := ⟨image.source, image.receipts⟩

def requestKey (lineage : Lineage) (request : FundedAppend.Request Payload Ticket) : ReceiptReplay.Key Payload :=
  ⟨lineage, request.writer, request.lsn, request.payload⟩

def exactReceipt (lineage : Lineage) (before : Image slots Payload) (request : FundedAppend.Request Payload Ticket) :
    ReceiptReplay.Receipt Payload :=
  ⟨requestKey lineage request, before.source.source.position + 1, request.lsn + 1⟩

structure ReadyAppend (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (request : FundedAppend.Request Payload Ticket) (extent : PoolState.Identity) where
  physical : CompleteSettlement.Window
  paid : FundedAppend.Window
  namesPhysical : image.windows request.version = some physical
  namesPaid : image.source.book.windows request.version = some paid
  extentMatches : physical.lineage = lineage ∧ extent = physical.physical ∧ rules.append request extent
  checks : let frame : ChosenReplay.Frame slots Payload Ticket :=
      ⟨lineage, image.source.source.position + 1, .append request⟩
    FundedAppend.LocalChecks (ChosenReplay.frameRules rules.source frame) lineage.stream
      image.source.source image.source.book paid request

noncomputable def markerState (image : Image slots Payload) : Image slots Payload :=
  {image with source := ChosenReplay.advancePosition image.source
              receipts := ReceiptReplay.retain image.receipts image.source.source.core.stream.firstRetained}

theorem an_authenticated_but_different_group_route_cannot_claim
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (route : Route) (authenticate : Route → Prop) (old new : Kernel.Writer) (ticket : Ticket)
    (wrong : ¬ Names route lineage old) :
    claim rules lineage image route authenticate old new ticket = (image, .refused) := by
  simp [claim, wrong]

theorem serving_requires_the_actual_invocation_and_its_materialized_cut
    (pending : Invocation) (reply : Barrier) (authenticate : Barrier → Prop) (available : Invocation → Nat → Prop)
    (served : Nat) (delivered : acceptBarrier pending reply authenticate available = some served) :
    authenticate reply ∧ reply.invocation = pending ∧ available pending served ∧ served = reply.cut := by
  unfold acceptBarrier at delivered
  split at delivered
  · next checked =>
      cases delivered
      exact ⟨checked.1, checked.2.1, checked.2.2, rfl⟩
  · contradiction

theorem reuse_admits_a_genuine_reply_chosen_before_a_later_invocation
    (pending : Invocation) (reply : Barrier)
    (authenticate : Barrier → Prop) (available : Invocation → Nat → Prop)
    (invokedAfter : Nat) (oldMarker : reply.position ≤ invokedAfter)
    (identityReused : reply.invocation = pending) (genuine : authenticate reply)
    (stillAvailable : available pending reply.cut) :
    acceptBarrier pending reply authenticate available = some reply.cut ∧ reply.position ≤ invokedAfter := by
  have checks : authenticate reply ∧ reply.invocation = pending ∧ available pending reply.cut :=
    ⟨genuine, identityReused, stillAvailable⟩
  exact ⟨by simp only [acceptBarrier, ite_eq_left checks], oldMarker⟩

theorem the_joint_marker_returns_the_current_cut_and_spends_no_append_credit
    (rules : Rules width slots Payload Ticket) (image : Image slots Payload) (call : Invocation)
    (current : image.source.source.core.stream.authority = .active call.writer) :
    JointSource.decide rules call.lineage image (.stream (.read call.writer call.nonce)) =
      (markerState image, .stream (.readCut call.nonce image.source.source.core.stream.history.length)) := by
  have selected : OrderedApplication.decideCommand (rules.source.append.regional.limits call.lineage.stream)
      image.source.source.core.stream (.read call.writer call.nonce) =
      (image.source.source.core.stream, .readCut call.nonce image.source.source.core.stream.history.length) := by
    simp [OrderedApplication.decideCommand, Kernel.barrier, current]
  have routine : UnifiedSource.Routine (.read call.writer call.nonce : OrderedApplication.Command Payload) := trivial
  have result : UnifiedSource.decide (rules.source.append.regional.limits call.lineage.stream)
      (rules.source.append.regional.source call.lineage.stream) image.source.source.core (image.source.source.position + 1)
      (.stream (.read call.writer call.nonce)) =
      (image.source.source.core, .stream (.readCut call.nonce image.source.source.core.stream.history.length)) := by
    simp only [UnifiedSource.decide, ite_eq_left routine, selected]
  simp only [JointSource.decide, JointSource.runSource, ChosenReplay.decide, result]
  rfl

theorem a_paid_append_records_the_exact_replayable_receipt
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (request : FundedAppend.Request Payload Ticket) (extent : PoolState.Identity)
    (ready : ReadyAppend rules lineage image request extent)
    (within : image.source.source.core.stream.firstRetained ≤ request.lsn) :
    let result := JointSource.decide rules lineage image (.append request extent)
    result.2 = .stream (.appended request.lsn ⟨request.writer.epoch, request.payload⟩) ∧
    result.1.source.source.core.stream.history = image.source.source.core.stream.history ++
      [⟨request.writer.epoch, request.payload⟩] ∧
    result.1.source.source.core.stream.authority = image.source.source.core.stream.authority ∧
    result.1.source.source.core.stream.firstRetained = image.source.source.core.stream.firstRetained ∧
    result.1.receipts request.lsn = some (exactReceipt lineage image request) ∧
    result.1.windows = image.windows ∧
    result.1.source.book.windows request.version = some {ready.paid with
      nextLsn := request.lsn + 1, spent := request.offset + rules.source.append.cost request.payload} := by
  have allowed : OrderedApplication.AppendAllowed (rules.source.append.regional.limits lineage.stream)
      image.source.source.core.stream request.writer request.lsn := ready.checks.streamAllowed
  have effect : (UnifiedSource.replay (rules.source.append.regional.limits lineage.stream)
      (rules.source.append.regional.source lineage.stream) image.source.source [FundedAppend.appendCommand request]).1 =
      {image.source.source with
        position := image.source.source.position + 1
        core := {image.source.source.core with stream := {image.source.source.core.stream with
          history := image.source.source.core.stream.history ++ [⟨request.writer.epoch, request.payload⟩]}}} := by
    simp [UnifiedSource.replay, FundedAppend.appendCommand, UnifiedSource.decide, UnifiedSource.Routine,
      OrderedApplication.decideCommand, allowed]
  have paid := FundedAppend.eligible_append_uses_the_original_ordered_reducer ready.namesPaid ready.checks
  have routed : JointSource.decide rules lineage image (.append request extent) =
      JointSource.runSource rules lineage image (.append request) := by
    simp only [JointSource.decide, ready.namesPhysical, ite_eq_left ready.extentMatches]
  rw [routed]
  dsimp only
  simp only [JointSource.runSource, ChosenReplay.decide, paid]
  simp [ChosenReplay.frameRules, effect, ReceiptReplay.record, ReceiptReplay.retain, exactReceipt, requestKey,
    Nat.not_lt_of_ge within, FundedAppend.advanceWindow, SnapshotAdmission.setSlot]

theorem recovery_selects_the_chosen_append_while_extra_staged_bytes_remain
    {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (cut : RankedJointReplay.Cut ledger) (base : RankedJointReplay.Base rules lineage origin cut.frames)
    (request : FundedAppend.Request Payload Ticket) (extent : PoolState.Identity)
    (staged : List (Frame slots Payload Ticket))
    (chosen : cut.frames = [fromCurrent lineage origin (.append request extent)]) :
    RankedJointReplay.reopen rules lineage origin cut base (cut.frames.drop base.cut ++ staged) =
      some (JointSource.decide rules lineage origin (.append request extent)).1 := by
  unfold RankedJointReplay.reopen
  rw [RankedJointReplay.the_complete_historical_suffix_is_used rules lineage origin cut.frames _ base
    (List.prefix_append _ _), chosen]
  simp [JointSource.replay, JointSource.step, JointSource.eligible, fromCurrent]

theorem a_fresh_claim_at_the_same_route_preserves_the_original_receipt
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (route : Route) (authenticate : Route → Prop) (old new : Kernel.Writer) (ticket : Ticket)
    (known : authenticate route ∧ Names route lineage old)
    (nominated : JointSource.CurrentNomination rules lineage image old new ticket)
    (current : image.source.source.core.stream.authority = .active old)
    (samePlace : new.placement = old.placement) (higher : old.epoch < new.epoch)
    (authorized : Prop) (key : ReceiptReplay.Key Payload) :
    let result := claim rules lineage image route authenticate old new ticket
    result = (StableGrant.installed image new, .stream (.installed image.source.source.core.stream.history.length)) ∧
    ReceiptReplay.lookup lineage authorized (view result.1) key = ReceiptReplay.lookup lineage authorized (view image) key := by
  rw [claim, ite_eq_left known,
    StableGrant.a_nominated_same_placement_writer_inherits_the_exact_cut_and_window rules lineage
      image old new ticket nominated (Or.inl current) samePlace higher]
  exact ⟨rfl, StableGrant.a_receipt_lookup_is_unchanged_by_the_worker_replacement lineage image new authorized key⟩

theorem an_exact_cut_without_its_local_suffix_does_not_authorize_recovery
    {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (cut : RankedJointReplay.Cut ledger) (base : RankedJointReplay.Base rules lineage origin cut.frames)
    (physical : List (Frame slots Payload Ticket)) (missing : ¬ cut.frames.drop base.cut <+: physical) :
    RankedJointReplay.reopen rules lineage origin cut base physical = none :=
  RankedJointReplay.a_rival_or_missing_augmented_suffix_is_refused rules lineage origin cut.frames physical base missing

def barrierAt (call : Invocation) (image : Image slots Payload) : Barrier :=
  ⟨call, image.source.source.position + 1, image.source.source.core.stream.history.length⟩

theorem the_failover_program_reconciles_the_chosen_result_and_serves_from_the_prepaid_window
    {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (cut : RankedJointReplay.Cut ledger) (base : RankedJointReplay.Base rules lineage origin cut.frames)
    (original rival next : FundedAppend.Request Payload Ticket) (extent : PoolState.Identity)
    (oldReady : ReadyAppend rules lineage origin original extent)
    (oldRetained : origin.source.source.core.stream.firstRetained ≤ original.lsn)
    (choice : cut.frames = [fromCurrent lineage origin (.append original extent)])
    (rivalLsn : rival.lsn = original.lsn) (different : rival.payload ≠ original.payload)
    (route : Route) (authenticateRoute : Route → Prop) (successor : Kernel.Writer) (ticket : Ticket)
    (known : authenticateRoute route ∧ Names route lineage original.writer)
    (samePlace : successor.placement = original.writer.placement) (higher : original.writer.epoch < successor.epoch)
    (nonce : Nat) (authorizeRetry : Prop) (mayRetry : authorizeRetry)
    (authenticateBarrier : Barrier → Prop) (available : Invocation → Nat → Prop)
    (nominated : let recovered := (JointSource.decide rules lineage origin (.append original extent)).1
      JointSource.CurrentNomination rules lineage recovered original.writer successor ticket)
    (newReady : let recovered := (JointSource.decide rules lineage origin (.append original extent)).1
      ReadyAppend rules lineage (markerState (StableGrant.installed recovered successor)) next extent)
    (sameWindow : next.version = original.version)
    (certificate : let recovered := (JointSource.decide rules lineage origin (.append original extent)).1
      let claimed := StableGrant.installed recovered successor
      authenticateBarrier (barrierAt ⟨lineage, successor, nonce⟩ claimed))
    (applied : let recovered := (JointSource.decide rules lineage origin (.append original extent)).1
      available ⟨lineage, successor, nonce⟩ (StableGrant.installed recovered successor).source.source.core.stream.history.length) :
    let recovered := (JointSource.decide rules lineage origin (.append original extent)).1
    let claimed := StableGrant.installed recovered successor
    let observed := markerState claimed
    let call : Invocation := ⟨lineage, successor, nonce⟩
    let oldReceipt := exactReceipt lineage origin original
    RankedJointReplay.reopen rules lineage origin cut base
        (cut.frames.drop base.cut ++ [fromCurrent lineage origin (.append rival extent)]) = some recovered ∧
    claim rules lineage recovered route authenticateRoute original.writer successor ticket =
      (claimed, .stream (.installed (original.lsn + 1))) ∧
    ReceiptReplay.lookup lineage authorizeRetry (view claimed) (requestKey lineage original) = .committed oldReceipt ∧
    ReceiptReplay.lookup lineage authorizeRetry (view claimed) (requestKey lineage rival) = .conflict ∧
    JointSource.decide rules lineage claimed (.stream (.read successor nonce)) =
      (observed, .stream (.readCut nonce (original.lsn + 1))) ∧
    acceptBarrier call (barrierAt call claimed) authenticateBarrier available = some (original.lsn + 1) ∧
    next.lsn = original.lsn + 1 ∧ next.offset = original.offset + rules.source.append.cost original.payload ∧
    let finished := JointSource.decide rules lineage observed (.append next extent)
    finished.2 = .stream (.appended next.lsn ⟨successor.epoch, next.payload⟩) ∧ finished.1.windows = origin.windows := by
  let recovered := (JointSource.decide rules lineage origin (.append original extent)).1
  let claimed := StableGrant.installed recovered successor
  let observed := markerState claimed
  let call : Invocation := ⟨lineage, successor, nonce⟩
  let oldReceipt := exactReceipt lineage origin original
  have ⟨_, history, oldAuthority, floor, saved, originalPhysical, advanced⟩ :=
    a_paid_append_records_the_exact_replayable_receipt rules lineage origin original extent oldReady oldRetained
  have recoveredCut : recovered.source.source.core.stream.history.length = original.lsn + 1 := by
    change (JointSource.decide rules lineage origin (.append original extent)).1.source.source.core.stream.history.length = _
    rw [history, List.length_append, ← oldReady.checks.streamAllowed.2.1]
    rfl
  have current : recovered.source.source.core.stream.authority = .active original.writer :=
    oldAuthority.trans oldReady.checks.streamAllowed.1
  have exactClaim := a_fresh_claim_at_the_same_route_preserves_the_original_receipt rules lineage recovered
    route authenticateRoute original.writer successor ticket known nominated current samePlace higher authorizeRetry
  have recover := recovery_selects_the_chosen_append_while_extra_staged_bytes_remain rules lineage origin cut base
    original extent [fromCurrent lineage origin (.append rival extent)] choice
  have atFloor : (CoreReference.stream (view recovered).image).firstRetained ≤ (requestKey lineage original).lsn :=
    floor.symm ▸ oldRetained
  have inHistory : (requestKey lineage original).lsn < (CoreReference.stream (view recovered).image).history.length := by
    change original.lsn < recovered.source.source.core.stream.history.length
    rw [recoveredCut]
    exact Nat.lt_succ_self _
  have originalLookup := ReceiptReplay.the_exact_retained_receipt_is_available_without_appending
    (view := view recovered) (receipt := oldReceipt) (approved := And.intro mayRetry rfl)
    atFloor inHistory saved rfl
  have wrongResult : ¬ ReceiptReplay.Matches oldReceipt (requestKey lineage rival) := by
    intro same
    exact different (congrArg ReceiptReplay.Key.payload same).symm
  have rivalLookup : ReceiptReplay.lookup lineage authorizeRetry (view recovered) (requestKey lineage rival) = .conflict := by
    have held : ¬ (requestKey lineage rival).lsn < (CoreReference.stream (view recovered).image).firstRetained := by
      simpa only [requestKey, rivalLsn] using Nat.not_lt_of_ge atFloor
    have existsAt : ¬ (CoreReference.stream (view recovered).image).history.length ≤ (requestKey lineage rival).lsn := by
      simpa only [requestKey, rivalLsn] using Nat.not_le_of_gt inHistory
    have sameRow : (view recovered).rows (requestKey lineage rival).lsn = some oldReceipt := by
      simpa only [view, requestKey, rivalLsn] using saved
    have authorized : authorizeRetry ∧ (requestKey lineage rival).lineage = lineage := ⟨mayRetry, rfl⟩
    simp [ReceiptReplay.lookup, authorized, held, existsAt, sameRow, wrongResult]
  have binding : claim rules lineage recovered route authenticateRoute original.writer successor ticket =
      (claimed, .stream (.installed recovered.source.source.core.stream.history.length)) :=
    (exactClaim (requestKey lineage original)).1
  have observesOriginal : ReceiptReplay.lookup lineage authorizeRetry (view claimed) (requestKey lineage original) =
      .committed oldReceipt := by
    simpa only [binding] using ((exactClaim (requestKey lineage original)).2.trans originalLookup)
  have refusesRival : ReceiptReplay.lookup lineage authorizeRetry (view claimed) (requestKey lineage rival) =
      .conflict := by
    simpa only [binding] using ((exactClaim (requestKey lineage rival)).2.trans rivalLookup)
  have marker := the_joint_marker_returns_the_current_cut_and_spends_no_append_credit rules claimed call rfl
  have appliedCut : acceptBarrier call (barrierAt call claimed) authenticateBarrier available =
      some (original.lsn + 1) := by
    have verified : authenticateBarrier (barrierAt call claimed) ∧ (barrierAt call claimed).invocation = call ∧
        available call (barrierAt call claimed).cut := ⟨certificate, rfl, applied⟩
    simp only [acceptBarrier, ite_eq_left verified]
    change some recovered.source.source.core.stream.history.length = _
    rw [recoveredCut]
  have windowStill : observed.source.book.windows next.version =
      some {oldReady.paid with
        nextLsn := original.lsn + 1
        spent := original.offset + rules.source.append.cost original.payload} := by
    change recovered.source.book.windows next.version = _
    rw [sameWindow]
    exact advanced
  have samePaid := Option.some.inj (newReady.namesPaid.symm.trans windowStill)
  have nextLsn : next.lsn = original.lsn + 1 := by
    have exactLsn := newReady.checks.nextLsn.symm
    rw [samePaid] at exactLsn
    exact exactLsn
  have nextOffset : next.offset = original.offset + rules.source.append.cost original.payload := by
    have exactOffset := newReady.checks.offset.symm
    rw [samePaid] at exactOffset
    exact exactOffset
  have newRetained : observed.source.source.core.stream.firstRetained ≤ next.lsn := by
    change recovered.source.source.core.stream.firstRetained ≤ next.lsn
    rw [nextLsn]
    exact Nat.le_trans atFloor (Nat.le_succ _)
  have nextWriter : next.writer = successor :=
    (Kernel.Authority.active.inj newReady.checks.streamAllowed.1).symm
  have last := a_paid_append_records_the_exact_replayable_receipt rules lineage observed next extent newReady newRetained
  refine ⟨recover, ?_, observesOriginal, refusesRival, ?_, appliedCut, nextLsn, nextOffset, ?_, ?_⟩
  · rwa [← recoveredCut]
  · rw [← recoveredCut]
    exact marker
  · simpa only [nextWriter] using last.1
  · exact last.2.2.2.2.2.1.trans originalPhysical

#print axioms an_authenticated_but_different_group_route_cannot_claim
#print axioms serving_requires_the_actual_invocation_and_its_materialized_cut
#print axioms reuse_admits_a_genuine_reply_chosen_before_a_later_invocation
#print axioms the_joint_marker_returns_the_current_cut_and_spends_no_append_credit
#print axioms a_paid_append_records_the_exact_replayable_receipt
#print axioms recovery_selects_the_chosen_append_while_extra_staged_bytes_remain
#print axioms a_fresh_claim_at_the_same_route_preserves_the_original_receipt
#print axioms an_exact_cut_without_its_local_suffix_does_not_authorize_recovery
#print axioms the_failover_program_reconciles_the_chosen_result_and_serves_from_the_prepaid_window

end RTDBFailover
