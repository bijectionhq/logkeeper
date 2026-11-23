import FundedWindowMove

set_option warningAsError true

namespace MoveRecovery

open SnapshotAdmission (setSlot)

variable {slots : Nat} {Payload Ticket : Type}

structure Evidence (slots : Nat) (Payload Ticket : Type) where
  grant : ChosenReplay.Lineage → ChosenReplay.Grant Ticket → Prop
  activation : ChosenReplay.Lineage → ChosenReplay.Activation slots Payload Ticket → Prop

def MatchesMove (rules : FundedWindowMove.Rules slots Payload Ticket) (lineage : ChosenReplay.Lineage)
    (activation : ChosenReplay.Activation slots Payload Ticket) : Prop :=
  let key : FundedWindowMove.Key slots := ⟨lineage.stream, activation.installation.anchor.decision.key⟩
  FundedWindowMove.BindsPlan rules key activation.installation.anchor ∧
  activation.grant.version = (rules.plan key).window ∧
  activation.grant.writer = FundedWindowMove.destinationWriter rules key activation.installation

def sourceRules (rules : FundedWindowMove.Rules slots Payload Ticket) (evidence : Evidence slots Payload Ticket) :
    ChosenReplay.Rules slots Payload Ticket :=
  ⟨rules.append, evidence.grant, fun lineage activation =>
    MatchesMove rules lineage activation ∧ evidence.activation lineage activation⟩

def sourceImage (state : FundedWindowMove.State slots Payload Ticket) (stream : Nat) :
    ChosenReplay.Image slots Payload :=
  ⟨state.appends.regional.streams stream, state.appends.book⟩

def activationFor (rules : FundedWindowMove.Rules slots Payload Ticket) (key : FundedWindowMove.Key slots)
    (proof : UnifiedSource.Installation slots Nat Payload Ticket) (grantProof : Ticket) :
    ChosenReplay.Activation slots Payload Ticket :=
  ⟨proof, ⟨(rules.plan key).window, FundedWindowMove.destinationWriter rules key proof, grantProof⟩⟩

theorem a_bare_activation_cannot_publish_authority
    (rules : ChosenReplay.Rules slots Payload Ticket) (lineage : ChosenReplay.Lineage)
    (image : ChosenReplay.Image slots Payload) (proof : UnifiedSource.Installation slots Nat Payload Ticket) :
    ChosenReplay.decide rules lineage image ⟨lineage, image.source.position + 1, .source (.activate proof)⟩ =
      (ChosenReplay.advancePosition image, .refused) := by
  rfl

theorem a_missing_historical_activation_receipt_changes_neither_writer_nor_window
    (rules : ChosenReplay.Rules slots Payload Ticket) (lineage : ChosenReplay.Lineage)
    (image : ChosenReplay.Image slots Payload) (activation : ChosenReplay.Activation slots Payload Ticket)
    (missing : ¬ rules.activation lineage activation) :
    ChosenReplay.decide rules lineage image ⟨lineage, image.source.position + 1, .activate activation⟩ =
      (ChosenReplay.advancePosition image, .refused) := by
  simp [ChosenReplay.decide, ChosenReplay.AcceptsActivation, missing]

theorem the_certified_move_selects_its_original_window
    {rules : FundedWindowMove.Rules slots Payload Ticket} {evidence : Evidence slots Payload Ticket}
    {lineage : ChosenReplay.Lineage} {activation : ChosenReplay.Activation slots Payload Ticket}
    (authorized : (sourceRules rules evidence).activation lineage activation) :
    activation.grant.version =
      (rules.plan ⟨lineage.stream, activation.installation.anchor.decision.key⟩).window := by
  exact authorized.1.2.1

theorem replaying_the_funded_activation_agrees_with_the_live_move
    (rules : FundedWindowMove.Rules slots Payload Ticket) (evidence : Evidence slots Payload Ticket)
    (state : FundedWindowMove.State slots Payload Ticket) (lineage : ChosenReplay.Lineage)
    (key : FundedWindowMove.Key slots) (stream : lineage.stream = key.stream)
    (proof : UnifiedSource.Installation slots Nat Payload Ticket) (grantProof : Ticket)
    (bound : FundedWindowMove.BindsPlan rules key proof.anchor)
    (accepted : (FundedWindowMove.applySource rules state key (.activate proof)).2 = [.accepted])
    (ready : FundedWindowMove.WindowReady rules (FundedWindowMove.applySource rules state key (.activate proof)).1
      key (FundedWindowMove.destinationWriter rules key proof))
    (original : evidence.activation lineage (activationFor rules key proof grantProof))
    (authGrant : evidence.grant lineage (activationFor rules key proof grantProof).grant) :
    let image := sourceImage state lineage.stream
    let frame : ChosenReplay.Frame slots Payload Ticket :=
      ⟨lineage, image.source.position + 1, .activate (activationFor rules key proof grantProof)⟩
    ChosenReplay.decide (sourceRules rules evidence) lineage image frame =
      (sourceImage (FundedWindowMove.publish rules state key proof) lineage.stream, .accepted) := by
  rcases lineage with ⟨streamId, incarnation⟩
  change streamId = key.stream at stream
  subst streamId
  let lineage : ChosenReplay.Lineage := ⟨key.stream, incarnation⟩
  let starting := state.appends.regional.streams key.stream
  let apply := UnifiedSource.decide (rules.append.regional.limits key.stream)
    (rules.append.regional.source key.stream) starting.core (starting.position + 1) (.activate proof)
  have authorizes : apply.2 = .accepted := by
    simpa [FundedWindowMove.applySource, FundedWindowMove.source, UnifiedSource.replay, apply, starting] using accepted
  have usesWriter : apply.1.stream.authority = .active (FundedWindowMove.destinationWriter rules key proof) := by
    simpa [FundedWindowMove.applySource, FundedWindowMove.source, UnifiedSource.replay, setSlot, apply, starting]
      using ready.writer
  have recorded : (sourceRules rules evidence).activation lineage (activationFor rules key proof grantProof) :=
    ⟨by
      have same : (⟨lineage.stream, proof.anchor.decision.key⟩ : FundedWindowMove.Key slots) = key := by
        cases key
        simp_all [lineage, FundedWindowMove.BindsPlan]
      simpa [MatchesMove, activationFor, same] using bound, original⟩
  have fits : ChosenReplay.InstallAllowed (sourceRules rules evidence) lineage
      ⟨⟨apply.1, starting.position⟩, state.appends.book⟩ (activationFor rules key proof grantProof).grant := by
    refine ⟨authGrant, ?_, ?_, ready.unused, usesWriter⟩
    · exact ready.owned
    · exact ready.newer
  have permits : ChosenReplay.AcceptsActivation (sourceRules rules evidence) lineage
      (sourceImage state key.stream) (activationFor rules key proof grantProof) :=
    ⟨authorizes, recorded, fits⟩
  simp only [ChosenReplay.decide]
  split
  · simp [FundedWindowMove.publish, FundedAppend.openWindow, FundedWindowMove.applySource, UnifiedSource.replay,
      FundedWindowMove.source, setSlot, ChosenReplay.installWindow, ChosenReplay.advancePosition, activationFor,
      ChosenReplay.applyActivation, sourceImage, sourceRules]
  · rename_i refused
    exact False.elim (refused permits)

def windowBook (rules : FundedWindowMove.Rules slots Payload Ticket) (stream : Nat)
    (current recovered : FundedAppend.Book) : FundedAppend.Book :=
  ⟨fun version => if rules.append.owner version = stream then recovered.windows version else current.windows version,
    setSlot current.latest stream (recovered.latest stream)⟩

def restoreSource (rules : FundedWindowMove.Rules slots Payload Ticket)
    (current : FundedWindowMove.State slots Payload Ticket) (stream : Nat)
    (recovered : ChosenReplay.Image slots Payload) : FundedWindowMove.State slots Payload Ticket :=
  {current with appends := {
    regional := {current.appends.regional with
      streams := setSlot current.appends.regional.streams stream recovered.source}
    book := windowBook rules stream current.appends.book recovered.book}}

theorem source_recovery_preserves_independent_pool_and_read_state
    (rules : FundedWindowMove.Rules slots Payload Ticket) (current : FundedWindowMove.State slots Payload Ticket)
    (stream : Nat) (recovered : ChosenReplay.Image slots Payload) :
    let next := restoreSource rules current stream recovered
    next.appends.regional.pools = current.appends.regional.pools ∧
      next.held = current.held ∧ next.installed = current.installed ∧
      next.appends.regional.borrows = current.appends.regional.borrows :=
  ⟨rfl, rfl, rfl, rfl⟩

def ConfirmsInstall (rules : FundedWindowMove.Rules slots Payload Ticket) (key : FundedWindowMove.Key slots)
    (receipt : ChosenReplay.Applied slots Payload Ticket) : Prop :=
  ∃ activation, receipt.frame.command = .activate activation ∧ receipt.reply = .accepted ∧
    receipt.frame.lineage.stream = key.stream ∧ activation.installation.anchor.decision.key = key.move ∧
    MatchesMove rules receipt.frame.lineage activation

def HasClaim (state : FundedWindowMove.State slots Payload Ticket) (key : FundedWindowMove.Key slots) : Prop :=
  ∃ version, state.held version = some key

noncomputable def recordInstallation (rules : FundedWindowMove.Rules slots Payload Ticket)
    (authentic : ChosenReplay.Applied slots Payload Ticket → Prop)
    (current : FundedWindowMove.State slots Payload Ticket) (key : FundedWindowMove.Key slots)
    (receipt : ChosenReplay.Applied slots Payload Ticket) :
    Option (FundedWindowMove.State slots Payload Ticket) := by
  classical
  exact if authentic receipt ∧ ConfirmsInstall rules key receipt ∧ HasClaim current key then
    some {current with installed := fun query => if query = key then true else current.installed query}
    else none

theorem recording_a_receipt_only_authorizes_its_own_settlement
    {rules : FundedWindowMove.Rules slots Payload Ticket}
    {authentic : ChosenReplay.Applied slots Payload Ticket → Prop}
    {current next : FundedWindowMove.State slots Payload Ticket} {key : FundedWindowMove.Key slots}
    {receipt : ChosenReplay.Applied slots Payload Ticket}
    (confirmed : recordInstallation rules authentic current key receipt = some next) :
    authentic receipt ∧ ConfirmsInstall rules key receipt ∧ FundedWindowMove.CanSettle next key ∧
      next.held = current.held ∧ next.appends.regional.pools = current.appends.regional.pools ∧
      ∀ other, other ≠ key → next.installed other = current.installed other := by
  unfold recordInstallation at confirmed
  split at confirmed
  · rename_i exactReceipt
    cases confirmed
    exact ⟨exactReceipt.1, exactReceipt.2.1, .inl (by simp), rfl, rfl, fun other different => by simp [different]⟩
  · cases confirmed

theorem a_delayed_receipt_cannot_reopen_a_settled_claim
    {rules : FundedWindowMove.Rules slots Payload Ticket}
    {authentic : ChosenReplay.Applied slots Payload Ticket → Prop}
    {current : FundedWindowMove.State slots Payload Ticket} {key : FundedWindowMove.Key slots}
    (settled : ¬ HasClaim current key) (receipt : ChosenReplay.Applied slots Payload Ticket) :
    recordInstallation rules authentic current key receipt = none := by
  simp [recordInstallation, settled]

theorem restoring_a_stream_preserves_a_neighbors_cursor
    (rules : FundedWindowMove.Rules slots Payload Ticket) (current : FundedWindowMove.State slots Payload Ticket)
    (stream neighbor : Nat) (recovered : ChosenReplay.Image slots Payload) (other : neighbor ≠ stream) :
    let next := restoreSource rules current stream recovered
    next.appends.regional.streams neighbor = current.appends.regional.streams neighbor ∧
      next.appends.book.latest neighbor = current.appends.book.latest neighbor ∧
      (∀ version, rules.append.owner version = neighbor →
        next.appends.book.windows version = current.appends.book.windows version) := by
  simp [restoreSource, windowBook, setSlot, other]
  intro version owner
  simp [owner, other]

def PhysicalWindow (rules : FundedWindowMove.Rules slots Payload Ticket)
    (state : FundedWindowMove.State slots Payload Ticket) (stream version : Nat) : Prop :=
  ∃ window writer, state.appends.book.latest stream = version ∧
    state.appends.book.windows version = some window ∧ window.stream = stream ∧
    (state.appends.regional.streams stream).core.stream.authority = .active writer ∧
    window.placement = writer.placement ∧
    FundedAppend.Backed state.appends.regional version ∧
    PoolIncarnations.Eligible state.appends.regional.pools ((FundedWindowMove.layout rules).pool version)

noncomputable def admitService (rules : FundedWindowMove.Rules slots Payload Ticket)
    (state : FundedWindowMove.State slots Payload Ticket) (stream version : Nat) : Option Nat := by
  classical
  exact if PhysicalWindow rules state stream version then some version else none

theorem a_recovered_window_needs_current_physical_admission
    {rules : FundedWindowMove.Rules slots Payload Ticket} {state : FundedWindowMove.State slots Payload Ticket}
    {stream version served : Nat} (admitted : admitService rules state stream version = some served) :
    served = version ∧ FundedAppend.Backed state.appends.regional version ∧
      PoolIncarnations.Eligible state.appends.regional.pools ((FundedWindowMove.layout rules).pool version) := by
  unfold admitService at admitted
  split at admitted
  · rename_i physical
    cases admitted
    obtain ⟨_, _, _, _, _, _, _, backing, eligibility⟩ := physical
    exact ⟨rfl, backing, eligibility⟩
  · cases admitted

structure RestoreReady (rules : FundedWindowMove.Rules slots Payload Ticket)
    (current : FundedWindowMove.State slots Payload Ticket) (stream : Nat)
    (image : ChosenReplay.Image slots Payload) : Prop where
  valid : Kernel.Valid (rules.append.regional.limits stream) image.source.core.stream
  charged : ∀ version window, rules.append.owner version = stream →
    image.book.windows version = some window →
    FundedAppend.Backed current.appends.regional version ∧
      window.spent ≤ FundedAppend.debitBytes rules.append version ∧ window.stream = stream ∧
      version ≤ image.book.latest stream

theorem independent_recovery_preserves_the_shared_ledger_invariants
    {rules : FundedWindowMove.Rules slots Payload Ticket} {current : FundedWindowMove.State slots Payload Ticket}
    {stream : Nat} {image : ChosenReplay.Image slots Payload}
    (safe : FundedWindowMove.Sound rules current) (ready : RestoreReady rules current stream image) :
    FundedWindowMove.Sound rules (restoreSource rules current stream image) := by
  refine ⟨⟨?_, safe.regional.pools, safe.regional.counts, safe.regional.unique, safe.regional.issued,
      safe.regional.bounded⟩, ?_, safe.claims⟩
  · intro deployment
    by_cases same : deployment = stream
    · subst deployment
      simpa [restoreSource, setSlot] using ready.valid
    · simpa [restoreSource, setSlot, same] using safe.regional.streams deployment
  · intro version window live
    by_cases owned : rules.append.owner version = stream
    · have present : image.book.windows version = some window := by
        simpa [restoreSource, windowBook, owned] using live
      obtain ⟨paid, fits, owner, before⟩ := ready.charged version window owned present
      exact ⟨paid, fits, owned.trans owner.symm, by simpa [restoreSource, windowBook, setSlot, owner] using before⟩
    · have present : current.appends.book.windows version = some window := by
        simpa [restoreSource, windowBook, owned] using live
      obtain ⟨paid, fits, owner, before⟩ := safe.windows version window present
      have elsewhere : window.stream ≠ stream := fun same => owned (owner.trans same)
      exact ⟨paid, fits, owner, by simpa [restoreSource, windowBook, setSlot, elsewhere] using before⟩

theorem either_certified_source_selector_restores_the_same_regional_projection
    {Voter : Type} {ledger : PrefixAgreement.Ledger Voter (ChosenReplay.Frame slots Payload Ticket)}
    (rules : FundedWindowMove.Rules slots Payload Ticket) (evidence : Evidence slots Payload Ticket)
    (lineage : ChosenReplay.Lineage) (origin : ChosenReplay.Image slots Payload)
    (current : FundedWindowMove.State slots Payload Ticket) (chosen : ChosenReplay.CertifiedCut ledger)
    (old new : ChosenReplay.SelectedBase (sourceRules rules evidence) lineage origin chosen.frames)
    (oldPhysical newPhysical : List (ChosenReplay.Frame slots Payload Ticket))
    {left right : ChosenReplay.Image slots Payload} {oldTail newTail : List (ChosenReplay.Applied slots Payload Ticket)}
    (reopenedOld : ChosenReplay.reopen (sourceRules rules evidence) lineage origin chosen old oldPhysical =
      some (left, oldTail))
    (reopenedNew : ChosenReplay.reopen (sourceRules rules evidence) lineage origin chosen new newPhysical =
      some (right, newTail)) :
    restoreSource rules current lineage.stream left = restoreSource rules current lineage.stream right ∧
      oldTail.map ChosenReplay.Applied.frame = chosen.frames.drop old.cut ∧
      newTail.map ChosenReplay.Applied.frame = chosen.frames.drop new.cut := by
  obtain ⟨same, oldRecords, newRecords⟩ := ChosenReplay.two_selectable_bases_restore_one_exact_state_and_suffix
    (sourceRules rules evidence) lineage origin chosen old new oldPhysical newPhysical reopenedOld reopenedNew
  exact ⟨congrArg (restoreSource rules current lineage.stream) same, oldRecords, newRecords⟩

#print axioms a_bare_activation_cannot_publish_authority
#print axioms a_missing_historical_activation_receipt_changes_neither_writer_nor_window
#print axioms the_certified_move_selects_its_original_window
#print axioms replaying_the_funded_activation_agrees_with_the_live_move
#print axioms source_recovery_preserves_independent_pool_and_read_state
#print axioms recording_a_receipt_only_authorizes_its_own_settlement
#print axioms a_delayed_receipt_cannot_reopen_a_settled_claim
#print axioms restoring_a_stream_preserves_a_neighbors_cursor
#print axioms a_recovered_window_needs_current_physical_admission
#print axioms independent_recovery_preserves_the_shared_ledger_invariants
#print axioms either_certified_source_selector_restores_the_same_regional_projection

end MoveRecovery
