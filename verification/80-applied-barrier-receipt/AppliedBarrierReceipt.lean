import RTDBFailover

set_option warningAsError true

namespace AppliedBarrierReceipt

open EnvelopeCodec (Bytes Field word wordLimit readWord readFields flattenFields)
open ChosenReplay (Lineage)
open JointSource (Rules Image Frame)
open RTDBFailover (Route Invocation Barrier fromCurrent)

variable {width slots : Nat} {Payload Ticket Voter Signature : Type}

def fields (reply : Barrier) : List Nat :=
  [reply.invocation.lineage.stream, reply.invocation.lineage.incarnation,
   reply.invocation.writer.placement.group, reply.invocation.writer.placement.generation,
   reply.invocation.writer.epoch, reply.invocation.writer.holder, reply.invocation.nonce, reply.position, reply.cut]

def assemble : List Nat → Option Barrier
  | [stream, incarnation, group, generation, epoch, holder, nonce, position, cut] =>
      some ⟨⟨⟨stream, incarnation⟩, ⟨⟨group, generation⟩, epoch, holder⟩, nonce⟩, position, cut⟩
  | _ => none

def domain : UInt8 := 4

def Fits (width : Nat) (reply : Barrier) : Prop := ∀ value ∈ fields reply, value < wordLimit width

def encode (width : Nat) (reply : Barrier) : Bytes :=
  domain :: flattenFields ((fields reply).map (word width))

def decode (width : Nat) : Bytes → Option Barrier
  | tag :: raw =>
      if tag = domain ∧ 0 < width then
        (readFields width 9 raw).bind fun words => assemble (words.map (fun field => readWord field.val))
      else none
  | [] => none

private theorem assemble_own_fields (reply : Barrier) : assemble (fields reply) = some reply := by
  rcases reply with ⟨⟨⟨stream, incarnation⟩, ⟨⟨group, generation⟩, epoch, holder⟩, nonce⟩, position, cut⟩
  rfl

private theorem assembly_binds_fields {words : List Nat} {reply : Barrier}
    (opened : assemble words = some reply) : fields reply = words := by
  unfold assemble at opened
  split at opened
  · cases opened
    rfl
  · contradiction

theorem a_representable_reply_round_trips (reply : Barrier) (positive : 0 < width) (fits : Fits width reply) :
    decode width (encode width reply) = some reply := by
  have exactWords : (readFields width 9 (flattenFields ((fields reply).map (word width)))) =
      some ((fields reply).map (word width)) := by
    have parsed := EnvelopeCodec.readFields_after_flatten ((fields reply).map (word width))
    simpa only [List.length_map, fields, List.length_cons, List.length_nil, Nat.reduceAdd] using parsed
  have decoded : ((fields reply).map (word width)).map (fun field => readWord field.val) = fields reply := by
    rw [List.map_map]
    refine Eq.trans ?_ (List.map_id _)
    apply List.map_congr_left
    intro item present
    exact EnvelopeCodec.fixed_width_words_roundtrip (fits item present)
  simp only [encode, decode, true_and, ite_eq_left positive, exactWords]
  change assemble (((fields reply).map (word width)).map (fun field => readWord field.val)) = some reply
  rw [decoded, assemble_own_fields]

theorem accepted_reply_bytes_are_canonical {wire : Bytes} {reply : Barrier}
    (decoded : decode width wire = some reply) : encode width reply = wire := by
  cases wire with
  | nil => simp [decode] at decoded
  | cons tag raw =>
      simp only [decode] at decoded
      split at decoded
      · next valid =>
        cases parsed : readFields width 9 raw with
        | none => simp [parsed] at decoded
        | some words =>
            have built : assemble (words.map (fun field => readWord field.val)) = some reply := by
              simpa [parsed] using decoded
            have sameWords : (fields reply).map (word width) = words := by
              rw [assembly_binds_fields built, List.map_map]
              refine Eq.trans ?_ (List.map_id _)
              apply List.map_congr_left
              intro field _
              exact EnvelopeCodec.readField_recovers_the_exact_word field
            simp [encode, valid.1, sameWords, EnvelopeCodec.readFields_recovers_the_exact_wire parsed]
      · contradiction

theorem an_encoded_reply_has_constant_length (width : Nat) (reply : Barrier) :
    (encode width reply).length = 1 + 9 * width := by
  simp [encode, fields, EnvelopeCodec.flattenFields_size, Nat.add_comm]

def readCommand (call : Invocation) : JointSource.Command slots Payload Ticket :=
  .stream (.read call.writer call.nonce)

structure ChosenMarker (rules : Rules width slots Payload Ticket) (ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket))
    (origin : Image slots Payload) (call : Invocation) where
  preceding : List (Frame slots Payload Ticket)
  before : Image slots Payload
  ballot : Nat
  replayed : JointSource.replay rules call.lineage origin preceding = some before
  chosen : PrefixAgreement.Chosen ledger ballot (preceding ++ [fromCurrent call.lineage before (readCommand call)])
  ordinal : before.source.source.position = origin.source.source.position + preceding.length

def ChosenMarker.position
    {rules : Rules width slots Payload Ticket} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    {origin : Image slots Payload} {call : Invocation} (marker : ChosenMarker rules ledger origin call) : Nat :=
  marker.before.source.source.position + 1

noncomputable def ChosenMarker.result
    {rules : Rules width slots Payload Ticket} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    {origin : Image slots Payload} {call : Invocation} (marker : ChosenMarker rules ledger origin call) : UnifiedSource.Reply Payload :=
  (JointSource.decide rules call.lineage marker.before (readCommand call)).2

def Issuable (rules : Rules width slots Payload Ticket) (ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket))
    (origin : Image slots Payload) (reply : Barrier) : Prop :=
  ∃ marker : ChosenMarker rules ledger origin reply.invocation,
    marker.position = reply.position ∧ marker.result = .stream (.readCut reply.invocation.nonce reply.cut)

theorem one_chosen_marker_position_has_one_applied_result
    {rules : Rules width slots Payload Ticket} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    {origin : Image slots Payload} {call : Invocation} (protocol : PrefixAgreement.Rules ledger)
    (first second : ChosenMarker rules ledger origin call) (samePosition : first.position = second.position) :
    first.result = second.result := by
  have lengths : first.preceding.length = second.preceding.length := by
    simp only [ChosenMarker.position, first.ordinal, second.ordinal] at samePosition
    omega
  have sameLength : (first.preceding ++ [fromCurrent call.lineage first.before (readCommand call)]).length =
      (second.preceding ++ [fromCurrent call.lineage second.before (readCommand call)]).length := by simp [lengths]
  have sameFrames :
      first.preceding ++ [fromCurrent call.lineage first.before (readCommand call)] =
      second.preceding ++ [fromCurrent call.lineage second.before (readCommand call)] := by
    rcases PrefixAgreement.every_chosen_prefix_agrees protocol first.chosen second.chosen with earlier | later
    · exact earlier.eq_of_length_le (Nat.le_of_eq sameLength.symm)
    · exact (later.eq_of_length_le (Nat.le_of_eq sameLength)).symm
  have samePrefix : first.preceding = second.preceding := by
    simpa using congrArg List.dropLast sameFrames
  have sameImage : first.before = second.before :=
    Option.some.inj (first.replayed.symm.trans (samePrefix ▸ second.replayed))
  simp [ChosenMarker.result, sameImage]

def sourceOf (invocation : Invocation) : Route :=
  ⟨invocation.lineage, invocation.writer.placement⟩

structure Packet (Signature : Type) where
  body : Bytes
  signature : Signature

noncomputable def issue (width : Nat) (rules : Rules width slots Payload Ticket)
    (ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)) (origin : Image slots Payload)
    (sign : Route → Bytes → Signature) (reply : Barrier) : Option (Packet Signature) := by
  classical
  exact if 0 < width ∧ Fits width reply ∧ Issuable rules ledger origin reply then
    let body := encode width reply
    some ⟨body, sign (sourceOf reply.invocation) body⟩
  else none

noncomputable def deliver (width : Nat) (pending : Invocation) (packet : Packet Signature)
    (verify : Route → Bytes → Signature → Prop) (available : Invocation → Nat → Prop) : Option Nat :=
  (decode width packet.body).bind fun reply =>
    RTDBFailover.acceptBarrier pending reply (fun _ => verify (sourceOf reply.invocation) packet.body packet.signature) available

theorem issuance_requires_the_exact_successful_application
    {rules : Rules width slots Payload Ticket} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    {origin : Image slots Payload} {sign : Route → Bytes → Signature} {reply : Barrier} {packet : Packet Signature}
    (issued : issue width rules ledger origin sign reply = some packet) :
    Issuable rules ledger origin reply ∧ decode width packet.body = some reply ∧
      packet.signature = sign (sourceOf reply.invocation) packet.body := by
  unfold issue at issued
  split at issued
  · next valid =>
      cases issued
      exact ⟨valid.2.2, a_representable_reply_round_trips reply valid.1 valid.2.1, rfl⟩
  · contradiction

private theorem marker_result_is_the_kernel_read
    {rules : Rules width slots Payload Ticket} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    {origin : Image slots Payload} {call : Invocation} (marker : ChosenMarker rules ledger origin call) :
    marker.result = .stream ((OrderedApplication.decideCommand (rules.source.append.regional.limits call.lineage.stream)
      marker.before.source.source.core.stream (.read call.writer call.nonce)).2) := by
  have unchanged : (OrderedApplication.decideCommand (rules.source.append.regional.limits call.lineage.stream)
      marker.before.source.source.core.stream (.read call.writer call.nonce)).1 =
        marker.before.source.source.core.stream := by
    simp [OrderedApplication.decideCommand]
  have routine : UnifiedSource.Routine (.read call.writer call.nonce : OrderedApplication.Command Payload) := trivial
  simp only [ChosenMarker.result, readCommand, JointSource.decide, JointSource.runSource, ChosenReplay.decide,
    UnifiedSource.decide, ite_eq_left routine, unchanged]
  rfl

theorem issuance_proves_the_writer_was_active_at_that_exact_cut
    {rules : Rules width slots Payload Ticket} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    {origin : Image slots Payload} {sign : Route → Bytes → Signature} {reply : Barrier} {packet : Packet Signature}
    (issued : issue width rules ledger origin sign reply = some packet) :
    ∃ marker : ChosenMarker rules ledger origin reply.invocation,
      marker.position = reply.position ∧
      marker.before.source.source.core.stream.authority = .active reply.invocation.writer ∧
      reply.cut = marker.before.source.source.core.stream.history.length := by
  obtain ⟨⟨marker, located, read⟩, _, _⟩ := issuance_requires_the_exact_successful_application issued
  rw [marker_result_is_the_kernel_read marker] at read
  exact ⟨marker, located, (OrderedApplication.applied_read_reports_exact_cut
    (UnifiedSource.Reply.stream.inj read)).2⟩

theorem a_chosen_refusal_cannot_issue_a_positive_packet
    {rules : Rules width slots Payload Ticket} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    {origin : Image slots Payload} (protocol : PrefixAgreement.Rules ledger) (sign : Route → Bytes → Signature)
    (reply : Barrier) (marker : ChosenMarker rules ledger origin reply.invocation)
    (atSlot : marker.position = reply.position)
    (refused : marker.result = .stream .refused ∨ marker.result = .refused) :
    issue width rules ledger origin sign reply = none := by
  have unsupported : ¬ Issuable rules ledger origin reply := by
    rintro ⟨other, same, allowed⟩
    have outcome := one_chosen_marker_position_has_one_applied_result protocol marker other (atSlot.trans same.symm)
    rw [allowed] at outcome
    rcases refused with noRead | noSource <;> simp_all
  simp [issue, unsupported]

theorem accepted_delivery_comes_from_an_exact_issued_marker
    {rules : Rules width slots Payload Ticket} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    {origin : Image slots Payload} (sign : Route → Bytes → Signature) (pending : Invocation) (packet : Packet Signature)
    (verify : Route → Bytes → Signature → Prop) (available : Invocation → Nat → Prop)
    (genuine : ∀ reply, decode width packet.body = some reply →
      verify (sourceOf reply.invocation) packet.body packet.signature →
      ∃ original, issue width rules ledger origin sign original = some packet)
    (cut : Nat) (accepted : deliver width pending packet verify available = some cut) :
    ∃ reply, Issuable rules ledger origin reply ∧ reply.invocation = pending ∧
      reply.cut = cut ∧ available pending cut ∧ packet.body = encode width reply := by
  cases decoded : decode width packet.body with
  | none => simp [deliver, decoded] at accepted
  | some reply =>
      have applied : RTDBFailover.acceptBarrier pending reply
          (fun _ => verify (sourceOf reply.invocation) packet.body packet.signature) available = some cut := by
        simpa [deliver, decoded] using accepted
      obtain ⟨valid, answers, ready, returned⟩ :=
        RTDBFailover.serving_requires_the_actual_invocation_and_its_materialized_cut pending reply _ available cut applied
      obtain ⟨original, issued⟩ := genuine reply decoded valid
      obtain ⟨chosen, sameBytes, _⟩ := issuance_requires_the_exact_successful_application issued
      have same := Option.some.inj (sameBytes.symm.trans decoded)
      subst original
      exact ⟨reply, chosen, answers, returned.symm, ready, (accepted_reply_bytes_are_canonical decoded).symm⟩

theorem a_chosen_applied_marker_can_issue_and_deliver_from_retained_evidence
    {rules : Rules width slots Payload Ticket} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    {origin : Image slots Payload} {call : Invocation}
    (marker : ChosenMarker rules ledger origin call)
    (active : marker.before.source.source.core.stream.authority = .active call.writer)
    (positive : 0 < width) (fits : Fits width (RTDBFailover.barrierAt call marker.before))
    (sign : Route → Bytes → Signature) (verify : Route → Bytes → Signature → Prop)
    (available : Invocation → Nat → Prop)
    (trusted : let wire := encode width (RTDBFailover.barrierAt call marker.before)
      verify (sourceOf call) wire (sign (sourceOf call) wire))
    (ready : available call marker.before.source.source.core.stream.history.length) :
    ∃ packet, issue width rules ledger origin sign (RTDBFailover.barrierAt call marker.before) = some packet ∧
      deliver width call packet verify available = some marker.before.source.source.core.stream.history.length := by
  let reply := RTDBFailover.barrierAt call marker.before
  let body := encode width reply
  let packet : Packet Signature := ⟨body, sign (sourceOf call) body⟩
  have result : marker.result = .stream (.readCut call.nonce reply.cut) :=
    congrArg Prod.snd (RTDBFailover.the_joint_marker_returns_the_current_cut_and_spends_no_append_credit rules marker.before call active)
  have eligible : Issuable rules ledger origin reply := ⟨marker, rfl, result⟩
  have permitted : 0 < width ∧ Fits width reply ∧ Issuable rules ledger origin reply :=
    ⟨positive, fits, eligible⟩
  have minted : issue width rules ledger origin sign reply = some packet := by
    simp only [issue, ite_eq_left permitted]
    rfl
  have decoded : decode width packet.body = some reply := a_representable_reply_round_trips reply positive fits
  have exactPacket : verify (sourceOf reply.invocation) packet.body packet.signature ∧
      reply.invocation = call ∧ available call reply.cut := ⟨trusted, rfl, ready⟩
  refine ⟨packet, minted, ?_⟩
  simp only [deliver, decoded, RTDBFailover.acceptBarrier]
  exact ite_eq_left exactPacket

#print axioms a_representable_reply_round_trips
#print axioms accepted_reply_bytes_are_canonical
#print axioms an_encoded_reply_has_constant_length
#print axioms one_chosen_marker_position_has_one_applied_result
#print axioms issuance_requires_the_exact_successful_application
#print axioms issuance_proves_the_writer_was_active_at_that_exact_cut
#print axioms a_chosen_refusal_cannot_issue_a_positive_packet
#print axioms accepted_delivery_comes_from_an_exact_issued_marker
#print axioms a_chosen_applied_marker_can_issue_and_deliver_from_retained_evidence

end AppliedBarrierReceipt
