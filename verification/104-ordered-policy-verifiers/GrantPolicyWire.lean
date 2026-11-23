import GrantReadPolicy

set_option warningAsError true

namespace GrantPolicyWire

open EnvelopeCodec (Bytes word wordLimit readWord readFields flattenFields)
open ChosenReplay (Lineage)

structure Message where
  lineage : Lineage
  writer : Kernel.Writer
  horizon : Nat
  version : Nat

def binding (message : Message) : GrantReadPolicy.Binding :=
  ⟨message.lineage, some message.writer, message.horizon⟩

def fields (message : Message) : List Nat :=
  [message.lineage.stream, message.lineage.incarnation,
    message.writer.placement.group, message.writer.placement.generation,
    message.writer.epoch, message.writer.holder, message.horizon, message.version]

def assemble : List Nat → Option Message
  | [stream, incarnation, group, generation, epoch, holder, horizon, version] =>
    some ⟨⟨stream, incarnation⟩, ⟨⟨group, generation⟩, epoch, holder⟩, horizon, version⟩
  | _ => none

def domain : UInt8 := 5

def Fits (width : Nat) (message : Message) : Prop := ∀ value ∈ fields message, value < wordLimit width

def encode (width : Nat) (message : Message) : Bytes :=
  domain :: flattenFields ((fields message).map (word width))

def decode (width : Nat) : Bytes → Option Message
  | tag :: raw =>
    if tag = domain ∧ 0 < width then
      (readFields width 8 raw).bind fun words => assemble (words.map (fun field => readWord field.val))
    else none
  | [] => none

private theorem assemble_own_fields (message : Message) : assemble (fields message) = some message := by
  rcases message with ⟨⟨stream, incarnation⟩, ⟨⟨group, generation⟩, epoch, holder⟩, horizon, version⟩
  rfl

private theorem assembly_binds_fields {words : List Nat} {message : Message}
    (opened : assemble words = some message) : fields message = words := by
  unfold assemble at opened
  split at opened
  · cases opened
    rfl
  · contradiction

theorem a_policy_message_round_trips_exactly (width : Nat) (message : Message) (positive : 0 < width)
    (fits : Fits width message) : decode width (encode width message) = some message := by
  have exactWords : readFields width 8 (flattenFields ((fields message).map (word width))) =
      some ((fields message).map (word width)) := by
    have parsed := EnvelopeCodec.readFields_after_flatten ((fields message).map (word width))
    simpa only [List.length_map, fields, List.length_cons, List.length_nil, Nat.reduceAdd] using parsed
  have decoded : ((fields message).map (word width)).map (fun field => readWord field.val) = fields message := by
    rw [List.map_map]
    refine Eq.trans ?_ (List.map_id _)
    apply List.map_congr_left
    intro item present
    exact EnvelopeCodec.fixed_width_words_roundtrip (fits item present)
  simp only [encode, decode, true_and, ite_eq_left positive, exactWords]
  change assemble (((fields message).map (word width)).map (fun field => readWord field.val)) = some message
  rw [decoded, assemble_own_fields]

theorem decoded_policy_bytes_have_one_canonical_encoding {width : Nat} {wire : Bytes} {message : Message}
    (decoded : decode width wire = some message) : encode width message = wire := by
  cases wire with
  | nil => simp [decode] at decoded
  | cons tag raw =>
    simp only [decode] at decoded
    split at decoded
    · next valid =>
      cases parsed : readFields width 8 raw with
      | none => simp [parsed] at decoded
      | some words =>
        have built : assemble (words.map (fun field => readWord field.val)) = some message := by
          simpa [parsed] using decoded
        have sameWords : (fields message).map (word width) = words := by
          rw [assembly_binds_fields built, List.map_map]
          refine Eq.trans ?_ (List.map_id _)
          apply List.map_congr_left
          intro field _
          exact EnvelopeCodec.readField_recovers_the_exact_word field
        simp [encode, valid.1, sameWords, EnvelopeCodec.readFields_recovers_the_exact_wire parsed]
    · contradiction

theorem each_policy_message_has_a_fixed_signed_size (width : Nat) (message : Message) :
    (encode width message).length = 1 + 8 * width := by
  simp [encode, fields, EnvelopeCodec.flattenFields_size, Nat.add_comm]

structure Packet (Signature : Type) where
  body : Bytes
  signature : Signature

structure Verifier (Key : Type) where
  version : Nat
  key : Key

def CurrentVersion (seen expected : Nat) : Prop :=
  seen = expected

theorem a_verified_offer_uses_the_exact_current_version (seen expected : Nat)
    (current : CurrentVersion seen expected) : seen = expected := by
  exact current

noncomputable def authenticate (width : Nat) (current : Verifier Key)
    (valid : Key → Bytes → Signature → Prop) (packet : Packet Signature) :
    Option GrantReadPolicy.Binding := by
  classical
  exact do
    let message ← decode width packet.body
    if CurrentVersion message.version current.version ∧ valid current.key packet.body packet.signature then
      some (binding message)
    else none

theorem a_verified_offer_returns_only_its_exact_signed_scope
    (width : Nat) (current : Verifier Key) (valid : Key → Bytes → Signature → Prop)
    (packet : Packet Signature) (policy : GrantReadPolicy.Binding)
    (accepted : authenticate width current valid packet = some policy) :
    ∃ message, decode width packet.body = some message ∧ message.version = current.version ∧
      valid current.key (encode width message) packet.signature ∧ policy = binding message := by
  cases decoded : decode width packet.body with
  | none => simp [authenticate, decoded] at accepted
  | some message =>
    by_cases checks : CurrentVersion message.version current.version ∧ valid current.key packet.body packet.signature
    · have same : binding message = policy := by simpa [authenticate, decoded, checks] using accepted
      exact ⟨message, rfl, a_verified_offer_uses_the_exact_current_version _ _ checks.1,
        (decoded_policy_bytes_have_one_canonical_encoding decoded).symm ▸ checks.2, same.symm⟩
    · simp [authenticate, decoded, checks] at accepted

theorem a_packet_from_a_retired_version_refuses_fresh_use
    (width : Nat) (current : Verifier Key) (valid : Key → Bytes → Signature → Prop)
    (packet : Packet Signature) (old : Message)
    (decoded : decode width packet.body = some old) (retired : old.version ≠ current.version) :
    authenticate width current valid packet = none := by
  have rejects : ¬ (CurrentVersion old.version current.version ∧ valid current.key packet.body packet.signature) :=
    fun checked => retired (a_verified_offer_uses_the_exact_current_version _ _ checked.1)
  simp [authenticate, decoded, rejects]

#print axioms a_policy_message_round_trips_exactly
#print axioms decoded_policy_bytes_have_one_canonical_encoding
#print axioms each_policy_message_has_a_fixed_signed_size
#print axioms a_verified_offer_uses_the_exact_current_version
#print axioms a_verified_offer_returns_only_its_exact_signed_scope
#print axioms a_packet_from_a_retired_version_refuses_fresh_use

end GrantPolicyWire
