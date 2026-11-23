import AtomicPublication

set_option warningAsError true

open AtomicPublication

noncomputable def finishExisting {capacity : Nat} {Borrow Signature : Type} (use : ReplyUse capacity Borrow Signature)
    (held : RTDBFailover.Invocation → RecoverableRead.Permit capacity → SnapshotAdmission.Basis → Borrow → Prop) :
    Option (AppliedBarrierReceipt.Packet Signature) :=
  finishReply use held
