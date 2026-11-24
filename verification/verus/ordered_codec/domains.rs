use crate::ObjectName;
use crate::object_names::objectNamesCanonical;
use crate::production::{
    withdrawalIdentityAdmissible, withdrawnWorkerCountBounded,
};
use vstd::prelude::*;

verus! {

pub(super) open spec fn optionalObjectNamesAdmissible(names: Option<Seq<ObjectName>>) -> bool {
    match names {
        None => true,
        Some(names) => objectNamesCanonical(names),
    }
}

pub(super) ghost enum CommandAdmission {
    FixedFields,
    Append(Option<Seq<ObjectName>>),
    PrepareCheckpoint(Option<Seq<ObjectName>>),
    WithdrawObject(ObjectName, ObjectName),
}

pub(super) open spec fn commandAdmissible(command: CommandAdmission) -> bool {
    match command {
        CommandAdmission::FixedFields => true,
        CommandAdmission::Append(names) | CommandAdmission::PrepareCheckpoint(names)
            => optionalObjectNamesAdmissible(names),
        CommandAdmission::WithdrawObject(name, version)
            => withdrawalIdentityAdmissible(name@, version@),
    }
}

pub(super) open spec fn decisionBodyAdmissible(time: Seq<u8>, command: CommandAdmission) -> bool {
    time.len() == 8 && commandAdmissible(command)
}

pub(super) ghost enum OperationAdmission {
    FixedFields,
    Execute(CommandAdmission),
    Reconcile(CommandAdmission),
}

pub(super) open spec fn serviceOperationAdmissible(operation: OperationAdmission) -> bool {
    match operation {
        OperationAdmission::FixedFields => true,
        OperationAdmission::Execute(command) | OperationAdmission::Reconcile(command)
            => commandAdmissible(command),
    }
}

pub(super) open spec fn recordAdmissible(payload_bytes: nat, names: Option<Seq<ObjectName>>) -> bool {
    payload_bytes < 0x8000_0000_0000_0000int && optionalObjectNamesAdmissible(names)
}

pub(super) ghost enum DecisionAdmission {
    Plain(bool),
    Barrier { exact_receipt: bool, canonical_claim: bool },
    Rotation { has_barrier: bool, covers_receipt: bool },
}

pub(super) open spec fn serviceDecisionAdmissible(decision: DecisionAdmission) -> bool {
    match decision {
        DecisionAdmission::Plain(barrier) => !barrier,
        DecisionAdmission::Barrier { exact_receipt, canonical_claim } => exact_receipt && canonical_claim,
        DecisionAdmission::Rotation { has_barrier, covers_receipt } => !has_barrier && covers_receipt,
    }
}

pub(super) ghost enum ReplyAdmission {
    FixedFields,
    Decision(Option<(ObjectName, ObjectName)>, DecisionAdmission),
    Replay(Seq<(nat, Option<Seq<ObjectName>>)>),
    WithdrawnWorkers(nat),
}

pub(super) open spec fn serviceReplyAdmissible(reply: ReplyAdmission) -> bool {
    match reply {
        ReplyAdmission::FixedFields => true,
        ReplyAdmission::Decision(withdrawal, evidence) => {
            (match withdrawal {
                None => true,
                Some((name, version)) => withdrawalIdentityAdmissible(name@, version@),
            }) && serviceDecisionAdmissible(evidence)
        },
        ReplyAdmission::Replay(records) => forall|i: int| 0 <= i < records.len() ==> {
            let row = #[trigger] records[i];
            recordAdmissible(row.0, row.1)
        },
        ReplyAdmission::WithdrawnWorkers(count) => withdrawnWorkerCountBounded(count as int),
    }
}

}
