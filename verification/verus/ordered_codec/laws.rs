use crate::production::{
    bodyLengthBounded, commandVersion, decisionHeader, decisionRequestBytes,
    decision_header, decision_request_parts, decode_flag, encode_flag,
    has_command_version, object_name_count, read_decision_time, bounded_body_length,
    read_fixed_field, withdrawal_identity_admissible, withdrawn_worker_count_bounded,
};
use crate::domains::{
    CommandAdmission, OperationAdmission, ReplyAdmission, commandAdmissible, decisionBodyAdmissible,
    serviceOperationAdmissible, serviceReplyAdmissible,
};
use crate::object_names::valid_object_names;
use crate::ObjectName;
use vstd::prelude::*;

verus! {

fn decision_time_round_trips(time: [u8; 8]) {
    let header = decision_header(time);
    let decoded = read_decision_time(&header);
    assert(decoded matches Some(copy) && copy@ == time@);
}

fn short_decision_header_is_rejected(frame: &[u8])
    requires frame@.len() < 9,
{
    let decoded = read_decision_time(frame);
    assert(decoded is None);
}

fn decision_request_bytes_round_trip(
    frame: &[u8], time: [u8; 8], Ghost(request): Ghost<Seq<u8>>,
    Ghost(command): Ghost<CommandAdmission>,
)
    requires
        decisionBodyAdmissible(time@, command),
        request.len() > 0, request[0] == commandVersion(),
        frame@ == decisionHeader(time@) + request.skip(1),
{
    let decoded = decision_request_parts(frame);
    assert(decisionRequestBytes(frame@) =~= request);
    assert(decoded matches Some((stamp, version, fields))
        && stamp@ =~= time@ && version@ + fields@ =~= request);
}

fn fixed_field_round_trips_with_suffix<const N: usize>(
    frame: &[u8], field: [u8; N], Ghost(suffix): Ghost<Seq<u8>>,
)
    requires frame@ == field@ + suffix,
{
    let decoded = read_fixed_field::<N>(frame);
    assert(frame@.take(N as int) =~= field@);
    assert(decoded matches Some(copy) && copy@ =~= field@);
}

fn withdrawal_command_admission_requires_both_nonzero_fields(name: [u8; 32], version: [u8; 32]) {
    let accepted = withdrawal_identity_admissible(&name, &version);
    assert(accepted == commandAdmissible(CommandAdmission::WithdrawObject(name, version)));
    assert(accepted ==> name@ != Seq::new(32, |_i| 0u8) && version@ != Seq::new(32, |_i| 0u8));
}

fn referenced_commands_and_operations_share_the_name_domain(names: &[ObjectName]) {
    let accepted = valid_object_names(names);
    let ghost append = CommandAdmission::Append(Some(names@));
    let ghost prepare = CommandAdmission::PrepareCheckpoint(Some(names@));
    assert(accepted == commandAdmissible(append));
    assert(accepted == commandAdmissible(prepare));
    assert(accepted == serviceOperationAdmissible(OperationAdmission::Execute(append)));
    assert(accepted == serviceOperationAdmissible(OperationAdmission::Reconcile(append)));
}

fn admitted_withdrawn_worker_count_round_trips(count: usize)
    requires serviceReplyAdmissible(ReplyAdmission::WithdrawnWorkers(count as nat)),
{
    let encoded = count as u8;
    let decoded = usize::from(encoded);
    let accepted = withdrawn_worker_count_bounded(decoded);
    assert(accepted && decoded == count);
}

fn oversized_withdrawn_worker_count_is_rejected(count: u8)
    requires count > 64,
{
    let accepted = withdrawn_worker_count_bounded(usize::from(count));
    assert(!accepted);
}

fn wrong_command_version_is_rejected(version: u8)
    requires version != commandVersion(),
{
    let admitted = has_command_version(version);
    assert(!admitted);
}

fn flag_round_trips(value: bool) {
    let marker = encode_flag(value);
    let decoded = decode_flag(marker);
    assert(decoded == Some(value));
}

fn noncanonical_flag_is_rejected(tag: u8)
    requires tag > 1,
{
    let decoded = decode_flag(tag);
    assert(decoded is None);
}

fn body_over_limit_is_rejected(declared: u64, minimum: usize, maximum: usize)
    requires maximum < declared,
{
    let decoded = bounded_body_length(declared, minimum, maximum);
    assert(!bodyLengthBounded(declared as int, minimum as int, maximum as int));
    assert(decoded is None);
}

fn a_torn_object_name_is_rejected(declared: u32, maximum: usize, remaining: usize)
    requires remaining < 32 * declared as int,
{
    let count = object_name_count(declared, maximum, remaining);
    assert(count is None);
}

}
