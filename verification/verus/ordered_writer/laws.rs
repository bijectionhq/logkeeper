use crate::production::{
    Authority, Cut, append_next, authorize, commit_append, is_current_enrollment as current, next_epoch,
};
use crate::retention::{trim_records, trimCredit, well_formed_debits};
use crate::AppendClass;
use std::collections::VecDeque;
use vstd::laws_eq::obeys_concrete_eq;
use vstd::prelude::*;

verus! {

// Logkeeper.Kernel.Ordered.authorize_writer
pub open spec fn authorize_writer<E>(
    principal: Option<E>, current: Option<(E, u64, u64)>, presented: (E, u64, u64),
) -> bool {
    principal == Some(presented.0) && current == Some(presented)
}

// Logkeeper.Kernel.Ordered.is_current_enrollment
pub open spec fn is_current_enrollment<E>(installed: Option<E>, presented: E) -> bool {
    installed == Some(presented)
}

pub fn a_displaced_enrollment_cannot_acquire_replay<E: Eq>(installed: Option<E>, presented: E)
    requires obeys_concrete_eq::<E>(),
{
    let admit = current(installed, presented);
    assert(admit == is_current_enrollment(installed, presented));
}

// Logkeeper.Kernel.Ordered.append_next_lsn
pub open spec fn append_next_lsn(head: int, expected: int, limit: int) -> Option<int> {
    if head == expected && expected < limit { Some(expected + 1) } else { None }
}

// Logkeeper.Kernel.Ordered.next_writer_epoch
pub open spec fn next_writer_epoch(epoch: int, limit: int) -> Option<int> {
    if epoch < limit { Some(epoch + 1) } else { None }
}

// Logkeeper.Kernel.Ordered.withdraw_grant
pub open spec fn withdraw_grant<G>(grant: Option<G>, holder_matches: bool) -> Option<G> {
    if holder_matches { None } else { grant }
}

pub enum AbstractAuthority<G> {
    Active(G),
    Vacant(G),
}

pub open spec fn abstract_authority<G>(grant: Option<G>, previous: G) -> AbstractAuthority<G> {
    match grant {
        Some(current) => AbstractAuthority::Active(current),
        None => AbstractAuthority::Vacant(previous),
    }
}

pub fn append_only_by_current_grant_at_next_lsn<E: Eq + Copy>(
    head: u64, expected: u64, principal: Option<E>, current: Option<(E, u64, u64)>,
    presented: (E, u64, u64),
)
    requires obeys_concrete_eq::<E>(),
{
    let writer = authorize(principal, current, presented);
    if let Ok(()) = writer {
        assert(authorize_writer(principal, current, presented));
        let next = append_next(head, expected);
        match next {
            Ok(value) => {
                assert(append_next_lsn(head as int, expected as int, u64::MAX as int)
                    == Some(value as int) && expected == head && value as int == head as int + 1);
            },
            Err(_) => {
                assert(append_next_lsn(head as int, expected as int, u64::MAX as int).is_none());
            },
        }
    } else {
        assert(!authorize_writer(principal, current, presented));
    }
}

pub(super) fn grant_installation_fences_older_epochs<G>(
    authority: &mut Authority<G>, generation: u64, grant: G, superseded_epoch: u64,
)
    requires superseded_epoch <= old(authority).epoch,
{
    let epoch = authority.epoch;
    match next_epoch(epoch) {
        Ok(next) => {
            authority.install(next, generation, grant);
            assert(next_writer_epoch(epoch as int, u64::MAX as int) == Some(authority.epoch as int)
                && superseded_epoch < authority.epoch && authority.grant == Some(grant)
                && authority.key_generation == generation
                && abstract_authority(authority.grant, grant) == AbstractAuthority::Active(grant));
        },
        Err(_) => {
            assert(next_writer_epoch(epoch as int, u64::MAX as int).is_none());
        },
    }
}

pub fn withdrawal_clears_only_the_matching_grant<G>(
    authority: &mut Authority<G>, holder_matches: bool,
) {
    let ghost before = *authority;
    authority.withdraw(holder_matches);
    assert(authority.grant == withdraw_grant(before.grant, holder_matches)
        && authority.epoch == before.epoch && authority.key_generation == before.key_generation);
}

pub fn vacancy_clears_the_grant<G>(authority: &mut Authority<G>) {
    let ghost before = *authority;
    authority.vacate();
    assert(authority.grant == withdraw_grant(before.grant, true)
        && authority.epoch == before.epoch && authority.key_generation == before.key_generation);
}

// History field of Logkeeper.Kernel.Ordered.abstract_state.
pub open spec fn abstract_history<R>(compacted: Seq<R>, records: Seq<R>) -> Seq<R> {
    compacted + records
}

pub open spec fn abstract_state<G, R>(
    grant: Option<G>, previous: G, compacted: Seq<R>, records: Seq<R>,
) -> (AbstractAuthority<G>, Seq<R>) {
    (abstract_authority(grant, previous), abstract_history(compacted, records))
}

pub fn applied_append_extends_history<G, R>(
    records: &mut VecDeque<R>, head: &mut Cut, expected: u64, record: R,
    history_digest: [u8; 32], Ghost(compacted): Ghost<Seq<R>>, Ghost(writer): Ghost<G>,
)
    requires old(head).next_lsn as int == abstract_state(Some(writer), writer, compacted, old(records)@).1.len(),
{
    let ghost before = abstract_state(Some(writer), writer, compacted, records@);
    if let Ok(next_lsn) = append_next(head.next_lsn, expected) {
        let cut = Cut { next_lsn, history: history_digest };
        commit_append(records, head, record, cut);
        let ghost after = abstract_state(Some(writer), writer, compacted, records@);
        assert(after.0 == before.0 && after.1 =~= before.1.push(record));
        assert(head.next_lsn == after.1.len() && after.1[expected as int] == record);
    }
}

pub fn trim_keeps_the_logical_history<G, R, P: Fn(&R) -> (AppendClass, u64, u64)>(
    records: &mut VecDeque<R>, count: usize, ordinary: &mut u64, maintenance: &mut u64,
    project: P, debit: Ghost<Map<R, (AppendClass, u64, u64)>>,
    Ghost(compacted): Ghost<Seq<R>>, Ghost(grant): Ghost<Option<G>>, Ghost(previous): Ghost<G>,
)
    requires count <= old(records)@.len(),
        well_formed_debits(project, debit@, old(records)@),
        (*old(ordinary) as nat, *old(maintenance) as nat)
            == trimCredit(old(records)@, old(records)@.len(), debit@),
{
    let ghost original = records@;
    let ghost before = abstract_state(grant, previous, compacted, original);
    let _ = trim_records(records, count, ordinary, maintenance, project, debit);
    let ghost newly_compacted = compacted + original.take(count as int);
    assert(abstract_state(grant, previous, newly_compacted, records@) =~= before);
}

}
