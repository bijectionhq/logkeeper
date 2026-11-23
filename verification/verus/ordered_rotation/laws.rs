use crate::production::{
    admits_history as may_admit_history, check_preparation, check_rotation, publish_selection,
    successor_generation as checked_successor,
};
use crate::writer::{Authority, Cut, authorize, next_epoch};
use vstd::laws_eq::obeys_concrete_eq;
use vstd::prelude::*;

verus! {

// ErasureCommit.rotation_head: a cut includes both the LSN and the prefix digest.
pub open spec fn rotation_head<G, C>(
    custodian: bool, current: Option<G>, grant: G, head: Cut, cut: Cut,
    published: C, requested: C,
) -> bool {
    &&& custodian
    &&& current == Some(grant)
    &&& head.next_lsn == cut.next_lsn
    &&& head.history@ == cut.history@
    &&& published != requested
}

// ErasureCommit.exact_preparation.
pub open spec fn exact_preparation<C>(
    prepared_cut: Cut, cut: Cut, prepared_root: Seq<u8>, root: Seq<u8>,
    prepared_custody: C, custody: C, manifest_present: bool, observed: Option<Cut>,
) -> bool {
    &&& manifest_present
    &&& prepared_cut.next_lsn == cut.next_lsn
    &&& prepared_cut.history@ == cut.history@
    &&& prepared_root == root
    &&& prepared_custody == custody
    &&& observed matches Some(seen) && seen.next_lsn == cut.next_lsn && seen.history@ == cut.history@
}

// ErasureCommit.successor_generation, using the X2 next_writer_epoch bound.
pub open spec fn successor_generation<G, C>(
    erasure: bool, source: G, grant: G, base: C, published: C, generation: u64,
) -> Option<u64> {
    if erasure && source == grant && base == published && generation < u64::MAX {
        Some((generation as int + 1) as u64)
    } else {
        None
    }
}

// ErasureCommit.erasure_floor and .admits_history.
pub open spec fn erasure_floor(previous: u64, chosen_cut: u64, closes_history: bool) -> u64 {
    if closes_history { chosen_cut } else { previous }
}

pub open spec fn admits_history(floor: u64, start: u64) -> bool {
    floor <= start
}

fn rotation_requires_exact_incumbent_and_head<G: Eq + Copy, C: Eq + Copy>(
    custodian: bool, current: Option<G>, grant: G, head: Cut, cut: Cut,
    published: C, requested: C,
)
    requires obeys_concrete_eq::<G>(), obeys_concrete_eq::<C>(),
{
    let result = check_rotation(custodian, current, grant, head, published, requested, cut);
    assert((result is Ok) == rotation_head(custodian, current, grant, head, cut, published, requested));
}

fn rotation_requires_exact_preparation<C: Eq + Copy>(
    prepared_cut: Cut, cut: Cut, prepared_root: [u8; 32], root: [u8; 32],
    prepared_custody: C, custody: C, manifest: [u8; 32], observed: Option<Cut>,
)
    requires obeys_concrete_eq::<C>(),
{
    let result = check_preparation(
        prepared_cut, prepared_root, prepared_custody, cut, root, custody, manifest, observed,
    );
    assert((result is Ok) == exact_preparation(
        prepared_cut, cut, prepared_root@, root@, prepared_custody, custody,
        manifest@ != Seq::new(32, |_: int| 0u8), observed,
    ));
}

fn rotation_installs_successor_generation<G: Eq + Copy, C: Eq + Copy>(
    erasure: bool, source: G, grant: G, base: C, published: C, generation: u64,
)
    requires obeys_concrete_eq::<G>(), obeys_concrete_eq::<C>(),
{
    let result = checked_successor(erasure, source, grant, base, published, generation);
    assert(result.ok() == successor_generation(erasure, source, grant, base, published, generation));
}

fn rotated_suffix_refuses_superseded_grant<E: Eq + Copy, C: Eq + Copy>(
    authority: &mut Authority<(E, u64, u64)>, owner: E, checkpoint: C,
) -> Result<(), crate::Refusal>
    requires
        obeys_concrete_eq::<E>(), obeys_concrete_eq::<C>(),
        old(authority).grant == Some((owner, old(authority).epoch, old(authority).key_generation)),
{
    let original = (owner, authority.epoch, authority.key_generation);
    let generation = checked_successor(true, owner, owner, checkpoint, checkpoint, original.2)?;
    let epoch = next_epoch(authority.epoch)?;
    let successor = (owner, epoch, generation);
    authority.install(epoch, generation, successor);
    assert(authority.epoch as int == original.1 as int + 1
        && authority.key_generation as int == original.2 as int + 1);
    let stale = authorize(Some(owner), authority.grant, original);
    let fresh = authorize(Some(owner), authority.grant, successor);
    assert(stale is Err && fresh is Ok);
    Ok(())
}

fn generation_survives_vacancy<E: Copy>(
    authority: &mut Authority<(E, u64, u64)>, owner: E,
) -> Result<(), crate::Refusal> {
    let old_generation = authority.key_generation;
    authority.vacate();
    let generation = authority.key_generation;
    assert(authority.grant == None && generation == old_generation);
    let epoch = next_epoch(authority.epoch)?;
    authority.install(epoch, generation, (owner, epoch, generation));
    assert(authority.key_generation == old_generation);
    Ok(())
}

fn publication_closes_old_history<C: Copy, P>(
    published: &mut C, preparing: &mut Option<P>, floor: &mut u64,
    checkpoint: C, cut: Cut, start: u64, closes_history: bool,
) {
    let previous = *floor;
    publish_selection(published, preparing, floor, checkpoint, cut, closes_history);
    let admitted = may_admit_history(*floor, start);
    assert(*published == checkpoint && *preparing == None
        && admitted == admits_history(erasure_floor(previous, cut.next_lsn, closes_history), start));
}

}
