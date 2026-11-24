use crate::production::{acknowledged, outranks};
use vstd::prelude::*;

verus! {

pub fn one_keeper_cannot_head(epoch: u64, at: u64) {
    let chosen = acknowledged(Some((epoch, at)), None, None, epoch, at);
    assert(!chosen);
}

pub fn an_ack_in_another_epoch_cannot_head(epoch: u64, newer: u64, at: u64)
    requires newer > epoch,
{
    let chosen = acknowledged(Some((epoch, at)), Some((newer, at)), None, epoch, at);
    assert(!chosen);
}

pub fn an_ack_for_a_shorter_prefix_cannot_head(epoch: u64, at: u64, short: u64)
    requires at > short,
{
    let chosen = acknowledged(Some((epoch, at)), Some((epoch, short)), None, epoch, at);
    assert(!chosen);
}

pub fn either_pair_of_survivors_can_head(epoch: u64, at: u64, missing: u8)
    requires missing < 3,
{
    let ack = Some((epoch, at));
    let a = if missing == 0 { None } else { ack };
    let b = if missing == 1 { None } else { ack };
    let c = if missing == 2 { None } else { ack };
    let chosen = acknowledged(a, b, c, epoch, at);
    assert(chosen);
}

pub fn latest_synced_wins_even_if_shorter(older: u64, newer: u64, short: u64, long: u64)
    requires older < newer, short < long,
{
    let prefer_newer = outranks(Some(older), long, Some(newer), short);
    assert(prefer_newer);
}

pub fn longer_history_wins_at_equal_synced(epoch: u64, short: u64, long: u64)
    requires short < long,
{
    let prefer_longer = outranks(Some(epoch), short, Some(epoch), long);
    assert(prefer_longer);
}

pub fn synced_zero_outranks_no_synced_epoch(tail: u64) {
    let prefer_synced = outranks(None, tail, Some(0), 0);
    assert(prefer_synced);
}

}
