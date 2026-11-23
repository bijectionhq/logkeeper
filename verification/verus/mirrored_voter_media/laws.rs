use crate::production::{
    Ballot, Error, Fingerprint, Inner, Media, SlotPair, VoterState, mirrored,
    reads_both_images, reply_requires_both_syncs,
};
use crate::production::selection::*;
use vstd::prelude::*;

verus! {

pub open spec fn state_of(input: Option<(u64, VoterState)>) -> Option<VoterState> {
    match input { Some((_, state)) => Some(state), None => None }
}

pub enum SyncPhase {
    Started,
    AlternateSynced,
    SelectedSynced,
    Acknowledged,
}

pub enum SyncEvent {
    Sync(usize),
    Reply,
}

pub open spec fn sync_step(selected: usize, phase: SyncPhase, event: SyncEvent) -> Option<SyncPhase> {
    match (phase, event) {
        (SyncPhase::Started, SyncEvent::Sync(index)) if index as int == 1 - selected as int =>
            Some(SyncPhase::AlternateSynced),
        (SyncPhase::AlternateSynced, SyncEvent::Sync(index)) if index == selected =>
            Some(SyncPhase::SelectedSynced),
        (SyncPhase::SelectedSynced, SyncEvent::Reply) => Some(SyncPhase::Acknowledged),
        _ => None,
    }
}

pub open spec fn sync_trace(selected: usize, phase: SyncPhase, writes: Seq<usize>) -> Option<SyncPhase>
    decreases writes.len(),
{
    if writes.len() == 0 {
        Some(phase)
    } else {
        match sync_step(selected, phase, SyncEvent::Sync(writes[0])) {
            Some(next) => sync_trace(selected, next, writes.skip(1)),
            None => None,
        }
    }
}

pub open spec fn acknowledged(before: Media, after: Media) -> bool {
    let selected = before.selected.unwrap();
    let writes = after.writes@.skip(before.writes@.len() as int);
    sync_trace(selected, SyncPhase::Started, writes) matches Some(phase)
        && sync_step(selected, phase, SyncEvent::Reply) == Some(SyncPhase::Acknowledged)
}

pub open spec fn ballot_le(earlier: Ballot, later: Ballot) -> bool {
    earlier.round < later.round || earlier.round == later.round && earlier.nonce <= later.nonce
}

pub open spec fn promise_le(earlier: Option<Ballot>, later: Option<Ballot>) -> bool {
    match earlier {
        None => true,
        Some(a) => later matches Some(b) && ballot_le(a, b),
    }
}

pub open spec fn dominates(later: VoterState, earlier: VoterState) -> bool {
    promise_le(earlier.promised, later.promised)
    && match earlier.accepted {
        None => true,
        Some((ballot, len)) => match later.accepted {
            None => false,
            Some((new_ballot, new_len)) => ballot_le(ballot, new_ballot)
                && (ballot == new_ballot ==> len <= new_len),
        },
    }
}

pub open spec fn keeps(floor: VoterState, media: Seq<Option<VoterState>>) -> bool {
    media.len() == 2 && forall|i: int| 0 <= i < 2 && #[trigger] media[i].is_some()
        ==> dominates(media[i].unwrap(), floor)
}

// SelectionFence.Step.write and .tear. A torn header and a torn body both
// project to None once the file reader and digest contract reject them.
proof fn a_sync_or_tear_keeps_the_acknowledged_rank(
    floor: VoterState, before: Seq<Option<VoterState>>, index: int, next: Option<VoterState>,
)
    requires keeps(floor, before), 0 <= index < 2,
        next.is_some() ==> before[1 - index].is_some()
            && dominates(next.unwrap(), before[1 - index].unwrap()),
    ensures keeps(floor, before.update(index, next)),
{
    if next.is_some() {
        assert(before[1 - index].is_some());
        assert(dominates(next.unwrap(), floor));
    }
}

}

verus! {

fn a_reply_requires_both_syncs(voter: &Inner, media: &mut Media, next: VoterState)
    -> (out: Result<SlotPair, Error>)
    requires old(media).selected matches Some(i) && i < 2,
    ensures out matches Ok(pair) ==> mirrored(*final(media), next, pair)
        && acknowledged(*old(media), *final(media)),
{
    let ghost initial = *media;
    let result = voter.mirror(media, next);
    proof {
        if result.is_ok() {
            assert(reply_requires_both_syncs(initial, *media));
            let selected = initial.selected.unwrap();
            let writes = media.writes@.skip(initial.writes@.len() as int);
            assert(writes =~= seq![(1 - selected) as usize, selected]);
            assert(writes.skip(1) =~= seq![selected]);
            assert(writes.skip(2) =~= Seq::<usize>::empty());
            assert(writes.skip(1).skip(1) =~= Seq::<usize>::empty());
            reveal_with_fuel(sync_trace, 3);
        }
    }
    result
}

}

#[verus_spec(out =>
    ensures out.is_ok() ==> reads_both_images(*old(media), *final(media), ballot, digest, pair),
)]
fn read_back_visits_both_physical_slots(
    voter: &Inner, media: &mut Media, ballot: Ballot, digest: Fingerprint, pair: SlotPair,
) -> Result<(), Error> {
    voter.read_back(media, ballot, digest, pair)
}

#[verus_spec(out =>
    requires a < b,
    ensures out matches Ok(Some(1)),
)]
fn selection_prefers_the_newer_generation(a: u64, b: u64) -> Result<Option<usize>, Error> {
    select_slot(Some(a), Some(b))
}

#[verus_spec(out =>
    requires keeps(floor@, seq![state_of(first), state_of(second)]),
    ensures out matches Ok(Some(image)) ==> dominates(image, floor@)
            && (state_of(first) == Some(image) || state_of(second) == Some(image)),
        first.is_some() != second.is_some() ==> out matches Ok(Some(_)),
)]
fn any_surviving_slot_keeps_the_acknowledged_rank(
    floor: Ghost<VoterState>, first: Option<(u64, VoterState)>, second: Option<(u64, VoterState)>,
) -> Result<Option<VoterState>, Error> {
    let a = match first { Some((generation, _)) => Some(generation), None => None };
    let b = match second { Some((generation, _)) => Some(generation), None => None };
    let selected = select_slot(a, b)?;
    let image = match selected {
        Some(0) => match first { Some((_, image)) => Some(image), None => None },
        Some(1) => match second { Some((_, image)) => Some(image), None => None },
        _ => None,
    };
    proof! {
        let media = seq![state_of(first), state_of(second)];
        assert(media[0] == state_of(first));
        assert(media[1] == state_of(second));
    }
    Ok(image)
}

#[verus_spec(out =>
    requires first.1 == ack@, second.1 == ack@,
    ensures out == Ok(Some(ack@)),
)]
fn one_detectable_tear_after_ack_selects_the_acknowledged_image(
    ack: Ghost<VoterState>, first: (u64, VoterState), second: (u64, VoterState), tear_second: bool,
) -> Result<Option<VoterState>, Error> {
    let a = if tear_second { Some(first) } else { None };
    let b = if tear_second { None } else { Some(second) };
    proof! {
        assert(dominates(ack@, ack@));
        let media = seq![state_of(a), state_of(b)];
        assert(media[0] == state_of(a) && media[1] == state_of(b));
        assert(keeps(ack@, media));
    }
    any_surviving_slot_keeps_the_acknowledged_rank(ack, a, b)
}

#[verus_spec(result =>
    requires computed@ != stored@,
    ensures !result,
)]
fn a_mismatched_digest_is_ineligible(computed: &[u8], stored: &[u8]) -> bool {
    authenticates_body(computed, stored)
}
