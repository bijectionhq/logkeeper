use super::*;

const A: KeeperId = KeeperId(1);
const B: KeeperId = KeeperId(2);
const C: KeeperId = KeeperId(3);
const C2: KeeperId = KeeperId(4);
const C3: KeeperId = KeeperId(5);
const D: KeeperId = KeeperId(6);

fn roster(members: &[(KeeperId, &str)]) -> Roster {
    Roster::new(members.iter().map(|(id, zone)| Member {
        id: *id,
        zone: (*zone).into(),
    }))
}

#[test]
fn a_spare_comes_from_the_lost_keepers_zone_and_is_stable_per_stream() {
    let roster = roster(&[(A, "a"), (B, "b"), (C, "c"), (C2, "c"), (C3, "c"), (D, "d")]);
    let ensemble = [A, B, C];
    let picks: Vec<_> = (0..4)
        .map(|stream| roster.spare(StreamId(stream), ensemble, C, &[]))
        .collect();
    assert_eq!(picks, [Some(C2), Some(C3), Some(C2), Some(C3)]);
    assert_eq!(roster.spare(StreamId(1), ensemble, C, &[]), picks[1]);
    // An unavailable spare is skipped; with none left in the zone, a free zone serves.
    assert_eq!(roster.spare(StreamId(1), ensemble, C, &[C3]), Some(C2));
    assert_eq!(roster.spare(StreamId(1), ensemble, C, &[C2, C3]), Some(D));
}

#[test]
fn no_spare_shares_a_survivors_zone() {
    let roster = roster(&[(A, "a"), (B, "b"), (C, "c"), (D, "a")]);
    assert_eq!(roster.spare(StreamId(0), [A, B, C], C, &[]), None);
    assert_eq!(roster.spare(StreamId(0), [A, B, C], A, &[]), Some(D));
}

#[test]
fn an_interrupted_move_names_its_learner_only_in_the_lost_slot() {
    assert_eq!(learner_of([A, B, C], C, [A, B, C2]), Some(C2));
    assert_eq!(learner_of([A, B, C], C, [A, B, C]), None);
    assert_eq!(
        learner_of([A, B, C], C, [A, C2, C]),
        None,
        "another slot changed"
    );
    assert_eq!(
        learner_of([A, B, C], C, [A, B, A]),
        None,
        "an existing member"
    );
    assert_eq!(
        learner_of([A, B, C], C, [D, B, C2]),
        None,
        "two slots changed"
    );
}
