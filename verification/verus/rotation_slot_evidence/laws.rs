use crate::production::*;
use crate::production::evidence::{record_vote, register_peer, strict_majority};
use vstd::prelude::*;

verus! {

pub open spec fn distinct_voters(rows: Seq<VoterSlots>) -> bool {
    forall|i: int, j: int| #![trigger rows[i].voter, rows[j].voter]
        0 <= i < j < rows.len() ==> rows[i].voter != rows[j].voter
}

proof fn ordered_rows_are_distinct(rows: Seq<VoterSlots>, i: int, j: int)
    requires valid_voter_prefix(rows, rows.len() as int), 0 <= i < j < rows.len(),
    ensures rows[i].voter.0 < rows[j].voter.0,
    decreases j - i,
{
    if j > i + 1 {
        ordered_rows_are_distinct(rows, i, j - 1);
    }
}

pub open spec fn at_fence(vote: Vote, ballot: Ballot, prefix: Seq<u8>) -> bool {
    vote.ballot == ballot && vote.digest@ == prefix && vote.read_back
}

// read_back is the authenticated Replica attestation that both physical reads
// passed read_back_matches. L10 checks the comparison at the media boundary.
pub open spec fn mirrors_fence(row: VoterSlots, ballot: Ballot, prefix: Seq<u8>,
    replies: Seq<Vote>) -> bool
{
    well_formed(row.slots) && exists|i: int| 0 <= i < replies.len()
        && #[trigger] replies[i].voter == row.voter
        && replies[i].slots == row.slots
        && at_fence(replies[i], ballot, prefix)
}

pub open spec fn exact_rows(rows: Seq<VoterSlots>, roster: Set<Uuid>, ballot: Ballot,
    prefix: Seq<u8>, replies: Seq<Vote>) -> bool
{
    forall|i: int| 0 <= i < rows.len() ==> roster.contains(#[trigger] rows[i].voter)
        && mirrors_fence(rows[i], ballot, prefix, replies)
}

}

verus! {

fn recording_a_rotation_vote_preserves_exact_configured_rows(
    voters: &mut Vec<VoterSlots>, expected: Uuid, ballot: Ballot, prefix: Fingerprint,
    reply: Vote, roster: Ghost<Set<Uuid>>, replies: Ghost<Seq<Vote>>, reply_index: Ghost<int>,
) -> (out: bool)
    requires roster@.contains(expected),
        0 <= reply_index@ < replies@.len(), replies@[reply_index@] == reply,
        exact_rows(old(voters)@, roster@, ballot, prefix@, replies@),
    ensures exact_rows(final(voters)@, roster@, ballot, prefix@, replies@),
        out ==> final(voters)@.last().slots == reply.slots,
{
    let ghost previous = voters@;
    let recorded = record_vote(voters, expected, ballot, prefix, true, reply);
    proof {
        if recorded {
            let rows = voters@;
            let last = rows.len() as int - 1;
            assert forall|i: int| 0 <= i < rows.len() implies
                roster@.contains(#[trigger] rows[i].voter)
                && mirrors_fence(rows[i], ballot, prefix@, replies@) by {
                if i == last {
                    assert(at_fence(reply, ballot, prefix@));
                    assert(replies@[reply_index@].voter == rows[i].voter);
                    assert(mirrors_fence(rows[i], ballot, prefix@, replies@));
                } else {
                    assert(rows[i] == previous[i]);
                    assert(i < previous.len());
                    assert(roster@.contains(previous[i].voter) && mirrors_fence(previous[i], ballot, prefix@, replies@));
                }
            }
        }
    }
    recorded
}

}

#[verus_spec(out =>
    requires evidence.cohort_size == roster@.len(),
        exact_rows(evidence.voters@, roster@, evidence.ballot, evidence.prefix@, replies@),
    ensures out == covers_rotation(evidence, receipt),
      out ==> distinct_voters(evidence.voters@)
        && 2 * evidence.voters@.len() > roster@.len()
        && exact_rows(evidence.voters@, roster@, evidence.ballot, evidence.prefix@, replies@)
        && (receipt.outcome matches Ok(Outcome::Granted { grant, recovery })
            && evidence.checkpoint == recovery.checkpoint
            && recovery.start == evidence.checkpoint.cut && recovery.through == evidence.checkpoint.cut
            && evidence.key_generation == grant.key_generation && evidence.position >= receipt.position),
)]
fn rotation_evidence_names_a_majority_with_both_exact_reads(
    evidence: &RotationSlots, receipt: Receipt, roster: Ghost<Set<Uuid>>, replies: Ghost<Seq<Vote>>,
) -> bool {
    let covers = evidence.covers(receipt);
    if covers {
        let majority = strict_majority(evidence.cohort_size);
        proof! {
            assert(evidence.voters@.len() == majority);
            let rows = evidence.voters@;
            assert forall|i: int, j: int| #![trigger rows[i].voter, rows[j].voter]
                0 <= i < j < rows.len() implies rows[i].voter != rows[j].voter by {
                ordered_rows_are_distinct(rows, i, j);
            }
        }
    }
    covers
}

#[verus_spec(
    ensures final(output).contents@ == old(output).contents@ + rotation_header(evidence)
        + voters_wire(evidence.voters@),
)]
fn the_wire_preserves_the_fence_and_both_images_in_physical_order(
    evidence: &RotationSlots, output: &mut BytesMut,
) {
    evidence.encode(output);
}


#[verus_spec(out =>
    requires chosen.cohort_size == roster@.len(),
        exact_rows(chosen.images@, roster@, chosen.ballot, chosen.prefix@, replies@),
    ensures out matches Some(evidence) ==> agrees_with_rotation(chosen, request, &evidence)
        && distinct_voters(evidence.voters@)
        && 2 * evidence.voters@.len() > roster@.len()
        && exact_rows(evidence.voters@, roster@, evidence.ballot, evidence.prefix@, replies@),
)]
fn published_evidence_preserves_the_exact_rotation_and_roster(
    chosen: &Chosen, request: &Request, roster: Ghost<Set<Uuid>>, replies: Ghost<Seq<Vote>>,
) -> Option<RotationSlots> {
    let evidence = chosen.rotation_slots(request)?;
    proof! { assert(agrees_with_rotation(chosen, request, &evidence)); }
    let covers = rotation_evidence_names_a_majority_with_both_exact_reads(
        &evidence, chosen.receipt, roster, replies,
    );
    proof! { assert(covers); }
    Some(evidence)
}


#[verus_spec(out =>
    ensures out ==> configured.members@.contains(peer) && !old(seen).members@.contains(peer),
)]
fn only_new_configured_peers_can_enter_the_round(
    configured: &BTreeSet<Uuid>, seen: &mut BTreeSet<Uuid>, peer: Uuid,
) -> bool {
    register_peer(configured, seen, peer)
}
