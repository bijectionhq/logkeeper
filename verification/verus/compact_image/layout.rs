use crate::production::{
    ReducerImage, objectControlTrailerCanonical, oldRootKeyIncreases, receiptPositionsUnique,
    reducerInvariant,
};
use vstd::prelude::*;

verus! {

pub(super) ghost struct CompactImageAdmission {
    pub same_initial_configuration: bool,
    pub header_valid: bool,
    pub records_valid: bool,
    pub checkpoint_and_hold_cuts_valid: bool,
    pub receipts_valid: bool,
    pub derived_state_exact: bool,
}

pub(super) open spec fn compactImageAdmissible(
    image: ReducerImage, checks: CompactImageAdmission,
) -> bool {
    reducerInvariant(image)
        && checks.same_initial_configuration
        && checks.header_valid
        && checks.records_valid
        && checks.checkpoint_and_hold_cuts_valid
        && checks.receipts_valid
        && checks.derived_state_exact
}

pub(super) ghost struct ObjectControlTrailer {
    pub roots: usize,
    pub fences: usize,
    pub bytes: Seq<u8>,
}

pub(super) type OldRootBytes = (u64, Seq<u8>);

pub(super) ghost struct CompactImageLayout {
    pub header: Seq<u8>,
    pub old_roots: Seq<OldRootBytes>,
    pub body: Seq<u8>,
    pub trailer: Option<ObjectControlTrailer>,
    pub receipt_positions: Seq<u64>,
}

pub(super) open spec fn oldRootsInOrder(rows: Seq<OldRootBytes>) -> bool {
    forall|i: int, j: int| 0 <= i < j < rows.len()
        ==> oldRootKeyIncreases((#[trigger] rows[j]).0, Some((#[trigger] rows[i]).0))
}

pub(super) open spec fn compactImageBytesAdmissible(layout: CompactImageLayout) -> bool {
    oldRootsInOrder(layout.old_roots)
        && (match layout.trailer {
            None => objectControlTrailerCanonical(false, 0, 0),
            Some(trailer) => objectControlTrailerCanonical(true, trailer.roots, trailer.fences),
        })
        && receiptPositionsUnique(layout.receipt_positions)
}

pub(super) open spec fn compactImageLayoutBytes(layout: CompactImageLayout) -> Seq<u8> {
    layout.header + layout.old_roots.flat_map(|row: OldRootBytes| row.1) + layout.body
        + match layout.trailer { None => Seq::<u8>::empty(), Some(trailer) => trailer.bytes }
}

// old_roots is the map's ordered traversal of the same revision/row pairs.
pub(super) open spec fn canonicalCompactImageLayout(
    layout: CompactImageLayout, old_roots: Seq<OldRootBytes>,
) -> CompactImageLayout {
    CompactImageLayout {
        old_roots,
        trailer: match layout.trailer {
            Some(trailer) if trailer.roots == 0 && trailer.fences == 0 => None,
            trailer => trailer,
        },
        ..layout
    }
}

pub(super) proof fn strictly_ordered_old_roots_have_unique_iteration(
    a: Seq<OldRootBytes>, b: Seq<OldRootBytes>,
)
    requires oldRootsInOrder(a), oldRootsInOrder(b), a.to_set() == b.to_set(),
    ensures a == b,
    decreases a.len(),
{
    broadcast use Seq::to_set_ensures;
    if a.len() == 0 {
        if b.len() > 0 {
            assert(b.contains(b[0]));
            assert(b.to_set().contains(b[0]));
            assert(a.contains(b[0]));
        }
        assert(a =~= b);
    } else {
        assert(a.contains(a[0]));
        assert(a.to_set().contains(a[0]));
        assert(b.contains(a[0]));
        let j = choose|j: int| 0 <= j < b.len() && #[trigger] b[j] == a[0];
        assert(b.contains(b[0]));
        assert(b.to_set().contains(b[0]));
        assert(a.contains(b[0]));
        let i = choose|i: int| 0 <= i < a.len() && #[trigger] a[i] == b[0];
        assert(a[0].0 <= a[i].0);
        assert(b[0].0 <= b[j].0);
        assert(i == 0 && j == 0);
        assert(a[0] == b[0]);
        let a_tail = a.skip(1);
        let b_tail = b.skip(1);
        assert(oldRootsInOrder(a_tail));
        assert(oldRootsInOrder(b_tail));
        assert forall|row: OldRootBytes| #[trigger] a_tail.contains(row) implies b_tail.contains(row) by {
            let i = choose|i: int| 0 <= i < a_tail.len() && #[trigger] a_tail[i] == row;
            assert(a[i + 1] == row && a[0].0 < row.0 && a.contains(row));
            assert(a.to_set().contains(row));
            assert(b.contains(row));
            let j = choose|j: int| 0 <= j < b.len() && #[trigger] b[j] == row;
            assert(b_tail[j - 1] == row);
        }
        assert forall|row: OldRootBytes| #[trigger] b_tail.contains(row) implies a_tail.contains(row) by {
            let j = choose|j: int| 0 <= j < b_tail.len() && #[trigger] b_tail[j] == row;
            assert(b[j + 1] == row && b[0].0 < row.0 && b.contains(row));
            assert(b.to_set().contains(row));
            assert(a.contains(row));
            let i = choose|i: int| 0 <= i < a.len() && #[trigger] a[i] == row;
            assert(a_tail[i - 1] == row);
        }
        assert(a_tail.to_set() =~= b_tail.to_set());
        strictly_ordered_old_roots_have_unique_iteration(a_tail, b_tail);
        assert(a.len() == b.len());
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i] == #[trigger] b[i] by {
            if i > 0 {
                assert(a[i] == a_tail[i - 1] && b[i] == b_tail[i - 1]);
            }
        }
        assert(a =~= b);
    }
}

}
