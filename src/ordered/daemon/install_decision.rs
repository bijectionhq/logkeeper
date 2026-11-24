#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(not(verus_keep_ghost), derive(Clone, Copy, Debug, PartialEq, Eq))]
pub(super) enum InstallDecision {
    Persist,
    AlreadyInstalled,
    Refuse,
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        match existing {
            Some(same) => if same { out is AlreadyInstalled } else { out is Refuse },
            None => if expected_absent { out is Persist } else { out is Refuse },
        },
))]
pub(super) fn install_group(existing: Option<bool>, expected_absent: bool) -> InstallDecision {
    match existing {
        Some(true) => InstallDecision::AlreadyInstalled,
        Some(false) => InstallDecision::Refuse,
        None if expected_absent => InstallDecision::Persist,
        None => InstallDecision::Refuse,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (persisted && !retired),
))]
pub(super) fn may_serve(persisted: bool, retired: bool) -> bool {
    persisted && !retired
}
