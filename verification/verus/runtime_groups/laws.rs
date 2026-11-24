use crate::production::{install_group, may_serve, InstallDecision};
use vstd::prelude::*;

#[verus_spec(out =>
    ensures out is Refuse,
)]
fn conflicting_definition_is_refused(expected_absent: bool) -> InstallDecision {
    install_group(Some(false), expected_absent)
}

#[verus_spec(out =>
    ensures !out,
)]
fn unpersisted_group_is_never_served(retired: bool) -> bool {
    may_serve(false, retired)
}

#[verus_spec(out =>
    ensures out is AlreadyInstalled,
)]
fn identical_definition_is_idempotent(expected_absent: bool) -> InstallDecision {
    install_group(Some(true), expected_absent)
}
