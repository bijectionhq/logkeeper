//! Execution traces for the Lean prefix-agreement checker.

use super::{Accepted, Ballot, Fingerprint, Group, Prefix, State, VoterSlots};
use bytes::{Bytes, BytesMut};
use parking_lot::Mutex;
use std::collections::HashMap;
use std::fmt::Write;
use std::sync::Arc;
use uuid::Uuid;

#[derive(Clone, Default)]
pub struct Trace(Arc<Mutex<Recording>>);

#[derive(Default)]
struct Recording {
    groups: HashMap<Fingerprint, usize>,
    bytes: HashMap<Bytes, usize>,
    histories: HashMap<(u64, Fingerprint), Vec<usize>>,
    steps: Vec<String>,
}

impl Trace {
    /// Attaches before provisioning the voters. Cloned groups share the same recorder.
    pub fn observe(&self, mut group: Group) -> Group {
        let mut data = self.0.lock();
        let id = data.groups.len() + 1;
        assert!(data.groups.insert(group.identity, id).is_none());
        let mut step = format!("roster {id}");
        for voter in &group.voters {
            write!(step, " {}", voter.as_u128()).unwrap();
        }
        data.steps.push(step);
        group.trace = Some(self.clone());
        group
    }

    pub fn steps(&self) -> Vec<String> {
        self.0.lock().steps.clone()
    }

    pub(super) fn decision(&self, parent: Fingerprint, state: &State, frame: &Bytes) {
        let mut data = self.0.lock();
        let position = state.position();
        let mut history = data.history(position - 1, parent).to_vec();
        history.push(data.bytes_id(frame.clone()));
        let recorded = data
            .histories
            .entry((position, state.command_history()))
            .or_insert_with(|| history.clone());
        assert_eq!(*recorded, history);
    }

    pub(super) fn promise(
        &self,
        group: Fingerprint,
        voter: Uuid,
        ballot: Ballot,
        report: Option<&Accepted>,
    ) {
        let mut data = self.0.lock();
        let group = data.groups[&group];
        let mut step = format!("promise {group} {} {}", voter.as_u128(), rank(ballot));
        data.report(&mut step, report);
        data.steps.push(step);
    }

    pub(super) fn prepared(
        &self,
        group: Fingerprint,
        ballot: Ballot,
        voters: &super::BTreeSet<Uuid>,
        winner: Option<&Accepted>,
    ) {
        let mut data = self.0.lock();
        let group = data.groups[&group];
        let mut step = format!("prepared {group} {}", rank(ballot));
        if let Some(winner) = winner {
            data.report(&mut step, Some(winner));
        } else {
            step.push_str(" 0 0 0");
        }
        for voter in voters {
            write!(step, " {}", voter.as_u128()).unwrap();
        }
        data.steps.push(step);
    }

    pub(super) fn issued(
        &self,
        group: Fingerprint,
        ballot: Ballot,
        prefix: &Prefix,
        state: &State,
    ) {
        let mut data = self.0.lock();
        let group = data.groups[&group];
        let image = data.image_id(prefix);
        let mut step = format!("issue {group} {} {image}", rank(ballot));
        data.project(&mut step, state);
        data.steps.push(step);
    }

    pub(super) fn accept(
        &self,
        group: Fingerprint,
        voter: Uuid,
        accepted: &Accepted,
        state: &State,
    ) {
        let mut data = self.0.lock();
        let group = data.groups[&group];
        let image = data.image_id(&accepted.prefix);
        let mut step = format!(
            "accept {group} {} {} {image}",
            voter.as_u128(),
            rank(accepted.ballot)
        );
        data.project(&mut step, state);
        data.steps.push(step);
    }

    pub(super) fn choice(
        &self,
        group: Fingerprint,
        ballot: Ballot,
        prefix: &Prefix,
        voters: &[VoterSlots],
    ) {
        let mut data = self.0.lock();
        let group = data.groups[&group];
        let image = data.image_id(prefix);
        let mut step = format!("choice {group} {} {image}", rank(ballot));
        for vote in voters {
            write!(step, " {}", vote.voter.as_u128()).unwrap();
        }
        data.steps.push(step);
    }

    pub(super) fn restart(
        &self,
        group: Fingerprint,
        voter: Uuid,
        floor: Option<Ballot>,
        report: Option<&Accepted>,
    ) {
        let mut data = self.0.lock();
        let group = data.groups[&group];
        let floor = floor.map_or_else(|| "0 0".to_owned(), rank);
        let mut step = format!("restart {group} {} {floor}", voter.as_u128());
        data.report(&mut step, report);
        data.steps.push(step);
    }

    pub(super) fn seal(&self, source: Fingerprint, target: Fingerprint, mut selected: State) {
        assert_eq!(selected.successor, Some(target));
        selected.voter_scope = target;
        selected.successor = None;
        let base = selected.encode_base();

        let mut data = self.0.lock();
        let source = data.groups[&source];
        let target = data.groups[&target];
        let base = data.bytes_id(base);
        let mut step = format!("seal {source} {target} {base}");
        data.project(&mut step, &selected);
        data.steps.push(step);
    }

    pub(super) fn install(
        &self,
        group: Fingerprint,
        voter: Uuid,
        accepted: &Accepted,
        state: &State,
    ) {
        let mut data = self.0.lock();
        let group = data.groups[&group];
        let base = data.bytes_id(accepted.prefix.base.clone().expect("installed base"));
        let image = data.image_id(&accepted.prefix);
        let mut step = format!(
            "install {group} {} {} {base} {image}",
            voter.as_u128(),
            rank(accepted.ballot)
        );
        data.project(&mut step, state);
        data.steps.push(step);
    }
}

impl Recording {
    // Intern exact encoded bytes, so physical equality does not depend on a hash.
    fn bytes_id(&mut self, bytes: Bytes) -> usize {
        let id = self.bytes.len() + 1;
        *self.bytes.entry(bytes).or_insert(id)
    }

    fn image_id(&mut self, prefix: &Prefix) -> usize {
        let mut bytes = BytesMut::new();
        prefix.encode_into(&mut bytes);
        self.bytes_id(bytes.freeze())
    }

    fn report(&mut self, step: &mut String, report: Option<&Accepted>) {
        if let Some(vote) = report {
            write!(
                step,
                " {} {}",
                rank(vote.ballot),
                self.image_id(&vote.prefix)
            )
            .unwrap();
        }
    }

    fn project(&self, step: &mut String, state: &State) {
        for decision in self.history(state.position(), state.command_history()) {
            write!(step, " {decision}").unwrap();
        }
    }

    // Replay supplies the full decision chain before compaction discards its frames.
    fn history(&self, position: u64, digest: Fingerprint) -> &[usize] {
        if position == 0 && digest == [0; 32] {
            return &[];
        }
        self.histories
            .get(&(position, digest))
            .expect("observed decision chain")
    }
}

fn rank(ballot: Ballot) -> String {
    format!("{} {}", ballot.round, ballot.nonce.as_u128())
}
