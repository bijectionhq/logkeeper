use logkeeper::ordered::replication::Group;

pub struct Fixture {
    #[cfg(feature = "simulation")]
    capture: Option<(
        std::path::PathBuf,
        logkeeper::ordered::replication::trace::Trace,
    )>,
}

impl Fixture {
    pub fn new(name: &str) -> Self {
        #[cfg(not(feature = "simulation"))]
        let _ = name;
        Self {
            #[cfg(feature = "simulation")]
            capture: std::env::var_os("LOGKEEPER_PREFIX_TRACE_DIR").map(|directory| {
                let path = std::path::PathBuf::from(directory).join(name);
                (path, Default::default())
            }),
        }
    }

    pub fn observe(&self, group: Group) -> Group {
        #[cfg(feature = "simulation")]
        if let Some((_, trace)) = &self.capture {
            return trace.observe(group);
        }
        group
    }

    pub fn finish(self) {
        #[cfg(feature = "simulation")]
        if let Some((path, trace)) = self.capture {
            Self::write(&path.with_extension("trace"), &trace.steps());
        }
    }

    #[cfg(feature = "simulation")]
    #[allow(dead_code)]
    pub fn finish_with_forbidden_accept(self, restarted: uuid::Uuid) {
        if let Some((path, trace)) = &self.capture {
            let mut steps = trace.steps();
            let old = format!("accept 1 {} 1 ", restarted.as_u128());
            let forbidden = steps
                .iter()
                .find(|step| step.starts_with(&old))
                .unwrap()
                .clone();
            steps.push(forbidden);
            Self::write(&path.with_extension("reject"), &steps);
        }
        self.finish();
    }

    #[cfg(feature = "simulation")]
    fn write(path: &std::path::Path, steps: &[String]) {
        assert!(steps.iter().any(|event| event.starts_with("choice ")));
        std::fs::write(path, steps.join("\n") + "\n").unwrap();
    }
}

#[cfg(feature = "simulation")]
#[allow(dead_code)]
pub mod ordered {
    use super::Fixture;
    use logkeeper::ordered::replication::{DurableVoter, Group};
    use logkeeper::ordered::{
        Checkpoint, Command, Custody, Cut, Limits, Placement, Principal, Request, RequestId, Window,
    };
    use uuid::Uuid;

    pub struct Cohort {
        pub group: Group,
        pub ids: [Uuid; 3],
        pub media: [tempfile::TempDir; 3],
    }

    impl Cohort {
        pub fn new(trace: &Fixture) -> Self {
            let ids = std::array::from_fn(|_| Uuid::new_v4());
            let group = Group::new(
                Placement {
                    deployment: Uuid::new_v4(),
                    incarnation: Uuid::new_v4(),
                    group: Uuid::new_v4(),
                    generation: 1,
                },
                Limits {
                    enrolled_workers: 4,
                    replay_holds: 2,
                    retry_positions: 16,
                    retained_data_bytes: 8192,
                    maintenance_bytes: 1024,
                    serving_lease: 100,
                    clock_drift: 20,
                },
                Checkpoint {
                    cut: Cut {
                        next_lsn: 0,
                        history: [1; 32],
                    },
                    root: [0; 32],
                    manifest: [0; 32],
                    custody: Custody {
                        allocation: Uuid::new_v4(),
                        revision: 1,
                        provider: [0; 32],
                    },
                },
                Window {
                    allocation: Uuid::new_v4(),
                    serial: 1,
                    bytes: 4096,
                },
                ids,
                1 << 20,
            )
            .unwrap();
            Self {
                ids,
                group: trace.observe(group),
                media: std::array::from_fn(|_| tempfile::tempdir().unwrap()),
            }
        }

        pub fn provision(&self) -> [DurableVoter; 3] {
            std::array::from_fn(|i| {
                DurableVoter::initialize(self.group.clone(), self.ids[i], self.media[i].path())
                    .unwrap()
            })
        }

        pub fn enroll(&self) -> Request {
            Request {
                placement: self.group.placement(),
                principal: Principal::Administrator,
                id: RequestId {
                    nonce: Uuid::new_v4(),
                    expires_at: 16,
                },
                command: Command::Enroll {
                    worker: Uuid::new_v4(),
                    expected: None,
                },
            }
        }
    }
}
