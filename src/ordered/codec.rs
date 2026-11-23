use super::{
    BarrierClaim, Checkpoint, Command, Cut, Enrollment, Fingerprint, Grant, Hold, Placement,
    Principal, Refusal, Request, RequestId, WriterState,
};
use bytes::{BufMut, Bytes, BytesMut};
use uuid::Uuid;

const VERSION: u8 = 1;
const BARRIER_DOMAIN: &[u8; 8] = b"LKBRAR01";

impl Request {
    /// The exact bytes used by ordered replication and crash replay.
    pub fn encode(&self) -> Bytes {
        let mut output = BytesMut::new();
        output.put_u8(VERSION);
        placement(&mut output, self.placement);
        match self.principal {
            Principal::Administrator => output.put_u8(0),
            Principal::Worker(worker) => {
                output.put_u8(1);
                enrollment(&mut output, worker);
            }
        }
        request_id(&mut output, self.id);
        match &self.command {
            Command::Enroll { worker, expected } => {
                output.put_u8(0);
                uuid(&mut output, *worker);
                output.put_u8(u8::from(expected.is_some()));
                if let Some(expected) = expected {
                    enrollment(&mut output, *expected);
                }
            }
            Command::Withdraw { enrollment: worker } => {
                output.put_u8(1);
                enrollment(&mut output, *worker);
            }
            Command::Grant {
                expected,
                candidate,
            } => {
                output.put_u8(2);
                output.put_u64(expected.epoch);
                output.put_u8(u8::from(expected.grant.is_some()));
                if let Some(expected) = expected.grant {
                    grant(&mut output, expected);
                }
                enrollment(&mut output, *candidate);
            }
            Command::Append {
                grant: writer,
                expected_next,
                timestamp,
                payload,
            } => {
                output.put_u8(3);
                grant(&mut output, *writer);
                output.put_u64(*expected_next);
                output.put_i64(*timestamp);
                output.put_slice(payload);
            }
            Command::Barrier { grant: writer } => {
                output.put_u8(4);
                grant(&mut output, *writer);
            }
            Command::Publish {
                grant: writer,
                checkpoint: offered,
            } => {
                output.put_u8(5);
                grant(&mut output, *writer);
                checkpoint(&mut output, *offered);
            }
            Command::Protect {
                grant: writer,
                through,
            }
            | Command::Trim {
                grant: writer,
                through,
            } => {
                output.put_u8(if matches!(&self.command, Command::Protect { .. }) {
                    6
                } else {
                    8
                });
                grant(&mut output, *writer);
                cut(&mut output, *through);
            }
            Command::Release { hold } => {
                output.put_u8(7);
                request_id(&mut output, hold.id);
                enrollment(&mut output, hold.owner);
                output.put_u64(hold.admitted_at);
                checkpoint(&mut output, hold.checkpoint);
                cut(&mut output, hold.through);
            }
        }
        output.freeze()
    }

    /// Decodes a single frame. A transport authenticates the principal and
    /// placement before choosing the frame.
    pub fn decode(frame: Bytes) -> Result<Self, Refusal> {
        let mut input = Input(frame);
        if input.read_byte()? != VERSION {
            return Err(Refusal::Invalid);
        }
        let placement = input.placement()?;
        let principal = match input.read_byte()? {
            0 => Principal::Administrator,
            1 => Principal::Worker(input.enrollment()?),
            _ => return Err(Refusal::Invalid),
        };
        let id = input.request_id()?;
        let command = match input.read_byte()? {
            0 => Command::Enroll {
                worker: input.uuid()?,
                expected: input.optional(Input::enrollment)?,
            },
            1 => Command::Withdraw {
                enrollment: input.enrollment()?,
            },
            2 => Command::Grant {
                expected: WriterState {
                    epoch: input.u64()?,
                    grant: input.optional(Input::grant)?,
                },
                candidate: input.enrollment()?,
            },
            3 => Command::Append {
                grant: input.grant()?,
                expected_next: input.u64()?,
                timestamp: i64::from_be_bytes(input.take()?),
                payload: std::mem::take(&mut input.0),
            },
            4 => Command::Barrier {
                grant: input.grant()?,
            },
            5 => Command::Publish {
                grant: input.grant()?,
                checkpoint: input.checkpoint()?,
            },
            6 => Command::Protect {
                grant: input.grant()?,
                through: input.cut()?,
            },
            7 => Command::Release {
                hold: Hold {
                    id: input.request_id()?,
                    owner: input.enrollment()?,
                    admitted_at: input.u64()?,
                    checkpoint: input.checkpoint()?,
                    through: input.cut()?,
                },
            },
            8 => Command::Trim {
                grant: input.grant()?,
                through: input.cut()?,
            },
            _ => return Err(Refusal::Invalid),
        };
        if !input.0.is_empty() {
            return Err(Refusal::Invalid);
        }
        Ok(Self {
            placement,
            principal,
            id,
            command,
        })
    }
}

impl BarrierClaim {
    /// Canonical bytes for the journal's scoped receipt issuer to authenticate.
    pub fn encode(&self) -> Bytes {
        let mut output = BytesMut::new();
        output.put_slice(BARRIER_DOMAIN);
        placement(&mut output, self.placement);
        grant(&mut output, self.grant);
        request_id(&mut output, self.read.id);
        output.put_u64(self.read.admitted_at);
        checkpoint(&mut output, self.read.checkpoint);
        cut(&mut output, self.read.through);
        output.freeze()
    }

    /// Parses a claim. The receiver still authenticates the original bytes
    /// against the installed journal scope before relying on their contents.
    pub fn decode(frame: Bytes) -> Result<Self, Refusal> {
        let mut input = Input(frame);
        if &input.take::<8>()? != BARRIER_DOMAIN {
            return Err(Refusal::Invalid);
        }
        let placement = input.placement()?;
        let grant = input.grant()?;
        let id = input.request_id()?;
        let admitted_at = input.u64()?;
        let checkpoint = input.checkpoint()?;
        let through = input.cut()?;
        if !input.0.is_empty()
            || checkpoint.cut.next_lsn > through.next_lsn
            || (checkpoint.cut.next_lsn == through.next_lsn && checkpoint.cut != through)
            || admitted_at == 0
            || admitted_at >= id.expires_at
        {
            return Err(Refusal::Invalid);
        }
        Ok(Self {
            placement,
            grant,
            read: Hold {
                id,
                owner: grant.enrollment,
                admitted_at,
                checkpoint,
                through,
            },
        })
    }
}

struct Input(Bytes);

impl Input {
    fn take<const N: usize>(&mut self) -> Result<[u8; N], Refusal> {
        if self.0.len() < N {
            return Err(Refusal::Invalid);
        }
        self.0
            .split_to(N)
            .as_ref()
            .try_into()
            .map_err(|_| Refusal::Invalid)
    }

    fn read_byte(&mut self) -> Result<u8, Refusal> {
        Ok(self.take::<1>()?[0])
    }
    fn uuid(&mut self) -> Result<Uuid, Refusal> {
        Ok(Uuid::from_bytes(self.take()?))
    }
    fn u64(&mut self) -> Result<u64, Refusal> {
        Ok(u64::from_be_bytes(self.take()?))
    }

    fn request_id(&mut self) -> Result<RequestId, Refusal> {
        Ok(RequestId {
            nonce: self.uuid()?,
            expires_at: self.u64()?,
        })
    }

    fn placement(&mut self) -> Result<Placement, Refusal> {
        Ok(Placement {
            deployment: self.uuid()?,
            incarnation: self.uuid()?,
            group: self.uuid()?,
            generation: self.u64()?,
        })
    }

    fn enrollment(&mut self) -> Result<Enrollment, Refusal> {
        Ok(Enrollment {
            worker: self.uuid()?,
            serial: self.u64()?,
        })
    }

    fn grant(&mut self) -> Result<Grant, Refusal> {
        Ok(Grant {
            enrollment: self.enrollment()?,
            epoch: self.u64()?,
        })
    }

    fn cut(&mut self) -> Result<Cut, Refusal> {
        let next_lsn = self.u64()?;
        let history: Fingerprint = self.take()?;
        Ok(Cut { next_lsn, history })
    }

    fn checkpoint(&mut self) -> Result<Checkpoint, Refusal> {
        Ok(Checkpoint {
            cut: self.cut()?,
            root: self.take()?,
            manifest: self.take()?,
        })
    }

    fn optional<T>(
        &mut self,
        read: impl FnOnce(&mut Self) -> Result<T, Refusal>,
    ) -> Result<Option<T>, Refusal> {
        match self.read_byte()? {
            0 => Ok(None),
            1 => Ok(Some(read(self)?)),
            _ => Err(Refusal::Invalid),
        }
    }
}

fn uuid(output: &mut BytesMut, value: Uuid) {
    output.put_slice(value.as_bytes());
}

fn request_id(output: &mut BytesMut, value: RequestId) {
    uuid(output, value.nonce);
    output.put_u64(value.expires_at);
}

fn placement(output: &mut BytesMut, value: Placement) {
    uuid(output, value.deployment);
    uuid(output, value.incarnation);
    uuid(output, value.group);
    output.put_u64(value.generation);
}

fn enrollment(output: &mut BytesMut, value: Enrollment) {
    uuid(output, value.worker);
    output.put_u64(value.serial);
}

fn grant(output: &mut BytesMut, value: Grant) {
    enrollment(output, value.enrollment);
    output.put_u64(value.epoch);
}

fn cut(output: &mut BytesMut, value: Cut) {
    output.put_u64(value.next_lsn);
    output.put_slice(&value.history);
}

fn checkpoint(output: &mut BytesMut, value: Checkpoint) {
    cut(output, value.cut);
    output.put_slice(&value.root);
    output.put_slice(&value.manifest);
}
