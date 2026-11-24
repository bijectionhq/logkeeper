//! Read the original WAL and checkpoint payloads during an upgrade.
use super::{Decoder, Epoch, Identity, KeeperId, Lsn, Request, StreamId, StreamView, invalid};
use crate::stream::wire::EpochRun;
use bytes::Bytes;
use std::io;

impl Decoder {
    fn records(&mut self) -> io::Result<Vec<Bytes>> {
        (0..self.count(4)?).map(|_| self.bytes()).collect()
    }

    fn runs(&mut self) -> io::Result<Vec<EpochRun>> {
        (0..self.count(24)?)
            .map(|_| {
                Ok(EpochRun {
                    epoch: Epoch(self.u64()?),
                    first: Lsn(self.u64()?),
                    last: Lsn(self.u64()?),
                })
            })
            .collect()
    }

    fn ensemble(&mut self) -> io::Result<[KeeperId; 3]> {
        Ok([
            KeeperId(self.u128()?),
            KeeperId(self.u128()?),
            KeeperId(self.u128()?),
        ])
    }

    pub(super) fn legacy_view(&mut self, identity: Option<Identity>) -> io::Result<StreamView> {
        let promised = if self.boolean()? {
            let epoch = Epoch(self.u64()?);
            self.u128()?; // The old request holder was independent of the authenticated identity.
            Some((
                epoch,
                identity.ok_or_else(|| invalid("missing legacy seal identity"))?,
            ))
        } else {
            None
        };
        Ok(StreamView {
            promised,
            synced: self.boolean()?.then(|| self.u64().map(Epoch)).transpose()?,
            tail: Lsn(self.u64()?),
            head: Lsn(self.u64()?),
            floor: Lsn(self.u64()?),
            ensemble: self.ensemble()?,
            learner: self.boolean()?,
            runs: self.runs()?,
        })
    }

    pub(super) fn legacy_request(mut self) -> io::Result<Request> {
        let tag = self.u8()?;
        let stream = StreamId(self.u128()?);
        let epoch = if matches!(tag, 1..=4 | 9) {
            let epoch = Epoch(self.u64()?);
            self.u128()?; // Discard the old request holder.
            epoch
        } else {
            Epoch(0)
        };
        let request = match tag {
            0 => Request::Create {
                stream,
                ensemble: self.ensemble()?,
            },
            1 => Request::Seal {
                stream,
                epoch,
                ensemble: self.ensemble()?,
            },
            2 => Request::Sync {
                stream,
                epoch,
                floor: Lsn(self.u64()?),
                from: Lsn(self.u64()?),
                head: Lsn(self.u64()?),
                complete: self.boolean()?,
                runs: self.runs()?,
                records: self.records()?,
            },
            3 => Request::Append {
                stream,
                epoch,
                at: Lsn(self.u64()?),
                head: Lsn(self.u64()?),
                records: self.records()?,
            },
            4 => Request::Trim {
                stream,
                epoch,
                through: Lsn(self.u64()?),
            },
            7 => Request::Delete {
                stream,
                ensemble: self.ensemble()?,
            },
            9 => Request::Replace {
                stream,
                epoch,
                from: self.ensemble()?,
                to: self.ensemble()?,
            },
            _ => return Err(invalid("invalid legacy WAL request")),
        };
        self.finish()?;
        Ok(request)
    }
}
