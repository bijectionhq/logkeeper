//! Drive election and recovery transfers for the writer.

use journal_contract::{Epoch, JournalError, Lsn, Result, StreamId};

use crate::stream::proposer::{
    driver,
    recovery::{Election, SyncLane, floor_reply, floor_request, recover_request, single_record},
};

pub(super) use crate::stream::proposer::recovery::Recovery;

use super::{Io, KeeperId, Reply, Stream};
use crate::stream::timed::Entry;

pub(super) async fn choose(io: &Io, stream: &Stream, epoch: Epoch) -> Result<Recovery> {
    let election = Election::new(
        stream.id,
        stream.ensemble,
        epoch,
        io.transport.identity().clone(),
        io.proposal,
    );
    driver::run(&*io.transport, election, Some(driver::RPC_TIMEOUT)).await
}

pub(super) async fn sync(
    io: &Io,
    recovery: &Recovery,
    keeper: KeeperId,
    floor: Lsn,
) -> Result<Lsn> {
    driver::run(
        &*io.transport,
        SyncLane::new(recovery, keeper, floor)?,
        Some(driver::RPC_TIMEOUT),
    )
    .await
}

pub(super) async fn install_floor(
    io: &Io,
    keeper: KeeperId,
    stream: StreamId,
    epoch: Epoch,
    floor: Lsn,
) -> Result<Lsn> {
    floor_reply(
        io.call(keeper, floor_request(stream, epoch, floor)).await?,
        floor,
    )
}

pub(super) async fn fetch(
    io: &Io,
    keeper: KeeperId,
    stream: StreamId,
    epoch: Epoch,
    from: Lsn,
) -> Result<Entry> {
    single_record(
        io.call(keeper, recover_request(stream, epoch, from, 1))
            .await,
        from,
    )
}

pub(super) async fn fetch_run(
    io: &Io,
    keeper: KeeperId,
    stream: StreamId,
    epoch: Epoch,
    from: Lsn,
    max: u32,
) -> Result<Vec<Entry>> {
    match io
        .call(keeper, recover_request(stream, epoch, from, max))
        .await?
    {
        Reply::Records { records, .. }
            if !records.is_empty()
                && records.len() <= max as usize
                && records
                    .iter()
                    .enumerate()
                    .all(|(i, (lsn, _))| from.0.checked_add(i as u64) == Some(lsn.0)) =>
        {
            Ok(records
                .into_iter()
                .map(|(_, payload)| Entry::Ordinary(payload))
                .collect())
        }
        reply @ Reply::OriginalRecord { .. } if max != 0 => {
            Ok(vec![single_record(Ok(reply), from)?])
        }
        _ => Err(JournalError::Unavailable),
    }
}
