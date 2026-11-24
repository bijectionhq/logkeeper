use std::time::Duration;

use journal_contract::{Lsn, Page, Result};

use super::{Io, Stream};
use crate::stream::proposer::{driver, read::Read};

pub(super) async fn read(
    io: &Io,
    stream: &Stream,
    from: Lsn,
    max: usize,
    wait: Duration,
) -> Result<Page> {
    let keepers = io.transport.read_order(stream.ensemble);
    let operation = Read::new(stream.id, from, max, wait, keepers);
    driver::run(&*io.transport, operation, Some(driver::RPC_TIMEOUT)).await
}
