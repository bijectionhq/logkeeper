mod cluster;
mod workload;

use std::{env, fs, path::PathBuf, time::Duration};

use cluster::Result;

const CAP: usize = 4 * 1024 * 1024;
const NO_CAP: usize = 64 * 1024 * 1024;

#[tokio::main(worker_threads = 4)]
async fn main() -> Result<()> {
    let args: Vec<_> = env::args().collect();
    let [_, binary, case, rtt, rest @ ..] = args.as_slice() else {
        return Err("usage: stream-measure KEEPER CASE RTT_US [STREAMS] [BATCH] [BATCHES]".into());
    };
    let binary = PathBuf::from(binary).canonicalize()?;
    let rtt = Duration::from_micros(rtt.parse()?);
    let size = |default| -> Result<u64> { Ok(rest.first().map_or(Ok(default), |v| v.parse())?) };
    fs::create_dir_all("verification/.results/measure")?;
    match case.as_str() {
        "calibrate" => workload::calibrate(rtt).await?,
        "commit" => {
            let streams = size(1000)?;
            let batch = rest.get(1).map_or(Ok(1), |v| v.parse::<u64>())?;
            let batches = rest.get(2).map_or(
                Ok(1000_u64.div_ceil(streams.max(1) * batch.max(1)).max(2)),
                |v| v.parse(),
            )?;
            workload::commit(&binary, rtt, streams, batch, batches).await?;
        }
        "head" => workload::head(&binary, rtt, size(32)?).await?,
        "kill" => workload::kill(&binary, rtt, size(1000)?).await?,
        "partition" => workload::partition(&binary, rtt, size(3000)?).await?,
        "replace" => workload::replace(&binary, rtt, size(100_000)?).await?,
        "hot" => {
            workload::hot(&binary, rtt, size(32)?, CAP).await?;
            workload::hot(&binary, rtt, size(32)?, NO_CAP).await?;
        }
        "pool" | "pool-check" => workload::pool(&binary, rtt, case == "pool-check").await?,
        _ => return Err(format!("unknown benchmark case {case}").into()),
    }
    Ok(())
}
