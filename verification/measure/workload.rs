use std::{
    fs::File,
    future::Future,
    io::{BufWriter, Write},
    path::Path,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering::Relaxed},
    },
    time::{Duration, Instant},
};

use bytes::Bytes;
use futures::{StreamExt, TryStreamExt, future::try_join_all, stream};
use journal_contract::{BoxFuture, Epoch, Identity, Journal, JournalError, Lsn, StreamId};
use logkeeper::stream::{
    keeper::{Sweep, SweepError, sweep_idle},
    transport::{Credentials, TcpTransport},
    wire::{EpochRun, KeeperId, Reply, Request, Transport, TransportError},
    writer::Writer,
};
use serde_json::{Value, json};
use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::{TcpListener, TcpStream},
    task::JoinSet,
};
use tokio_util::sync::CancellationToken;

use crate::{
    CAP,
    cluster::{BenchError, Cluster, ENSEMBLE, LEARNER, Link, Result, Timer},
};

const PARALLEL: usize = 64;
const CURRENT: Epoch = Epoch(1);
const NEXT: Epoch = Epoch(2);
const RECORD_BYTES: usize = 256;
const RETRY_LIMIT: Duration = Duration::from_secs(60);

#[derive(Default)]
struct Count {
    started: AtomicU64,
    returned: AtomicU64,
    errors: AtomicU64,
    checks: AtomicU64,
    appends: AtomicU64,
    publishes: AtomicU64,
    unreachable: AtomicU64,
    timed_out: AtomicU64,
}

struct Measured {
    tcp: TcpTransport,
    count: Count,
}

impl Transport for Measured {
    fn identity(&self) -> &Identity {
        self.tcp.identity()
    }

    fn read_order(&self, ensemble: [KeeperId; 3]) -> [KeeperId; 3] {
        self.tcp.read_order(ensemble)
    }

    fn call(
        &self,
        keeper: KeeperId,
        request: Request,
    ) -> BoxFuture<'_, std::result::Result<Reply, TransportError>> {
        Box::pin(async move {
            self.count.started.fetch_add(1, Relaxed);
            match &request {
                Request::Check { .. } => {
                    self.count.checks.fetch_add(1, Relaxed);
                }
                Request::Append { records, .. } if records.is_empty() => {
                    self.count.publishes.fetch_add(1, Relaxed);
                }
                Request::Append { .. } => {
                    self.count.appends.fetch_add(1, Relaxed);
                }
                _ => {}
            }
            let reply = self.tcp.call(keeper, request).await;
            self.count.returned.fetch_add(1, Relaxed);
            if let Err(error) = &reply {
                self.count.errors.fetch_add(1, Relaxed);
                match error {
                    TransportError::Unreachable => self.count.unreachable.fetch_add(1, Relaxed),
                    TransportError::TimedOut => self.count.timed_out.fetch_add(1, Relaxed),
                    TransportError::Protocol(message) => {
                        eprintln!("transport protocol error: {message}");
                        0
                    }
                };
            }
            reply
        })
    }
}

impl Measured {
    fn connect(cluster: &Cluster, credentials: &Credentials) -> Result<Arc<Self>> {
        Ok(Arc::new(Self {
            tcp: cluster.transport(credentials)?,
            count: Count::default(),
        }))
    }

    fn writer(self: &Arc<Self>) -> Result<Writer> {
        Ok(Writer::new(self.clone(), ENSEMBLE)?)
    }

    fn counters(&self) -> [u64; 8] {
        let c = &self.count;
        [
            &c.started,
            &c.returned,
            &c.errors,
            &c.checks,
            &c.appends,
            &c.publishes,
            &c.unreachable,
            &c.timed_out,
        ]
        .map(|v| v.load(Relaxed))
    }

    fn rates(&self, before: [u64; 8], elapsed: Duration) -> Value {
        let [
            started,
            returned,
            errors,
            checks,
            appends,
            publishes,
            unreachable,
            timed_out,
        ] = self
            .counters()
            .into_iter()
            .zip(before)
            .map(|(after, before)| after - before)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let seconds = elapsed.as_secs_f64();
        json!({"started_per_sec": started as f64 / seconds, "returned_per_sec": returned as f64 / seconds,
               "transport_errors": errors, "unreachable": unreachable, "timed_out": timed_out, "check_per_sec": checks as f64 / seconds,
               "data_append_per_sec": appends as f64 / seconds, "publish_per_sec": publishes as f64 / seconds})
    }
}

fn settle() -> impl Future<Output = ()> {
    tokio::time::sleep(Duration::from_millis(50))
}

fn record() -> Bytes {
    Bytes::from_static(&[7; RECORD_BYTES])
}

fn ms(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

fn stats(mut samples: Vec<Duration>) -> Value {
    assert!(!samples.is_empty());
    samples.sort_unstable();
    let at = |permille: usize| ms(samples[(samples.len() * permille).div_ceil(1000) - 1]);
    json!({"n": samples.len(), "p50_ms": at(500), "p99_ms": at(990), "p999_ms": at(999), "max_ms": ms(*samples.last().unwrap())})
}

async fn retry<T, F>(mut call: impl FnMut() -> F) -> Result<T>
where
    F: Future<Output = journal_contract::Result<T>>,
{
    Ok(tokio::time::timeout(RETRY_LIMIT, async {
        loop {
            match call().await {
                Err(JournalError::Unavailable) => {
                    tokio::time::sleep(Duration::from_millis(2)).await;
                }
                result => return result,
            }
        }
    })
    .await??)
}

async fn init(writer: &Writer, id: u64) -> Result<()> {
    let stream = StreamId(id.into());
    retry(|| writer.create(stream)).await?;
    let head = retry(|| writer.seal(stream, CURRENT)).await?;
    assert_eq!(head, Lsn(0));
    Ok(())
}

async fn prepare(writer: &Writer, streams: u64) -> Result<()> {
    stream::iter(1..=streams)
        .map(|id| init(writer, id))
        .buffer_unordered(PARALLEL)
        .try_collect::<Vec<_>>()
        .await?;
    settle().await;
    Ok(())
}

async fn append(
    writer: &Writer,
    id: u64,
    epoch: Epoch,
    at: u64,
    payload: Bytes,
) -> Result<Duration> {
    let start = Instant::now();
    let lsn = retry(|| writer.append(StreamId(id.into()), epoch, Lsn(at), payload.clone())).await?;
    assert_eq!(lsn, Lsn(at));
    Ok(start.elapsed())
}

async fn batch(
    writer: &Writer,
    id: u64,
    first: u64,
    count: u64,
) -> Result<(Duration, Vec<Duration>)> {
    let start = Instant::now();
    // First polls submit contiguous positions in order. Each stream has one batch
    // in flight, with every record using the public Journal::append entry point.
    let records =
        try_join_all((first..first + count).map(|at| append(writer, id, CURRENT, at, record())))
            .await?;
    Ok((start.elapsed(), records))
}

pub async fn calibrate(rtt: Duration) -> Result<()> {
    let listener = TcpListener::bind("127.0.0.1:0").await?;
    let target = listener.local_addr()?;
    let link = Link::start(target, rtt, Timer::start()?).await?;
    let echo = tokio::spawn(async move {
        let (mut socket, _) = listener.accept().await?;
        socket.set_nodelay(true)?;
        let mut byte = [0];
        while socket.read(&mut byte).await? != 0 {
            socket.write_all(&byte).await?;
        }
        Ok::<_, std::io::Error>(())
    });
    let mut socket = TcpStream::connect(link.address).await?;
    socket.set_nodelay(true)?;
    let mut times = Vec::with_capacity(1000);
    for _ in 0..1000 {
        let start = Instant::now();
        socket.write_all(&[1]).await?;
        let mut response = [0];
        socket.read_exact(&mut response).await?;
        assert_eq!(response, [1]);
        times.push(start.elapsed());
    }
    drop(socket);
    echo.await??;
    println!(
        "{}",
        json!({"case":"calibrate", "rtt_us":rtt.as_micros(), "echo":stats(times)})
    );
    Ok(())
}

pub async fn commit(
    binary: &Path,
    rtt: Duration,
    streams: u64,
    width: u64,
    batches: u64,
    in_flight: usize,
) -> Result<Value> {
    assert!(streams > 0 && width > 0 && batches > 0 && in_flight > 0);
    let in_flight = in_flight.min(streams as usize);
    let cluster = Cluster::start(binary, [rtt; 3], CAP).await?;
    let io = Measured::connect(&cluster, &cluster.writer)?;
    let writer = io.writer()?;
    prepare(&writer, streams).await?;
    let before = io.counters();
    let connections: Vec<_> = cluster.links.iter().map(Link::connections).collect();
    let mut tasks = JoinSet::new();
    let gate = Arc::new(tokio::sync::Barrier::new(streams as usize + 1));
    let admission = Arc::new(tokio::sync::Semaphore::new(in_flight));
    for id in 1..=streams {
        let writer = writer.clone();
        let gate = gate.clone();
        let admission = admission.clone();
        tasks.spawn(async move {
            gate.wait().await;
            let mut queue_times = Vec::new();
            let mut batch_times = Vec::new();
            let mut append_times = Vec::new();
            for index in 0..batches {
                let queued = Instant::now();
                let _permit = admission.acquire().await.unwrap();
                queue_times.push(queued.elapsed());
                let (elapsed, records) = batch(&writer, id, index * width + 1, width).await?;
                batch_times.push(elapsed);
                append_times.extend(records);
            }
            Ok::<_, BenchError>((queue_times, batch_times, append_times))
        });
    }
    let start = Instant::now();
    gate.wait().await;
    let mut queue_times = Vec::new();
    let mut batch_times = Vec::new();
    let mut append_times = Vec::new();
    while let Some(task) = tasks.join_next().await {
        let (queue, batch, append) = task??;
        queue_times.extend(queue);
        batch_times.extend(batch);
        append_times.extend(append);
    }
    let elapsed = start.elapsed();
    let result = json!({"case":"commit", "rtt_us":rtt.as_micros(), "streams":streams, "batch":width,
        "in_flight_streams":in_flight, "batches_per_stream":batches, "seconds":elapsed.as_secs_f64(),
        "records_per_sec":append_times.len() as f64 / elapsed.as_secs_f64(), "record":stats(append_times),
        "producer_queue":stats(queue_times), "batch_ack":stats(batch_times), "rpc":io.rates(before, elapsed), "new_connections":
        cluster.links.iter().zip(connections).map(|(link, before)| link.connections()-before).collect::<Vec<_>>() });
    println!("{result}");
    Ok(result)
}

/// Regression guard for node-level batching. Fails unless one stream's batch-32 records
/// cost well under a quarter of batch-1 records, 10,000 streams at batch 32 run with no
/// transport errors or reconnections, and observers never see `Unavailable` under load.
pub async fn scale_check(binary: &Path, rtt: Duration) -> Result<()> {
    let single = commit(binary, rtt, 1, 1, 256, 1).await?;
    let batched = commit(binary, rtt, 1, 32, 8, 1).await?;
    let ratio =
        batched["records_per_sec"].as_f64().unwrap() / single["records_per_sec"].as_f64().unwrap();
    if ratio < 4.0 {
        return Err(format!("batch 32 is only {ratio:.1} times batch 1 throughput").into());
    }
    let wide = commit(binary, rtt, 10_000, 32, 1, 256).await?;
    let errors = wide["rpc"]["transport_errors"].as_u64().unwrap();
    let reconnects: u64 = wide["new_connections"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(Value::as_u64)
        .sum();
    if errors != 0 || reconnects != 0 {
        return Err(format!(
            "10,000 streams at batch 32: {errors} transport errors, {reconnects} new connections"
        )
        .into());
    }
    for row in head(binary, rtt, 32).await? {
        if row["unavailable"].as_u64() != Some(0) {
            return Err(format!("head returned Unavailable: {row}").into());
        }
    }
    Ok(())
}

fn background(
    writer: Writer,
    ids: impl IntoIterator<Item = u64>,
    payload: Bytes,
    first: u64,
    stop: &CancellationToken,
    period: Duration,
) -> JoinSet<Result<(u64, Lsn)>> {
    let mut tasks = JoinSet::new();
    for id in ids {
        let writer = writer.clone();
        let payload = payload.clone();
        let stop = stop.clone();
        tasks.spawn(async move {
            let mut head = first - 1;
            while !stop.is_cancelled() {
                let start = Instant::now();
                append(&writer, id, CURRENT, head + 1, payload.clone()).await?;
                head += 1;
                let slept = period.saturating_sub(start.elapsed());
                if !slept.is_zero() {
                    tokio::select! { _ = stop.cancelled() => {}, _ = tokio::time::sleep(slept) => {} }
                }
            }
            Ok((id, Lsn(head)))
        });
    }
    tasks
}

async fn collect_background(mut tasks: JoinSet<Result<(u64, Lsn)>>) -> Result<Vec<(u64, Lsn)>> {
    let mut heads = Vec::new();
    while let Some(task) = tasks.join_next().await {
        heads.push(task??);
    }
    Ok(heads)
}

pub async fn head(binary: &Path, rtt: Duration, streams: u64) -> Result<Vec<Value>> {
    assert!(streams > 0);
    let mut rows = Vec::new();
    for loaded in [false, true] {
        let cluster = Cluster::start(binary, [rtt; 3], CAP).await?;
        let writer_io = Measured::connect(&cluster, &cluster.writer)?;
        let reader_io = Measured::connect(&cluster, &cluster.observer)?;
        let writer = writer_io.writer()?;
        let reader = reader_io.writer()?;
        prepare(&writer, streams).await?;
        let stop = CancellationToken::new();
        let appends = if loaded {
            background(
                writer.clone(),
                1..=streams,
                record(),
                1,
                &stop,
                Duration::ZERO,
            )
        } else {
            JoinSet::new()
        };
        settle().await;
        for (handle, io, observer) in [(&writer, &writer_io, false), (&reader, &reader_io, true)] {
            let before = io.counters();
            let write_before = writer_io.counters();
            let start = Instant::now();
            let (times, errors) = stream::iter(1..=streams)
                .map(|id| async move {
                    let mut times = Vec::new();
                    let mut errors = 0u64;
                    for _ in 0..1000u64.div_ceil(streams).max(32) {
                        let start = Instant::now();
                        match handle.head(StreamId(id.into())).await {
                            Ok(_) => times.push(start.elapsed()),
                            Err(JournalError::Unavailable) => errors += 1,
                            Err(error) => return Err(error),
                        }
                    }
                    Ok((times, errors))
                })
                .buffer_unordered(PARALLEL)
                .try_fold(
                    (Vec::new(), 0),
                    |(mut times, errors), (part, failed)| async move {
                        times.extend(part);
                        Ok((times, errors + failed))
                    },
                )
                .await?;
            let elapsed = start.elapsed();
            let latency = if times.is_empty() {
                Value::Null
            } else {
                stats(times)
            };
            let row = json!({"case":"head", "rtt_us":rtt.as_micros(), "streams":streams,
                "loaded":loaded, "observer":observer, "head":latency, "unavailable":errors,
                "seconds":elapsed.as_secs_f64(), "rpc":io.rates(before, elapsed),
                "writer_rpc":writer_io.rates(write_before, elapsed)});
            println!("{row}");
            rows.push(row);
        }
        stop.cancel();
        collect_background(appends).await?;
    }
    Ok(rows)
}

async fn seed(writer: &Writer, ids: impl IntoIterator<Item = u64>) -> Result<Vec<(u64, Instant)>> {
    stream::iter(ids)
        .map(|id| async move {
            append(writer, id, CURRENT, 1, record()).await?;
            Ok((id, Instant::now()))
        })
        .buffer_unordered(PARALLEL)
        .try_collect()
        .await
}

fn fault_results(
    case: &str,
    rtt: Duration,
    start: Instant,
    samples: Vec<(u64, Duration, Duration)>,
) -> Result<()> {
    let last = samples
        .iter()
        .map(|(_, recovered, _)| *recovered)
        .max()
        .ok_or("no affected streams")?;
    let path = format!(
        "verification/.results/measure/{case}-{}-{}-{}.csv",
        rtt.as_micros(),
        samples.len(),
        std::process::id()
    );
    let mut out = BufWriter::new(File::create(&path)?);
    writeln!(out, "stream,after_fault_ms,ack_gap_ms")?;
    for (id, recovery, stall) in &samples {
        writeln!(out, "{id},{:.6},{:.6}", ms(*recovery), ms(*stall))?;
    }
    out.flush()?;
    println!(
        "{}",
        json!({"case":case, "rtt_us":rtt.as_micros(), "streams":samples.len(), "last_ms":ms(last),
        "elapsed_ms":ms(start.elapsed()), "after_fault":stats(samples.iter().map(|x| x.1).collect()),
        "ack_gap":stats(samples.into_iter().map(|x| x.2).collect()),"per_stream_csv":path})
    );
    Ok(())
}

pub async fn kill(binary: &Path, rtt: Duration, streams: u64) -> Result<()> {
    let mut cluster = Cluster::start(binary, [rtt; 3], CAP).await?;
    let writer = Measured::connect(&cluster, &cluster.writer)?.writer()?;
    prepare(&writer, streams).await?;
    let warm = seed(&writer, 1..=streams).await?;
    let start = Instant::now();
    cluster.keepers[0].kill()?;
    let affected = stream::iter(warm)
        .map(|(id, before)| {
            let writer = &writer;
            async move {
                append(writer, id, CURRENT, 2, record()).await?;
                let now = Instant::now();
                Ok::<_, BenchError>((id, now - start, now - before))
            }
        })
        .buffer_unordered(streams as usize)
        .try_collect()
        .await?;
    fault_results("kill", rtt, start, affected)
}

pub async fn partition(binary: &Path, rtt: Duration, streams: u64) -> Result<()> {
    assert!(streams >= 3);
    let cluster = Cluster::start(binary, [rtt; 3], CAP).await?;
    let prior = Measured::connect(&cluster, &cluster.writer)?.writer()?;
    let successor = Measured::connect(&cluster, &cluster.successor)?.writer()?;
    let affected = (1..=streams).filter(|id| id % 3 == 0);
    let others = (1..=streams).filter(|id| id % 3 != 0);
    stream::iter(1..=streams)
        .map(|id| init(if id % 3 == 0 { &prior } else { &successor }, id))
        .buffer_unordered(PARALLEL)
        .try_collect::<Vec<_>>()
        .await?;
    seed(&successor, others.clone()).await?;
    let warm = seed(&prior, affected).await?;
    let start = Instant::now();
    cluster.links[0].partition();
    let (claimed, _) = tokio::try_join!(
        stream::iter(warm)
            .map(|(id, before)| {
                let successor = &successor;
                async move {
                    let stream = StreamId(id.into());
                    let head = retry(|| successor.seal(stream, NEXT)).await?;
                    assert_eq!(head, Lsn(1));
                    // Apply the adopted record before issuing the first write as successor.
                    let page = retry(|| successor.read(stream, Lsn(1), 1, Duration::ZERO)).await?;
                    assert_eq!(page.records, vec![(Lsn(1), record())]);
                    append(successor, id, NEXT, 2, record()).await?;
                    let now = Instant::now();
                    Ok::<_, BenchError>((id, now - start, now - before))
                }
            })
            .buffer_unordered(streams as usize)
            .try_collect(),
        stream::iter(others)
            .map(|id| append(&successor, id, CURRENT, 2, record()))
            .buffer_unordered(PARALLEL)
            .try_collect::<Vec<_>>(),
    )?;
    fault_results("partition", rtt, start, claimed)
}

async fn park(io: &Measured, id: u64) -> Result<()> {
    let stream = StreamId(id.into());
    // Seed exactly two durable copies, including one on the keeper we will lose.
    // Alternate survivors so both positions in the sweep see missing metadata.
    let survivor = ENSEMBLE[1 + id as usize % 2];
    try_join_all(
        [ENSEMBLE[0], survivor]
            .into_iter()
            .map(|keeper| async move {
                let requests = [
                    Request::Create {
                        stream,
                        ensemble: ENSEMBLE,
                    },
                    Request::Seal {
                        stream,
                        ensemble: ENSEMBLE,
                        epoch: CURRENT,
                        proposal: None,
                    },
                    Request::Sync {
                        stream,
                        epoch: CURRENT,
                        floor: Lsn(1),
                        from: Lsn(1),
                        records: vec![record()],
                        runs: vec![EpochRun {
                            epoch: CURRENT,
                            first: Lsn(1),
                            last: Lsn(1),
                        }],
                        head: Lsn(1),
                        complete: true,
                    },
                ];
                for (step, request) in requests.into_iter().enumerate() {
                    retry(|| async {
                        let reply = io.call(keeper, request.clone()).await;
                        match (step, reply) {
                            (0, Ok(Reply::Created))
                            | (1, Ok(Reply::Sealed(_)))
                            | (2, Ok(Reply::Synced { tail: Lsn(1) })) => Ok(()),
                            _ => Err(JournalError::Unavailable),
                        }
                    })
                    .await?;
                }
                Ok::<_, BenchError>(())
            }),
    )
    .await?;
    Ok(())
}

pub async fn replace(binary: &Path, rtt: Duration, streams: u64) -> Result<()> {
    assert!(streams >= 100 && streams % 100 == 0);
    let mut cluster = Cluster::start(binary, [rtt; 3], CAP).await?;
    let io = Measured::connect(&cluster, &cluster.writer)?;
    let writer = io.writer()?;
    eprintln!("Preparing {streams} replacement streams");
    // The active cohort keeps its writer after the fault. Start that cohort with
    // metadata on both survivors, so it can keep writing as idle streams move.
    let count = streams / 100;
    stream::iter(1..=count)
        .map(|id| {
            let io = &io;
            async move {
                for keeper in ENSEMBLE {
                    retry(|| async {
                        match io
                            .call(
                                keeper,
                                Request::Create {
                                    stream: StreamId(id.into()),
                                    ensemble: ENSEMBLE,
                                },
                            )
                            .await
                        {
                            Ok(Reply::Created) => Ok(()),
                            _ => Err(JournalError::Unavailable),
                        }
                    })
                    .await?;
                }
                Ok::<_, BenchError>(())
            }
        })
        .buffer_unordered(PARALLEL)
        .try_collect::<Vec<_>>()
        .await?;
    prepare(&writer, count).await?;
    seed(&writer, 1..=count).await?;
    stream::iter(count + 1..=streams)
        .map(|id| park(&io, id))
        .buffer_unordered(PARALLEL)
        .try_collect::<Vec<_>>()
        .await?;
    cluster.keepers[0].kill()?;
    cluster.add(binary, LEARNER, rtt, CAP).await?;
    eprintln!("Installing a learner for {streams} streams");
    let transport = Measured::connect(&cluster, &cluster.successor)?;
    let plan = |id: u64| Sweep {
        stream: StreamId(id.into()),
        ensemble: ENSEMBLE,
        survivors: [ENSEMBLE[1], ENSEMBLE[2]],
        learner: LEARNER,
        epoch: NEXT,
    };
    let start = Instant::now();
    let sweep = |id| {
        let transport = &transport;
        async move {
            let started = Instant::now();
            loop {
                match sweep_idle(transport.as_ref(), [plan(id)])
                    .await
                    .pop()
                    .unwrap()
                    .1
                {
                    Err(SweepError::Transport { .. }) if started.elapsed() < RETRY_LIMIT => {
                        tokio::time::sleep(Duration::from_millis(2)).await;
                    }
                    result => {
                        result.map_err(|error| format!("stream {id}: {error}"))?;
                        return Ok::<_, BenchError>(start.elapsed());
                    }
                }
            }
        }
    };
    // Park 99%. The rest stay active until their writer drains for replacement.
    let stop = CancellationToken::new();
    let appends = background(
        writer,
        1..=count,
        record(),
        2,
        &stop,
        Duration::from_secs(1),
    );
    let mut completion = stream::iter(count + 1..=streams)
        .map(sweep)
        .buffer_unordered(PARALLEL)
        .try_collect::<Vec<_>>()
        .await?;
    stop.cancel();
    let heads: std::collections::HashMap<_, _> =
        collect_background(appends).await?.into_iter().collect();
    completion.extend(
        stream::iter(1..=count)
            .map(sweep)
            .buffer_unordered(PARALLEL)
            .try_collect::<Vec<_>>()
            .await?,
    );
    let elapsed = start.elapsed();
    eprintln!("Verifying {streams} learner copies");
    // Check the learner has the copied data and is a voting member on every stream.
    // This observation is outside the measured installation interval.
    stream::iter(1..=streams).map(|id| {
        let transport = &transport;
        let expected = heads.get(&id).copied().unwrap_or(Lsn(1));
        async move {
            let stream = StreamId(id.into());
            let reply = transport.call(LEARNER, Request::Check { stream, epoch:NEXT }).await;
            assert!(matches!(reply, Ok(Reply::Checked(view)) if !view.learner && view.head == expected
                && view.ensemble == [LEARNER, ENSEMBLE[1], ENSEMBLE[2]]), "unrestored learner on {stream:?}");
            let data = transport.call(LEARNER, Request::Read {
                stream, from: expected, max: 1, wait_ms: 0,
            }).await;
            assert!(matches!(data, Ok(Reply::Records { records, .. }) if records == [(expected, record())]),
                "unreadable learner copy on {stream:?}");
            Ok::<_, BenchError>(())
        }
    }).buffer_unordered(PARALLEL).try_collect::<Vec<_>>().await?;
    println!(
        "{}",
        json!({"case":"replace", "rtt_us":rtt.as_micros(), "streams":streams, "active":count,
        "active_appends":heads.values().map(|head| head.0 - 1).sum::<u64>(),
        "seconds":elapsed.as_secs_f64(), "streams_per_sec":streams as f64 / elapsed.as_secs_f64(),
        "completion":stats(completion)})
    );
    Ok(())
}

pub async fn hot(binary: &Path, rtt: Duration, neighbours: u64, cap: usize) -> Result<()> {
    assert!(neighbours > 0);
    let cluster = Cluster::start(binary, [rtt; 3], cap).await?;
    let writer = Measured::connect(&cluster, &cluster.writer)?.writer()?;
    prepare(&writer, neighbours + 1).await?;
    let hot_bytes = 8 * 1024 * 1024;
    let payload = Bytes::from(vec![9; hot_bytes]);
    let stop = CancellationToken::new();
    let period = Duration::from_secs_f64(hot_bytes as f64 / 200_000_000.0);
    let start = Instant::now();
    let task = background(writer.clone(), [1], payload, 1, &stop, period);
    let samples = stream::iter(2..=neighbours + 1)
        .map(|id| {
            let writer = &writer;
            async move {
                let mut out = Vec::new();
                let deadline = start + Duration::from_secs(4);
                let mut at = 1;
                while Instant::now() < deadline {
                    out.push(append(writer, id, CURRENT, at, record()).await?);
                    at += 1;
                }
                Ok::<_, BenchError>(out)
            }
        })
        .buffer_unordered(neighbours as usize)
        .try_collect::<Vec<_>>()
        .await;
    stop.cancel();
    let [(_, Lsn(records))] = collect_background(task).await?[..] else {
        unreachable!()
    };
    let elapsed = start.elapsed();
    println!(
        "{}",
        json!({"case":"hot", "rtt_us":rtt.as_micros(), "neighbours":neighbours, "cap_bytes":cap,
        "hot_records":records, "hot_bytes_per_sec":(records * hot_bytes as u64) as f64 / elapsed.as_secs_f64(),
        "neighbour":stats(samples?.into_iter().flatten().collect())})
    );
    Ok(())
}

pub async fn pool(binary: &Path, rtt: Duration, check: bool) -> Result<()> {
    let cluster = Cluster::start(binary, [rtt; 3], CAP).await?;
    let transport = Measured::connect(&cluster, &cluster.writer)?;
    let keeper = ENSEMBLE[0];
    let wave = || {
        try_join_all((0..PARALLEL).map(|_| async {
            let start = Instant::now();
            let reply = transport
                .call(
                    keeper,
                    Request::Check {
                        stream: StreamId(0),
                        epoch: CURRENT,
                    },
                )
                .await;
            assert!(
                matches!(
                    reply,
                    Ok(Reply::Refused(logkeeper::stream::wire::Refusal::NotFound))
                ),
                "pool probe failed: {reply:?}"
            );
            Ok::<_, BenchError>(start.elapsed())
        }))
    };
    wave().await?;
    let before = cluster.links[0].connections();
    let start = Instant::now();
    let mut samples = Vec::new();
    for _ in 0..24 {
        samples.extend(wave().await?);
    }
    let new = cluster.links[0].connections() - before;
    println!(
        "{}",
        json!({"case":"pool", "rtt_us":rtt.as_micros(), "parallel":PARALLEL,
        "seconds":start.elapsed().as_secs_f64(),"new_connections":new, "check":stats(samples)})
    );
    if check && new != 0 {
        return Err(format!("warm 64-channel route reopened {new} connections").into());
    }
    Ok(())
}
