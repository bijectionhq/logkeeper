//! Continuous offload of committed records to object storage.
//!
//! Each stream's leader uploads the committed prefix of its log to an
//! S3-compatible store (or a directory) in immutable, LSN-ranged segment
//! objects, then records the new `offloaded_through` through Raft with
//! `Command::Offloaded`, so every voter knows it. Objects live under
//!
//! ```text
//! <prefix>/streams/<stream, 32 hex>/<lineage, 16 hex>/<first, 20 digits>-<last, 20 digits>.seg
//! <prefix>/streams/<stream, 32 hex>/<lineage, 16 hex>/lineage
//! ```
//!
//! A lineage is one history of the stream: an operator recovery or a
//! restore starts a new one, so a deposed configuration that keeps
//! uploading under its old lineage can never overwrite or extend the
//! recovered history. Within a lineage every record an object holds equals
//! the committed record at its LSN (uploaders read only applied entries),
//! so objects that overlap agree, and a key is written at most once
//! (`PutMode::Create`): a retry or a new leader that finds it present moves
//! on. The model is Neon's safekeepers, which upload WAL segments and
//! report a durable remote-consistent LSN.
//!
//! The invariant other components rely on, and the protocol model proves:
//! the uploaded prefix is a prefix of the committed log.

pub(super) mod format;
pub(super) mod transfer;

use std::{
    collections::{HashMap, VecDeque},
    io,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
    time::Duration,
};

use bytes::Bytes;
use journal_contract::{Lsn, StreamId};
use object_store::{
    ObjectStore, ObjectStoreExt, PutMode, PutOptions, PutPayload, aws::AmazonS3Builder,
    local::LocalFileSystem, path::Path,
};
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};

use super::invalid;
pub use format::{LineageRecord, Record, Segment};

fn default_batch_bytes() -> u64 {
    16 * 1024 * 1024
}

fn default_batch_interval_ms() -> u64 {
    10_000
}

fn default_max_lag_bytes() -> u64 {
    256 * 1024 * 1024
}

fn default_true() -> bool {
    true
}

fn default_cache_bytes() -> u64 {
    64 * 1024 * 1024
}

fn default_concurrency() -> usize {
    8
}

/// Where and how a keeper offloads committed records. Every keeper of a
/// cluster names the same store: any voter may lead and upload, and any
/// keeper may serve a read below its local floor.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct OffloadConfig {
    /// `s3://bucket/prefix` or `file:///absolute/directory`.
    pub url: String,
    /// An S3-compatible endpoint, such as `http://127.0.0.1:9000` for MinIO.
    #[serde(default)]
    pub endpoint: Option<String>,
    #[serde(default)]
    pub region: Option<String>,
    /// Credentials; without them the standard `AWS_*` variables apply.
    #[serde(default)]
    pub access_key_id: Option<String>,
    #[serde(default)]
    pub secret_access_key: Option<String>,
    /// Allows a plain HTTP endpoint (MinIO on loopback).
    #[serde(default)]
    pub allow_http: bool,
    /// An object is uploaded once this many committed bytes wait, and holds
    /// at most this many (or one record, when a record is larger).
    #[serde(default = "default_batch_bytes")]
    pub batch_bytes: u64,
    /// ... or once the oldest waiting record has waited this long.
    #[serde(default = "default_batch_interval_ms")]
    pub batch_interval_ms: u64,
    /// When this many committed bytes wait for upload (estimated from the
    /// stream's average retained record charge), the leader refuses new
    /// appends with `Unavailable` until offload catches up.
    #[serde(default = "default_max_lag_bytes")]
    pub max_lag_bytes: u64,
    /// Whether `max_lag_bytes` refuses appends (the default) or only alerts.
    #[serde(default = "default_true")]
    pub backpressure: bool,
    /// Local retention: once offloaded, records older than the newest
    /// `retain_local_bytes` bytes leave the keepers' disks and are read
    /// back from the store. Absent (the default), keepers keep every
    /// record until the writer trims it, and the store is a backup.
    #[serde(default)]
    pub retain_local_bytes: Option<u64>,
    /// Bytes of fetched segments each keeper caches for reads below its
    /// local floor.
    #[serde(default = "default_cache_bytes")]
    pub cache_bytes: u64,
    /// Uploads in flight per keeper across its streams.
    #[serde(default = "default_concurrency")]
    pub concurrency: usize,
}

impl OffloadConfig {
    pub fn batch_interval(&self) -> Duration {
        Duration::from_millis(self.batch_interval_ms)
    }

    /// The most bytes one object holds.
    pub fn object_bytes(&self) -> u64 {
        self.batch_bytes.max(1)
    }
}

/// One listed segment object.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjectRef {
    pub lineage: u64,
    pub first: Lsn,
    pub last: Lsn,
    pub path: Path,
    pub size: u64,
}

/// Which objects hold a contiguous run of a stream's records, and the run.
#[derive(Clone, Debug, Default)]
pub struct Plan {
    /// The first and last LSN of the run, or `None` when nothing is held.
    pub run: Option<(Lsn, Lsn)>,
    /// The objects that cover the run, each with the part of it they cover.
    pub parts: Vec<(ObjectRef, Lsn, Lsn)>,
}

impl Plan {
    pub fn end(&self) -> Option<Lsn> {
        self.run.map(|(_, end)| end)
    }
}

/// An offload store: an object store, its key prefix and a segment cache.
pub struct Store {
    inner: Arc<dyn ObjectStore>,
    prefix: Path,
    cache: Mutex<Cache>,
    listings: Mutex<HashMap<(StreamId, u64), Vec<ObjectRef>>>,
    pub metrics: OffloadMetrics,
}

/// Offload counters of one keeper.
#[derive(Default)]
pub struct OffloadMetrics {
    pub uploaded_bytes: AtomicU64,
    pub uploaded_objects: AtomicU64,
    /// Uploads that found their object already written.
    pub existing_objects: AtomicU64,
    pub upload_failures: AtomicU64,
    pub recorded: AtomicU64,
    pub record_failures: AtomicU64,
    pub fetched_bytes: AtomicU64,
    pub cache_hits: AtomicU64,
    pub remote_reads: AtomicU64,
    pub remote_read_failures: AtomicU64,
    pub corrupt_objects: AtomicU64,
    pub backpressured_appends: AtomicU64,
    pub locally_trimmed_records: AtomicU64,
    /// The largest committed bytes waiting for upload on a stream this
    /// keeper leads, and the age of the oldest such wait, in milliseconds.
    pub lag_bytes_max: AtomicU64,
    pub lag_age_ms_max: AtomicU64,
    pub upload_duration: super::metrics::DurationHistogram,
}

impl OffloadMetrics {
    /// Appends the offload metrics in Prometheus text format.
    pub fn render_prometheus(&self, out: &mut String) {
        use std::fmt::Write as _;
        let load = |counter: &AtomicU64| counter.load(Ordering::Relaxed);
        for (name, help, kind, value) in [
            (
                "uploaded_bytes_total",
                "Bytes of segment objects this keeper uploaded.",
                "counter",
                load(&self.uploaded_bytes),
            ),
            (
                "uploaded_objects_total",
                "Segment objects this keeper uploaded.",
                "counter",
                load(&self.uploaded_objects),
            ),
            (
                "existing_objects_total",
                "Uploads that found their object already written by an earlier leader or attempt.",
                "counter",
                load(&self.existing_objects),
            ),
            (
                "upload_failures_total",
                "Segment uploads that failed and will be retried.",
                "counter",
                load(&self.upload_failures),
            ),
            (
                "recorded_total",
                "offloaded_through advances committed through Raft.",
                "counter",
                load(&self.recorded),
            ),
            (
                "record_failures_total",
                "offloaded_through proposals that did not commit.",
                "counter",
                load(&self.record_failures),
            ),
            (
                "fetched_bytes_total",
                "Bytes of segment objects fetched for reads, exports and restores.",
                "counter",
                load(&self.fetched_bytes),
            ),
            (
                "cache_hits_total",
                "Remote reads served from the segment cache.",
                "counter",
                load(&self.cache_hits),
            ),
            (
                "remote_reads_total",
                "Read pages served from the object store below the local floor.",
                "counter",
                load(&self.remote_reads),
            ),
            (
                "remote_read_failures_total",
                "Reads below the local floor the object store could not serve.",
                "counter",
                load(&self.remote_read_failures),
            ),
            (
                "corrupt_objects_total",
                "Fetched objects refused for a checksum or key mismatch.",
                "counter",
                load(&self.corrupt_objects),
            ),
            (
                "backpressured_appends_total",
                "Appends refused because offload fell more than max_lag_bytes behind.",
                "counter",
                load(&self.backpressured_appends),
            ),
            (
                "locally_trimmed_records_total",
                "Offloaded records retention removed from this keeper's disk.",
                "counter",
                load(&self.locally_trimmed_records),
            ),
            (
                "lag_bytes",
                "Largest committed bytes waiting for upload on a stream this keeper leads.",
                "gauge",
                load(&self.lag_bytes_max),
            ),
            (
                "lag_seconds",
                "Age of the oldest committed record waiting for upload on a stream this keeper leads.",
                "gauge",
                load(&self.lag_age_ms_max) / 1000,
            ),
        ] {
            let _ = writeln!(out, "# HELP logkeeper_offload_{name} {help}");
            let _ = writeln!(out, "# TYPE logkeeper_offload_{name} {kind}");
            let _ = writeln!(out, "logkeeper_offload_{name} {value}");
        }
        self.upload_duration.write_prometheus_named(
            out,
            "logkeeper_offload_upload_duration_seconds",
            "Time to upload one segment object.",
        );
    }
}

#[derive(Default)]
struct Cache {
    capacity: u64,
    used: u64,
    order: VecDeque<String>,
    segments: HashMap<String, Arc<Segment>>,
}

impl Cache {
    fn get(&mut self, key: &str) -> Option<Arc<Segment>> {
        let segment = self.segments.get(key)?.clone();
        if let Some(position) = self.order.iter().position(|item| item == key) {
            let item = self.order.remove(position).unwrap();
            self.order.push_back(item);
        }
        Some(segment)
    }

    fn insert(&mut self, key: String, segment: Arc<Segment>) {
        let size = segment.size as u64;
        if size > self.capacity || self.segments.contains_key(&key) {
            return;
        }
        while self.used + size > self.capacity
            && let Some(oldest) = self.order.pop_front()
        {
            if let Some(evicted) = self.segments.remove(&oldest) {
                self.used -= evicted.size as u64;
            }
        }
        self.used += size;
        self.order.push_back(key.clone());
        self.segments.insert(key, segment);
    }
}

fn store_error(error: object_store::Error) -> io::Error {
    match error {
        object_store::Error::NotFound { .. } => io::Error::new(io::ErrorKind::NotFound, error),
        error => io::Error::other(error),
    }
}

impl std::fmt::Debug for Store {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Store({}, {})", self.inner, self.prefix)
    }
}

impl Store {
    /// Opens the store a configuration names.
    pub fn open(config: &OffloadConfig) -> io::Result<Self> {
        let (inner, prefix): (Arc<dyn ObjectStore>, String) = if let Some(rest) =
            config.url.strip_prefix("s3://")
        {
            let (bucket, prefix) = rest.split_once('/').unwrap_or((rest, ""));
            if bucket.is_empty() {
                return Err(invalid("an s3 offload URL names a bucket"));
            }
            let mut builder = AmazonS3Builder::from_env()
                .with_bucket_name(bucket)
                .with_allow_http(config.allow_http);
            if let Some(endpoint) = &config.endpoint {
                builder = builder.with_endpoint(endpoint);
            }
            builder = builder.with_region(config.region.as_deref().unwrap_or("us-east-1"));
            if let Some(key) = &config.access_key_id {
                builder = builder.with_access_key_id(key);
            }
            if let Some(secret) = &config.secret_access_key {
                builder = builder.with_secret_access_key(secret);
            }
            (
                Arc::new(builder.build().map_err(io::Error::other)?),
                prefix.to_owned(),
            )
        } else if let Some(directory) = config.url.strip_prefix("file://") {
            std::fs::create_dir_all(directory)?;
            (
                Arc::new(LocalFileSystem::new_with_prefix(directory).map_err(io::Error::other)?),
                String::new(),
            )
        } else {
            return Err(invalid(format!(
                "unsupported offload URL {:?}: use s3://bucket/prefix or file:///directory",
                config.url
            )));
        };
        Ok(Self::new(inner, &prefix, config.cache_bytes))
    }

    pub fn new(inner: Arc<dyn ObjectStore>, prefix: &str, cache_bytes: u64) -> Self {
        Self {
            inner,
            prefix: Path::from(prefix.trim_matches('/')),
            cache: Mutex::new(Cache {
                capacity: cache_bytes,
                ..Cache::default()
            }),
            listings: Mutex::default(),
            metrics: OffloadMetrics::default(),
        }
    }

    fn join(&self, parts: &[String]) -> Path {
        let mut path = self.prefix.clone();
        for part in parts {
            path = path.join(part.as_str());
        }
        path
    }

    fn stream_path(&self, stream: StreamId) -> Path {
        self.join(&["streams".into(), format!("{:032x}", stream.0)])
    }

    fn lineage_path(&self, stream: StreamId, lineage: u64) -> Path {
        self.stream_path(stream).join(format!("{lineage:016x}"))
    }

    pub fn segment_path(&self, stream: StreamId, lineage: u64, first: Lsn, last: Lsn) -> Path {
        self.lineage_path(stream, lineage)
            .join(format!("{:020}-{:020}.seg", first.0, last.0))
    }

    fn lineage_record_path(&self, stream: StreamId, lineage: u64) -> Path {
        self.lineage_path(stream, lineage).join("lineage")
    }

    /// Writes `bytes` at `path` unless an object is there already. Whether
    /// this call created it.
    pub async fn put_once(&self, path: &Path, bytes: Bytes) -> io::Result<bool> {
        let options = PutOptions {
            mode: PutMode::Create,
            ..PutOptions::default()
        };
        match self
            .inner
            .put_opts(path, PutPayload::from_bytes(bytes), options)
            .await
        {
            Ok(_) => Ok(true),
            Err(object_store::Error::AlreadyExists { .. }) => Ok(false),
            Err(error) => Err(store_error(error)),
        }
    }

    pub async fn get(&self, path: &Path) -> io::Result<Bytes> {
        self.inner
            .get(path)
            .await
            .map_err(store_error)?
            .bytes()
            .await
            .map_err(store_error)
    }

    /// Uploads one segment of `stream` under `lineage`. Whether this call
    /// created the object; `false` when an earlier upload of the same range
    /// in the same lineage, which holds the same records, already did.
    pub async fn upload(
        &self,
        stream: StreamId,
        lineage: u64,
        records: &[Record],
        epochs: Vec<(Lsn, journal_contract::Epoch)>,
    ) -> io::Result<(bool, usize)> {
        let bytes = format::encode_segment(stream, lineage, records, epochs)?;
        let size = bytes.len();
        let path = self.segment_path(
            stream,
            lineage,
            records[0].lsn,
            records[records.len() - 1].lsn,
        );
        let created = self.put_once(&path, bytes).await?;
        self.listings.lock().remove(&(stream, lineage));
        Ok((created, size))
    }

    /// Records where a lineage starts, once.
    pub async fn put_lineage(&self, record: &LineageRecord) -> io::Result<()> {
        let path = self.lineage_record_path(record.stream, record.lineage);
        self.put_once(&path, format::encode_lineage(record)?)
            .await
            .map(drop)
    }

    pub async fn lineage_record(
        &self,
        stream: StreamId,
        lineage: u64,
    ) -> io::Result<Option<LineageRecord>> {
        match self.get(&self.lineage_record_path(stream, lineage)).await {
            Ok(bytes) => format::decode_lineage(&bytes).map(Some),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(error),
        }
    }

    /// The lineages the store holds objects of for `stream`, ascending.
    pub async fn lineages(&self, stream: StreamId) -> io::Result<Vec<u64>> {
        let listed = self
            .inner
            .list_with_delimiter(Some(&self.stream_path(stream)))
            .await
            .map_err(store_error)?;
        let mut lineages = listed
            .common_prefixes
            .iter()
            .filter_map(|path| u64::from_str_radix(path.filename()?, 16).ok())
            .collect::<Vec<_>>();
        lineages.sort_unstable();
        Ok(lineages)
    }

    /// The segment objects of one lineage, by first LSN then longest first.
    pub async fn list(&self, stream: StreamId, lineage: u64) -> io::Result<Vec<ObjectRef>> {
        use futures::TryStreamExt;
        let prefix = self.lineage_path(stream, lineage);
        let metas = self
            .inner
            .list(Some(&prefix))
            .try_collect::<Vec<_>>()
            .await
            .map_err(store_error)?;
        let mut objects = metas
            .into_iter()
            .filter_map(|meta| {
                let name = meta.location.filename()?.strip_suffix(".seg")?;
                let (first, last) = name.split_once('-')?;
                let (first, last) = (first.parse().ok()?, last.parse().ok()?);
                (first >= 1 && last >= first).then(|| ObjectRef {
                    lineage,
                    first: Lsn(first),
                    last: Lsn(last),
                    path: meta.location,
                    size: meta.size,
                })
            })
            .collect::<Vec<_>>();
        objects.sort_by(|a, b| a.first.cmp(&b.first).then(b.last.cmp(&a.last)));
        self.listings
            .lock()
            .insert((stream, lineage), objects.clone());
        Ok(objects)
    }

    async fn listed(&self, stream: StreamId, lineage: u64) -> io::Result<Vec<ObjectRef>> {
        if let Some(objects) = self.listings.lock().get(&(stream, lineage)).cloned() {
            return Ok(objects);
        }
        self.list(stream, lineage).await
    }

    /// Fetches and verifies a segment, through the cache. A segment whose
    /// header does not match its key is refused as corrupt.
    pub async fn segment(&self, stream: StreamId, object: &ObjectRef) -> io::Result<Arc<Segment>> {
        let key = object.path.to_string();
        if let Some(segment) = self.cache.lock().get(&key) {
            super::metrics::count(&self.metrics.cache_hits);
            return Ok(segment);
        }
        let bytes = self.get(&object.path).await?;
        super::metrics::add(&self.metrics.fetched_bytes, bytes.len() as u64);
        let segment = format::decode_segment(&bytes).and_then(|segment| {
            let header = &segment.header;
            if header.stream != stream
                || header.lineage != object.lineage
                || header.first != object.first
                || header.last != object.last
            {
                return Err(invalid("offloaded segment differs from its key"));
            }
            Ok(segment)
        });
        let segment = Arc::new(segment.inspect_err(|_| {
            super::metrics::count(&self.metrics.corrupt_objects);
        })?);
        self.cache.lock().insert(key, segment.clone());
        Ok(segment)
    }

    /// Reads committed records of `stream` from `from` through `until`
    /// inclusive out of `lineage`'s segments, at most `limit` records and
    /// about `max_bytes` bytes (at least one record). A corrupt object is
    /// skipped when another one covers the same position.
    pub async fn read(
        &self,
        stream: StreamId,
        lineage: u64,
        from: Lsn,
        until: Lsn,
        limit: usize,
        max_bytes: usize,
    ) -> io::Result<Vec<Record>> {
        let mut out = Vec::new();
        let mut bytes = 0;
        let mut next = from;
        let mut refreshed = false;
        while next <= until && out.len() < limit {
            let objects = self.listed(stream, lineage).await?;
            let candidates = objects
                .iter()
                .filter(|object| object.first <= next && next <= object.last)
                .collect::<Vec<_>>();
            if candidates.is_empty() {
                if refreshed {
                    return if out.is_empty() {
                        Err(io::Error::new(
                            io::ErrorKind::NotFound,
                            format!("no offloaded object holds record {}", next.0),
                        ))
                    } else {
                        Ok(out)
                    };
                }
                refreshed = true;
                self.listings.lock().remove(&(stream, lineage));
                continue;
            }
            let mut error = None;
            let mut segment = None;
            for candidate in candidates {
                match self.segment(stream, candidate).await {
                    Ok(found) => {
                        segment = Some(found);
                        break;
                    }
                    Err(failure) => error = Some(failure),
                }
            }
            let Some(segment) = segment else {
                return Err(error.unwrap());
            };
            let skip = (next.0 - segment.header.first.0) as usize;
            for record in &segment.records[skip..] {
                if record.lsn > until
                    || out.len() >= limit
                    || (!out.is_empty() && bytes + record.bytes.len() > max_bytes)
                {
                    return Ok(out);
                }
                bytes += record.bytes.len();
                out.push(record.clone());
                next = Lsn(record.lsn.0 + 1);
            }
        }
        Ok(out)
    }

    /// The longest contiguous run of `stream`'s records the store holds
    /// under `lineages` (each lineage with the first LSN it is
    /// authoritative for, ascending), starting at or above `floor`. Each
    /// lineage covers only its own range; a deposed history's objects past
    /// the next lineage's start are never used.
    pub async fn plan(
        &self,
        stream: StreamId,
        lineages: &[(u64, Lsn)],
        floor: Lsn,
    ) -> io::Result<Plan> {
        let mut plan = Plan::default();
        for (index, &(lineage, start)) in lineages.iter().enumerate() {
            let end = lineages
                .get(index + 1)
                .map_or(Lsn(u64::MAX - 1), |(_, next)| Lsn(next.0.saturating_sub(1)));
            if end < start || end < floor {
                continue;
            }
            let objects = self.list(stream, lineage).await?;
            let low = Lsn(start.0.max(floor.0));
            // Continue the run when it reached this lineage's start.
            let mut next = match plan.run {
                Some((_, last)) if last.0 + 1 >= low.0 => Lsn(last.0 + 1),
                _ => {
                    plan = Plan::default();
                    low
                }
            };
            loop {
                if next > end {
                    break;
                }
                let best = objects
                    .iter()
                    .filter(|object| object.first <= next && next <= object.last)
                    .max_by_key(|object| object.last);
                let object = match best {
                    Some(object) => object,
                    None => {
                        // A gap: an earlier run cannot reach the head, so a
                        // later one replaces it.
                        let Some(after) = objects
                            .iter()
                            .filter(|object| object.first > next && object.first <= end)
                            .min_by_key(|object| object.first)
                        else {
                            break;
                        };
                        plan = Plan::default();
                        next = after.first;
                        continue;
                    }
                };
                let last = Lsn(object.last.0.min(end.0));
                plan.parts.push((object.clone(), next, last));
                plan.run = Some((plan.run.map_or(next, |(first, _)| first), last));
                next = Lsn(last.0 + 1);
            }
        }
        Ok(plan)
    }

    /// The highest lineage of `stream` and its lineage map, for a restore
    /// with no surviving voter. The map comes from the newest lineage
    /// object; without one, lineage 0 from LSN 1.
    pub async fn discover(&self, stream: StreamId) -> io::Result<(u64, Vec<(u64, Lsn)>)> {
        let lineages = self.lineages(stream).await?;
        for lineage in lineages.iter().rev() {
            if let Some(record) = self.lineage_record(stream, *lineage).await? {
                return Ok((record.lineage, record.lineages));
            }
        }
        match lineages.first() {
            Some(0) | None => Ok((0, vec![(0, Lsn(1))])),
            Some(_) => Err(invalid(
                "the offload store holds lineages without their lineage records",
            )),
        }
    }

    /// Fetches the segments a plan names, verified.
    pub async fn segments(
        &self,
        stream: StreamId,
        plan: &Plan,
    ) -> io::Result<Vec<(Arc<Segment>, Lsn, Lsn)>> {
        let mut out = Vec::with_capacity(plan.parts.len());
        for (object, first, last) in &plan.parts {
            out.push((self.segment(stream, object).await?, *first, *last));
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use journal_contract::Epoch;

    fn records(first: u64, last: u64) -> Vec<Record> {
        (first..=last)
            .map(|lsn| Record {
                lsn: Lsn(lsn),
                timed: false,
                bytes: Bytes::from(format!("r{lsn}")),
            })
            .collect()
    }

    fn store() -> (tempfile::TempDir, Store) {
        let dir = tempfile::tempdir().unwrap();
        let config: OffloadConfig = serde_json::from_value(serde_json::json!({
            "url": format!("file://{}", dir.path().display()),
        }))
        .unwrap();
        let store = Store::open(&config).unwrap();
        (dir, store)
    }

    #[tokio::test]
    async fn uploads_are_idempotent_and_plans_follow_lineages() {
        let (_dir, store) = store();
        let stream = StreamId(3);
        assert_eq!(
            store.discover(stream).await.unwrap(),
            (0, vec![(0, Lsn(1))])
        );
        let (created, _) = store
            .upload(stream, 0, &records(1, 10), vec![(Lsn(1), Epoch(1))])
            .await
            .unwrap();
        assert!(created);
        let (created, _) = store
            .upload(stream, 0, &records(1, 10), Vec::new())
            .await
            .unwrap();
        assert!(!created, "a second upload of the same range is a no-op");
        // A batching another leader chose overlaps, and a deposed history
        // keeps uploading past the next lineage's start.
        store
            .upload(stream, 0, &records(5, 20), Vec::new())
            .await
            .unwrap();
        store
            .upload(stream, 0, &records(21, 40), Vec::new())
            .await
            .unwrap();
        store
            .upload(stream, 1, &records(16, 25), Vec::new())
            .await
            .unwrap();
        let lineages = [(0, Lsn(1)), (1, Lsn(16))];
        store
            .put_lineage(&LineageRecord {
                stream,
                lineage: 1,
                lineages: lineages.to_vec(),
                floor: Lsn(1),
                epoch: Epoch(1),
            })
            .await
            .unwrap();
        let plan = store.plan(stream, &lineages, Lsn(1)).await.unwrap();
        assert_eq!(plan.run, Some((Lsn(1), Lsn(25))));
        assert!(
            plan.parts
                .iter()
                .all(|(object, first, _)| { (object.lineage == 0) == (first.0 < 16) })
        );
        let lsns = store
            .segments(stream, &plan)
            .await
            .unwrap()
            .into_iter()
            .flat_map(|(segment, first, last)| {
                segment
                    .records
                    .iter()
                    .map(|record| record.lsn)
                    .filter(|lsn| *lsn >= first && *lsn <= last)
                    .map(|lsn| lsn.0)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        assert_eq!(lsns, (1..=25).collect::<Vec<_>>());
        assert_eq!(
            store.discover(stream).await.unwrap(),
            (1, lineages.to_vec())
        );
        let read = store
            .read(stream, 0, Lsn(3), Lsn(15), 100, usize::MAX)
            .await
            .unwrap();
        assert_eq!(read.first().unwrap().lsn, Lsn(3));
        assert_eq!(read.last().unwrap().lsn, Lsn(15));
        // A gap below the head starts a new run.
        store
            .upload(stream, 1, &records(30, 31), Vec::new())
            .await
            .unwrap();
        let plan = store.plan(stream, &lineages, Lsn(1)).await.unwrap();
        assert_eq!(plan.run, Some((Lsn(30), Lsn(31))));
    }
}
