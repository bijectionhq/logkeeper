//! Structured tracing subscriber, rate-limited repeat suppression, and audit
//! logging for the consensus keeper.

use std::{
    collections::HashMap,
    fmt,
    io::{self, Write},
    sync::{
        Arc, LazyLock,
        atomic::{AtomicU64, Ordering},
    },
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use journal_contract::{Epoch, Lsn, StreamId};
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};
use tracing::{
    Event, Level, Metadata, Subscriber,
    field::{Field, Visit},
    level_filters::LevelFilter,
    span::{Attributes, Id, Record},
};
use uuid::Uuid;

/// Default window for suppressing repeated noisy warnings on the same key.
pub(super) const REPEAT_INTERVAL: Duration = Duration::from_secs(5);
const MAX_RATE_KEYS: usize = 1024;

/// Output format for consensus keeper logs.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum LogFormat {
    /// Human-readable timestamped key-value lines (default).
    #[default]
    Human,
    /// One JSON object per line.
    Json,
}

impl LogFormat {
    pub fn parse(value: &str) -> Option<Self> {
        match value.to_ascii_lowercase().as_str() {
            "human" | "text" => Some(Self::Human),
            "json" => Some(Self::Json),
            _ => None,
        }
    }
}

/// Formats a `StreamId` as a canonical hyphenated UUID for structured log fields.
pub(super) fn stream_uuid(stream: StreamId) -> Uuid {
    Uuid::from_u128(stream.0)
}

/// Installs the global structured tracing subscriber if none is installed yet.
///
/// Respects `LOGKEEPER_LOG_FORMAT` (`human` or `json`) over `default_format`,
/// and `LOGKEEPER_LOG` / `RUST_LOG` for the maximum level (default `info` for
/// `logkeeper`, `warn` for other crates such as `openraft`).
pub fn init(default_format: LogFormat) {
    let format = std::env::var("LOGKEEPER_LOG_FORMAT")
        .ok()
        .and_then(|value| LogFormat::parse(&value))
        .unwrap_or(default_format);
    let filter = std::env::var("LOGKEEPER_LOG")
        .or_else(|_| std::env::var("RUST_LOG"))
        .ok();
    let (logkeeper_level, other_level) = parse_filter(filter.as_deref());
    let subscriber = KeeperSubscriber::new(format, logkeeper_level, other_level, stderr_sink());
    let _ = tracing::subscriber::set_global_default(subscriber);
}

fn parse_filter(spec: Option<&str>) -> (LevelFilter, LevelFilter) {
    let Some(spec) = spec else {
        return (LevelFilter::INFO, LevelFilter::WARN);
    };
    let mut logkeeper = LevelFilter::INFO;
    let mut other = LevelFilter::WARN;
    for directive in spec.split(',').map(str::trim).filter(|s| !s.is_empty()) {
        if let Some((target, level)) = directive.split_once('=') {
            if let Some(level) = parse_level(level) {
                if target == "logkeeper" || target.starts_with("logkeeper::") {
                    logkeeper = level;
                } else {
                    other = level;
                }
            }
        } else if let Some(level) = parse_level(directive) {
            logkeeper = level;
            other = level;
        }
    }
    (logkeeper, other)
}

fn parse_level(value: &str) -> Option<LevelFilter> {
    match value.to_ascii_lowercase().as_str() {
        "off" => Some(LevelFilter::OFF),
        "error" => Some(LevelFilter::ERROR),
        "warn" | "warning" => Some(LevelFilter::WARN),
        "info" => Some(LevelFilter::INFO),
        "debug" => Some(LevelFilter::DEBUG),
        "trace" => Some(LevelFilter::TRACE),
        _ => None,
    }
}

type Sink = Arc<dyn Fn(&str) + Send + Sync>;

fn stderr_sink() -> Sink {
    Arc::new(|line: &str| {
        let mut stderr = io::stderr().lock();
        let _ = stderr.write_all(line.as_bytes());
        let _ = stderr.write_all(b"\n");
    })
}

/// Minimal, zero-extra-dependency `tracing::Subscriber` that emits structured
/// human-readable or JSON lines.
pub(super) struct KeeperSubscriber {
    format: LogFormat,
    logkeeper_level: LevelFilter,
    other_level: LevelFilter,
    sink: Sink,
    next_span: AtomicU64,
}

impl KeeperSubscriber {
    pub(super) fn new(
        format: LogFormat,
        logkeeper_level: LevelFilter,
        other_level: LevelFilter,
        sink: Sink,
    ) -> Self {
        Self {
            format,
            logkeeper_level,
            other_level,
            sink,
            next_span: AtomicU64::new(1),
        }
    }

    fn allowed(&self, metadata: &Metadata<'_>) -> bool {
        let limit = if metadata.target().starts_with("logkeeper") {
            self.logkeeper_level
        } else {
            self.other_level
        };
        *metadata.level() <= limit
    }
}

impl Subscriber for KeeperSubscriber {
    fn enabled(&self, metadata: &Metadata<'_>) -> bool {
        self.allowed(metadata)
    }

    fn max_level_hint(&self) -> Option<LevelFilter> {
        Some(self.logkeeper_level.max(self.other_level))
    }

    fn new_span(&self, _span: &Attributes<'_>) -> Id {
        Id::from_u64(self.next_span.fetch_add(1, Ordering::Relaxed))
    }

    fn record(&self, _span: &Id, _values: &Record<'_>) {}

    fn record_follows_from(&self, _span: &Id, _follows: &Id) {}

    fn event(&self, event: &Event<'_>) {
        let metadata = event.metadata();
        if !self.allowed(metadata) {
            return;
        }
        let mut visitor = FieldVisitor::default();
        event.record(&mut visitor);
        let timestamp = format_timestamp(SystemTime::now());
        let level = level_str(*metadata.level());
        let target = metadata.target();
        let line = match self.format {
            LogFormat::Human => format_human(&timestamp, level, target, &visitor),
            LogFormat::Json => format_json(&timestamp, level, target, &visitor),
        };
        (self.sink)(&line);
    }

    fn enter(&self, _span: &Id) {}

    fn exit(&self, _span: &Id) {}
}

fn level_str(level: Level) -> &'static str {
    match level {
        Level::ERROR => "ERROR",
        Level::WARN => "WARN",
        Level::INFO => "INFO",
        Level::DEBUG => "DEBUG",
        Level::TRACE => "TRACE",
    }
}

#[derive(Default)]
struct FieldVisitor {
    message: Option<String>,
    fields: Vec<(&'static str, FieldValue)>,
}

enum FieldValue {
    Bool(bool),
    I64(i64),
    U64(u64),
    F64(f64),
    Str(String),
}

impl Visit for FieldVisitor {
    fn record_bool(&mut self, field: &Field, value: bool) {
        self.fields.push((field.name(), FieldValue::Bool(value)));
    }

    fn record_i64(&mut self, field: &Field, value: i64) {
        self.fields.push((field.name(), FieldValue::I64(value)));
    }

    fn record_u64(&mut self, field: &Field, value: u64) {
        self.fields.push((field.name(), FieldValue::U64(value)));
    }

    fn record_f64(&mut self, field: &Field, value: f64) {
        self.fields.push((field.name(), FieldValue::F64(value)));
    }

    fn record_str(&mut self, field: &Field, value: &str) {
        if field.name() == "message" {
            self.message = Some(value.to_owned());
        } else {
            self.fields
                .push((field.name(), FieldValue::Str(value.to_owned())));
        }
    }

    fn record_error(&mut self, field: &Field, value: &(dyn std::error::Error + 'static)) {
        self.fields
            .push((field.name(), FieldValue::Str(value.to_string())));
    }

    fn record_debug(&mut self, field: &Field, value: &dyn fmt::Debug) {
        let formatted = format!("{value:?}");
        if field.name() == "message" {
            self.message = Some(formatted);
        } else {
            self.fields.push((field.name(), FieldValue::Str(formatted)));
        }
    }
}

fn format_human(timestamp: &str, level: &str, target: &str, visitor: &FieldVisitor) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(128);
    let _ = write!(&mut out, "{timestamp} {level} {target}:");
    if let Some(message) = &visitor.message {
        let _ = write!(&mut out, " {message}");
    }
    for (name, value) in &visitor.fields {
        let _ = write!(&mut out, " {name}=");
        match value {
            FieldValue::Bool(v) => {
                let _ = write!(&mut out, "{v}");
            }
            FieldValue::I64(v) => {
                let _ = write!(&mut out, "{v}");
            }
            FieldValue::U64(v) => {
                let _ = write!(&mut out, "{v}");
            }
            FieldValue::F64(v) => {
                let _ = write!(&mut out, "{v}");
            }
            FieldValue::Str(v) => {
                if v.is_empty() || v.contains(char::is_whitespace) || v.contains('"') {
                    let _ = write!(&mut out, "{v:?}");
                } else {
                    out.push_str(v);
                }
            }
        }
    }
    out
}

fn format_json(timestamp: &str, level: &str, target: &str, visitor: &FieldVisitor) -> String {
    let mut map = serde_json::Map::with_capacity(visitor.fields.len() + 4);
    map.insert(
        "timestamp".into(),
        serde_json::Value::String(timestamp.to_owned()),
    );
    map.insert("level".into(), serde_json::Value::String(level.to_owned()));
    map.insert(
        "target".into(),
        serde_json::Value::String(target.to_owned()),
    );
    if let Some(message) = &visitor.message {
        map.insert("message".into(), serde_json::Value::String(message.clone()));
    }
    for (name, value) in &visitor.fields {
        let json = match value {
            FieldValue::Bool(v) => serde_json::Value::Bool(*v),
            FieldValue::I64(v) => serde_json::Value::from(*v),
            FieldValue::U64(v) => serde_json::Value::from(*v),
            FieldValue::F64(v) => serde_json::Number::from_f64(*v)
                .map(serde_json::Value::Number)
                .unwrap_or_else(|| serde_json::Value::String(v.to_string())),
            FieldValue::Str(v) => serde_json::Value::String(v.clone()),
        };
        map.insert((*name).to_owned(), json);
    }
    serde_json::Value::Object(map).to_string()
}

/// Formats `time` as ISO-8601 UTC (`YYYY-MM-DDTHH:MM:SS.mmmZ`).
fn format_timestamp(time: SystemTime) -> String {
    let duration = time.duration_since(UNIX_EPOCH).unwrap_or_default();
    let secs = duration.as_secs();
    let millis = duration.subsec_millis();
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    let hour = rem / 3_600;
    let minute = (rem % 3_600) / 60;
    let second = rem % 60;
    // Howard Hinnant's civil_from_days algorithm (days since 1970-01-01).
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097) as u64;
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = y + i64::from(month <= 2);
    format!("{year:04}-{month:02}-{day:02}T{hour:02}:{minute:02}:{second:02}.{millis:03}Z")
}

/// Suppresses repeated log events per `(key, stream)` within a window and
/// returns the count of suppressed repeats when the next event is allowed.
pub(super) struct LogRateLimiter {
    entries: Mutex<HashMap<(&'static str, Option<StreamId>), RateState>>,
}

struct RateState {
    last: Instant,
    dropped: u64,
}

impl LogRateLimiter {
    pub(super) fn new() -> Self {
        Self {
            entries: Mutex::new(HashMap::new()),
        }
    }

    /// Returns `Some(dropped)` if an event for `(key, stream)` may be emitted
    /// at `now`, or `None` if it is suppressed (incrementing its dropped count).
    pub(super) fn allow(
        &self,
        key: &'static str,
        stream: Option<StreamId>,
        interval: Duration,
        now: Instant,
    ) -> Option<u64> {
        let mut entries = self.entries.lock();
        let map_key = (key, stream);
        if let Some(state) = entries.get_mut(&map_key) {
            if now.saturating_duration_since(state.last) < interval {
                state.dropped = state.dropped.saturating_add(1);
                return None;
            }
            let dropped = std::mem::take(&mut state.dropped);
            state.last = now;
            return Some(dropped);
        }
        if entries.len() >= MAX_RATE_KEYS
            && let Some(oldest) = entries
                .iter()
                .min_by_key(|(_, state)| state.last)
                .map(|(k, _)| *k)
        {
            entries.remove(&oldest);
        }
        entries.insert(
            map_key,
            RateState {
                last: now,
                dropped: 0,
            },
        );
        Some(0)
    }
}

static GLOBAL_RATE_LIMITER: LazyLock<LogRateLimiter> = LazyLock::new(LogRateLimiter::new);

/// Checks whether a repeated log event for `(key, stream)` should be emitted
/// now, returning `Some(dropped_since_last)` when allowed.
pub(super) fn rate_limit(key: &'static str, stream: Option<StreamId>) -> Option<u64> {
    GLOBAL_RATE_LIMITER.allow(key, stream, REPEAT_INTERVAL, Instant::now())
}

/// Audit log for a voter replacement (`replace`).
pub(super) fn audit_replace(
    keeper: Uuid,
    stream: StreamId,
    actor: &str,
    expected: u64,
    voters: &[Uuid; 3],
    outcome: &str,
) {
    let voters = format!("{},{},{}", voters[0], voters[1], voters[2]);
    tracing::info!(
        target: "logkeeper::audit",
        audit = true,
        action = "replace",
        keeper = %keeper,
        stream = %stream_uuid(stream),
        actor = %actor,
        expected_revision = expected,
        target_voters = %voters,
        outcome = %outcome,
        "admin action replace"
    );
}

/// Audit log for a preferred-leader request (`prefer_leader`).
pub(super) fn audit_prefer_leader(
    keeper: Uuid,
    stream: StreamId,
    actor: &str,
    target: Uuid,
    outcome: &str,
) {
    tracing::info!(
        target: "logkeeper::audit",
        audit = true,
        action = "prefer_leader",
        keeper = %keeper,
        stream = %stream_uuid(stream),
        actor = %actor,
        target_keeper = %target,
        outcome = %outcome,
        "admin action prefer_leader"
    );
}

/// Audit log for clearing a recovery fence (`acknowledge_recovery`).
pub(super) fn audit_acknowledge_recovery(
    keeper: Uuid,
    stream: StreamId,
    actor: &str,
    outcome: &str,
) {
    tracing::info!(
        target: "logkeeper::audit",
        audit = true,
        action = "acknowledge_recovery",
        keeper = %keeper,
        stream = %stream_uuid(stream),
        actor = %actor,
        outcome = %outcome,
        "admin action acknowledge_recovery"
    );
}

/// Audit log for retiring a removed copy (`retire`).
pub(super) fn audit_retire(
    keeper: Uuid,
    stream: StreamId,
    actor: &str,
    authority: Uuid,
    revision: u64,
    generation: u64,
    outcome: &str,
) {
    tracing::info!(
        target: "logkeeper::audit",
        audit = true,
        action = "retire",
        keeper = %keeper,
        stream = %stream_uuid(stream),
        actor = %actor,
        authority = %authority,
        revision = revision,
        generation = generation,
        outcome = %outcome,
        "admin action retire"
    );
}

/// Audit log for offline quorum-loss recovery (`recovery`).
#[allow(clippy::too_many_arguments)]
pub(super) fn audit_recovery(
    keeper: Uuid,
    stream: StreamId,
    lost: &[Uuid; 2],
    voters: &[Uuid; 3],
    revision: u64,
    head: Lsn,
    epoch: Epoch,
    term: u64,
    written: bool,
    outcome: &str,
) {
    let lost = format!("{},{}", lost[0], lost[1]);
    let voters = format!("{},{},{}", voters[0], voters[1], voters[2]);
    tracing::info!(
        target: "logkeeper::audit",
        audit = true,
        action = "recovery",
        keeper = %keeper,
        stream = %stream_uuid(stream),
        lost_voters = %lost,
        target_voters = %voters,
        revision = revision,
        head = head.0,
        epoch = epoch.0,
        term = term,
        written = written,
        outcome = %outcome,
        "admin action recovery"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rate_limiter_suppresses_repeats_and_reports_dropped_count() {
        let limiter = LogRateLimiter::new();
        let stream = StreamId(42);
        let t0 = Instant::now();
        let window = Duration::from_secs(5);

        assert_eq!(limiter.allow("refusal", Some(stream), window, t0), Some(0));
        assert_eq!(
            limiter.allow("refusal", Some(stream), window, t0 + Duration::from_secs(1)),
            None
        );
        assert_eq!(
            limiter.allow("refusal", Some(stream), window, t0 + Duration::from_secs(2)),
            None
        );
        assert_eq!(
            limiter.allow("refusal", Some(stream), window, t0 + Duration::from_secs(4)),
            None
        );
        // Independent key is not suppressed.
        assert_eq!(limiter.allow("other", Some(stream), window, t0), Some(0));
        // Once the window elapses, the next event reports the 3 dropped repeats.
        assert_eq!(
            limiter.allow("refusal", Some(stream), window, t0 + Duration::from_secs(5)),
            Some(3)
        );
        // Immediately after, dropped resets to 0.
        assert_eq!(
            limiter.allow(
                "refusal",
                Some(stream),
                window,
                t0 + Duration::from_secs(10)
            ),
            Some(0)
        );
    }

    #[test]
    fn subscriber_formats_human_and_json_with_level_filtering() {
        let lines = Arc::new(Mutex::new(Vec::<String>::new()));
        let sink: Sink = {
            let lines = lines.clone();
            Arc::new(move |line: &str| lines.lock().push(line.to_owned()))
        };
        let keeper = Uuid::from_u128(1);
        let stream = StreamId(2);

        let human = KeeperSubscriber::new(
            LogFormat::Human,
            LevelFilter::INFO,
            LevelFilter::WARN,
            sink.clone(),
        );
        tracing::subscriber::with_default(human, || {
            tracing::debug!(keeper = %keeper, "hidden debug");
            tracing::info!(
                keeper = %keeper,
                stream = %stream_uuid(stream),
                dropped = 4u64,
                "structured human event"
            );
            audit_acknowledge_recovery(keeper, stream, "urn:logkeeper:client:admin", "ok");
        });
        let captured = std::mem::take(&mut *lines.lock());
        assert_eq!(captured.len(), 2);
        assert!(captured[0].contains(" INFO "));
        assert!(captured[0].contains("structured human event"));
        assert!(captured[0].contains(&format!("keeper={keeper}")));
        assert!(captured[0].contains(&format!("stream={}", stream_uuid(stream))));
        assert!(captured[0].contains("dropped=4"));
        assert!(captured[1].contains("logkeeper::audit"));
        assert!(captured[1].contains("action=acknowledge_recovery"));
        assert!(captured[1].contains("actor=urn:logkeeper:client:admin"));

        let json =
            KeeperSubscriber::new(LogFormat::Json, LevelFilter::INFO, LevelFilter::WARN, sink);
        tracing::subscriber::with_default(json, || {
            tracing::warn!(
                keeper = %keeper,
                stream = %stream_uuid(stream),
                dropped = 7u64,
                "structured json event"
            );
        });
        let captured = std::mem::take(&mut *lines.lock());
        assert_eq!(captured.len(), 1);
        let parsed: serde_json::Value = serde_json::from_str(&captured[0]).unwrap();
        assert_eq!(parsed["level"], "WARN");
        assert_eq!(parsed["message"], "structured json event");
        assert_eq!(parsed["keeper"], keeper.to_string());
        assert_eq!(parsed["stream"], stream_uuid(stream).to_string());
        assert_eq!(parsed["dropped"], 7);
        assert!(parsed["timestamp"].as_str().unwrap().ends_with('Z'));
    }

    #[test]
    fn timestamp_formats_unix_epoch_and_known_date() {
        assert_eq!(format_timestamp(UNIX_EPOCH), "1970-01-01T00:00:00.000Z");
        // 2024-02-29T12:34:56.789Z (leap day)
        let leap = UNIX_EPOCH + Duration::from_millis(1_709_210_096_789);
        assert_eq!(format_timestamp(leap), "2024-02-29T12:34:56.789Z");
    }
}
