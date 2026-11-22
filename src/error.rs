use std::path::PathBuf;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorKind {
    Incorrect,
    Unavailable,
    Conflict,
    Fault,
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("{message}")]
    Reported { kind: ErrorKind, code: &'static str, message: String },
    #[error("requested log position {requested} is unavailable; first retained position is {first_retained}")]
    UnavailableLogRange { requested: i64, first_retained: i64 },
    #[error("log is closed: {0}")]
    Closed(String),
    #[error("cannot append to read-only log {0}")]
    ReadOnlyLog(PathBuf),
    #[error("message has {size} bytes; maximum is {maximum}")]
    MessageTooLarge { size: usize, maximum: usize },
    #[error("storage task failed: {0}")]
    Task(String),
    #[error("remote storage at {key}: {message}")]
    Remote { key: String, message: String },
    #[error("log writer at epoch {epoch} was deposed by a seal at epoch {promised}")]
    Deposed { epoch: u64, promised: u64 },
}

impl Error {
    pub(crate) fn reported(kind: ErrorKind, code: &'static str, message: impl Into<String>) -> Self {
        Self::Reported { kind, code, message: message.into() }
    }

    pub(crate) fn incorrect(code: &'static str, message: impl Into<String>) -> Self {
        Self::reported(ErrorKind::Incorrect, code, message)
    }

    pub(crate) fn fault(code: &'static str, message: impl Into<String>) -> Self {
        Self::reported(ErrorKind::Fault, code, message)
    }

    pub fn code(&self) -> &'static str {
        match self {
            Self::Reported { code, .. } => code,
            Self::UnavailableLogRange { .. } => "rtdb.storage/log-range-unavailable",
            Self::Closed(_) => "rtdb.storage/closed",
            Self::ReadOnlyLog(_) => "rtdb.storage/read-only-log",
            Self::MessageTooLarge { .. } => "rtdb.storage/message-too-large",
            Self::Task(_) => "rtdb.storage/task",
            Self::Remote { .. } => "rtdb.storage/remote",
            Self::Deposed { .. } => "rtdb.storage/deposed",
        }
    }

    pub fn kind(&self) -> ErrorKind {
        match self {
            Self::Reported { kind, .. } => *kind,
            Self::UnavailableLogRange { .. } | Self::Closed(_) | Self::Remote { .. } => ErrorKind::Unavailable,
            Self::ReadOnlyLog(_) | Self::MessageTooLarge { .. } => ErrorKind::Incorrect,
            Self::Task(_) => ErrorKind::Fault,
            Self::Deposed { .. } => ErrorKind::Conflict,
        }
    }
}
