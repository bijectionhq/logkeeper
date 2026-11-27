use std::fs::File;
use std::path::Path;
use std::sync::atomic::{AtomicU8, Ordering};

/// How a durable write reaches stable storage.
///
/// On Apple platforms `fsync` only hands the data to the drive, whose volatile
/// write cache may still lose it on power loss; `F_FULLFSYNC` also drains that
/// cache. Elsewhere both modes flush the same way: Linux's `fsync` and
/// `fdatasync` already ask the device to flush its cache.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(
    any(feature = "stream", feature = "ordered-daemon"),
    derive(serde::Deserialize, serde::Serialize),
    serde(rename_all = "lowercase")
)]
pub enum SyncMode {
    /// `fsync`, which on Apple platforms leaves the data in the drive's
    /// write cache.
    Fsync,
    /// `F_FULLFSYNC` on Apple platforms, which survives power loss.
    #[default]
    Full,
}

const UNSET: u8 = 0;

/// The process's sync mode. Until a keeper sets it, durable writes use
/// [`SyncMode::Full`].
static MODE: AtomicU8 = AtomicU8::new(UNSET);

impl SyncMode {
    fn code(self) -> u8 {
        match self {
            SyncMode::Fsync => 1,
            SyncMode::Full => 2,
        }
    }

    fn decode(code: u8) -> Self {
        if code == SyncMode::Fsync.code() {
            SyncMode::Fsync
        } else {
            SyncMode::Full
        }
    }

    /// Makes `self` the mode of every durable write in this process.
    ///
    /// The mode is process-wide because the writes it governs sit below any
    /// one keeper's state. Several keepers in one process that ask for
    /// different modes all get the stronger, so no keeper's configured
    /// durability is weakened by another's.
    pub fn install(self) {
        install_into(&MODE, self);
    }

    /// The mode durable writes in this process use.
    pub fn current() -> Self {
        SyncMode::decode(MODE.load(Ordering::Acquire))
    }

    /// The mode a keeper or harness installed in this process, if any.
    pub fn installed() -> Option<Self> {
        match MODE.load(Ordering::Acquire) {
            UNSET => None,
            code => Some(SyncMode::decode(code)),
        }
    }
}

fn install_into(mode: &AtomicU8, wanted: SyncMode) {
    let wanted = wanted.code();
    let mut current = mode.load(Ordering::Acquire);
    loop {
        let next = if current == UNSET {
            wanted
        } else {
            current.max(wanted)
        };
        match mode.compare_exchange_weak(current, next, Ordering::AcqRel, Ordering::Acquire) {
            Ok(_) => return,
            Err(seen) => current = seen,
        }
    }
}

/// Flushes a file's data and metadata to the device, in the process's
/// [`SyncMode`].
pub fn sync_file(file: &File) -> std::io::Result<()> {
    flush(file, SyncMode::current())
}

/// Flushes a file's data and metadata to the device in `mode`.
pub fn flush(file: &File, mode: SyncMode) -> std::io::Result<()> {
    #[cfg(target_vendor = "apple")]
    {
        use std::os::fd::AsRawFd;
        let descriptor = file.as_raw_fd();
        if mode == SyncMode::Full {
            loop {
                // SAFETY: the descriptor is owned by `file`, which outlives the call.
                if unsafe { libc::fcntl(descriptor, libc::F_FULLFSYNC) } != -1 {
                    return Ok(());
                }
                let error = std::io::Error::last_os_error();
                match error.raw_os_error() {
                    Some(libc::EINTR) => continue,
                    // A file system without a full flush, such as some network
                    // or virtual ones, gets the strongest flush it has.
                    Some(libc::ENOTSUP | libc::EINVAL | libc::ENOTTY) => break,
                    _ => return Err(error),
                }
            }
        }
        // SAFETY: the descriptor is owned by `file`, which outlives the call.
        if unsafe { libc::fsync(descriptor) } == 0 {
            Ok(())
        } else {
            Err(std::io::Error::last_os_error())
        }
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        let _ = mode;
        file.sync_all()
    }
}

/// Flushes the directory entries that publish or remove durable files.
pub fn sync_directory(path: &Path) -> std::io::Result<()> {
    sync_file(&open_for_sync(path)?)
}

fn open_for_sync(path: &Path) -> std::io::Result<File> {
    #[cfg(windows)]
    {
        use std::os::windows::fs::OpenOptionsExt as _;

        const FILE_FLAG_BACKUP_SEMANTICS: u32 = 0x0200_0000;
        const FILE_FLAG_OPEN_REPARSE_POINT: u32 = 0x0020_0000;
        // A Windows directory handle requires backup semantics to open.
        // Flushing the handle requires write access.
        let directory = File::options()
            .write(true)
            .custom_flags(FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OPEN_REPARSE_POINT)
            .open(path)?;
        let kind = directory.metadata()?.file_type();
        if !kind.is_dir() || kind.is_symlink() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::NotADirectory,
                "expected a directory for flushing",
            ));
        }
        Ok(directory)
    }
    #[cfg(not(windows))]
    {
        File::open(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unset_mode_is_full_and_the_stronger_mode_wins() {
        let mode = AtomicU8::new(UNSET);
        assert_eq!(
            SyncMode::decode(mode.load(Ordering::Acquire)),
            SyncMode::Full
        );
        install_into(&mode, SyncMode::Fsync);
        assert_eq!(
            SyncMode::decode(mode.load(Ordering::Acquire)),
            SyncMode::Fsync
        );
        install_into(&mode, SyncMode::Full);
        assert_eq!(
            SyncMode::decode(mode.load(Ordering::Acquire)),
            SyncMode::Full
        );
        install_into(&mode, SyncMode::Fsync);
        assert_eq!(
            SyncMode::decode(mode.load(Ordering::Acquire)),
            SyncMode::Full
        );
        assert_eq!(SyncMode::default(), SyncMode::Full);
    }

    #[cfg(any(feature = "stream", feature = "ordered-daemon"))]
    #[test]
    fn configurations_name_the_mode_in_lowercase() {
        let parse = |text: &str| serde_json::from_str::<SyncMode>(text);
        assert_eq!(parse("\"full\"").unwrap(), SyncMode::Full);
        assert_eq!(parse("\"fsync\"").unwrap(), SyncMode::Fsync);
        assert!(parse("\"Full\"").is_err());
        assert!(parse("\"fdatasync\"").is_err());
    }

    #[test]
    fn both_modes_flush_files_and_directories() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("file");
        std::fs::write(&path, b"durable").unwrap();
        let file = File::options().read(true).write(true).open(&path).unwrap();
        for mode in [SyncMode::Fsync, SyncMode::Full] {
            flush(&file, mode).unwrap();
            flush(&open_for_sync(directory.path()).unwrap(), mode).unwrap();
        }
    }
}
