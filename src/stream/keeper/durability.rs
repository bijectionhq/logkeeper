use std::fs::File;
use std::path::Path;

/// Flushes a file's data and metadata to the device,.
/// On Apple platforms that is `fsync`; the standard library's `sync_all` there issues `F_FULLFSYNC`, which also drains the drive's write cache.
pub fn sync_file(file: &File) -> std::io::Result<()> {
    #[cfg(test)]
    SYNCS.with(|count| count.set(count.get() + 1));
    #[cfg(target_vendor = "apple")]
    {
        use std::os::fd::AsRawFd;
        // SAFETY: the descriptor is owned by `file`, which outlives the call.
        if unsafe { libc::fsync(file.as_raw_fd()) } == 0 {
            Ok(())
        } else {
            Err(std::io::Error::last_os_error())
        }
    }
    #[cfg(not(target_vendor = "apple"))]
    {
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
thread_local! { static SYNCS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) }; }

#[cfg(test)]
pub(super) fn syncs() -> usize {
    SYNCS.with(std::cell::Cell::get)
}
