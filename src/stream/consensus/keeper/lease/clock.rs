use std::{io, time::Duration};

use tokio::time::{Instant, sleep};

use crate::stream::consensus::decisions;

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(super) fn now() -> Option<u64> {
    #[cfg(target_os = "linux")]
    let clock = libc::CLOCK_BOOTTIME;
    #[cfg(target_os = "macos")]
    let clock = libc::CLOCK_MONOTONIC_RAW;

    let mut value = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    // clock_gettime writes through a unique pointer to the initialized timespec.
    if unsafe { libc::clock_gettime(clock, &mut value) } != 0 {
        return None;
    }
    let seconds = u64::try_from(value.tv_sec).ok()?;
    let nanos = u64::try_from(value.tv_nsec).ok()?;
    const NANOS_PER_SECOND: u64 = 1_000_000_000;
    if nanos >= NANOS_PER_SECOND {
        return None;
    }
    seconds.checked_mul(NANOS_PER_SECOND)?.checked_add(nanos)
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub(super) fn now() -> Option<u64> {
    None
}

pub(super) fn unavailable() -> io::Error {
    io::Error::other("could not read the suspend-aware liveness lease clock")
}

/// Waits from the recovery's catalog acknowledgement. Retain at least the
/// previous Tokio wait so suspending the recovering keeper cannot shorten
/// the wait while an older build can still be a lease holder.
pub(super) async fn wait_for_expiry(
    window: Duration,
    now: impl Fn() -> Option<u64>,
) -> io::Result<()> {
    if window.is_zero() {
        return Ok(());
    }
    let started = now().ok_or_else(unavailable)?;
    let running = Instant::now();
    loop {
        let elapsed = now()
            .and_then(|sample| sample.checked_sub(started))
            .ok_or_else(unavailable)?;
        let elapsed = decisions::recovery_elapsed(elapsed, running.elapsed().as_nanos());
        let remaining = window.saturating_sub(Duration::from_nanos(elapsed));
        if remaining.is_zero() {
            return Ok(());
        }
        sleep(remaining.min(Duration::from_millis(100))).await;
    }
}

#[cfg(test)]
mod tests {
    use std::{cell::Cell, task::Poll};

    use super::*;

    #[tokio::test(start_paused = true)]
    async fn full_recovery_wait_requires_both_clocks_after_each_restart() {
        let window = Duration::from_secs(1);
        let continuous = Cell::new(0);
        let now = || Some(continuous.get());
        let window_nanos = u64::try_from(window.as_nanos()).unwrap();

        // A suspended recovery process sees only the continuous clock advance.
        let first = wait_for_expiry(window, now);
        tokio::pin!(first);
        assert!(futures::poll!(&mut first).is_pending());
        continuous.set(window_nanos);
        tokio::time::advance(Duration::from_millis(100)).await;
        assert!(futures::poll!(&mut first).is_pending());

        // A retry starts a fresh wait, even after the prior clock reached the window.
        let retry = wait_for_expiry(window, now);
        tokio::pin!(retry);
        assert!(futures::poll!(&mut retry).is_pending());
        tokio::time::advance(window).await;
        assert!(futures::poll!(&mut retry).is_pending());
        continuous.set(2 * window_nanos);
        tokio::time::advance(Duration::from_millis(100)).await;
        assert!(matches!(futures::poll!(&mut retry), Poll::Ready(Ok(()))));
    }

    #[tokio::test(start_paused = true)]
    async fn a_missing_or_reversed_clock_prevents_publication() {
        let window = Duration::from_secs(1);
        assert!(wait_for_expiry(window, || None).await.is_err());

        let continuous = Cell::new(1000);
        let wait = wait_for_expiry(window, || Some(continuous.get()));
        tokio::pin!(wait);
        assert!(futures::poll!(&mut wait).is_pending());
        continuous.set(999);
        tokio::time::advance(Duration::from_millis(100)).await;
        assert!(matches!(futures::poll!(&mut wait), Poll::Ready(Err(_))));
    }
}
