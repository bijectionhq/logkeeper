//! A shared timer for long polls, independent of the caller's async executor.

use std::{
    collections::BTreeMap,
    future::Future,
    pin::Pin,
    sync::{Condvar, Mutex, OnceLock},
    task::{Context, Poll, Waker},
    time::{Duration, Instant},
};

#[derive(Default)]
struct Alarm {
    pending: BTreeMap<(Instant, u64), Waker>,
    next: u64,
}

#[derive(Default)]
struct Timer {
    alarm: Mutex<Alarm>,
    changed: Condvar,
}

fn timer() -> &'static Timer {
    static TIMER: OnceLock<Timer> = OnceLock::new();
    TIMER.get_or_init(|| {
        std::thread::Builder::new()
            .name("journal-timer".into())
            .spawn(|| {
                // Initialization finishes before the worker acquires the timer.
                let timer = TIMER.wait();
                let mut alarm = timer.alarm.lock().unwrap();
                loop {
                    if let Some((&(deadline, _), _)) = alarm.pending.first_key_value() {
                        let remaining = deadline.saturating_duration_since(Instant::now());
                        if remaining.is_zero() {
                            let (_, waker) = alarm.pending.pop_first().unwrap();
                            drop(alarm);
                            waker.wake();
                            alarm = timer.alarm.lock().unwrap();
                        } else {
                            alarm = timer.changed.wait_timeout(alarm, remaining).unwrap().0;
                        }
                    } else {
                        alarm = timer.changed.wait(alarm).unwrap();
                    }
                }
            })
            .expect("start journal timer");
        Timer::default()
    })
}

pub(crate) struct Sleep {
    deadline: Option<Instant>,
    id: Option<u64>,
}

impl Sleep {
    pub(crate) fn new(duration: Duration) -> Self {
        Self {
            deadline: Instant::now().checked_add(duration),
            id: None,
        }
    }
}

impl Future for Sleep {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        let Some(deadline) = self.deadline else {
            return Poll::Pending;
        };
        if deadline <= Instant::now() {
            return Poll::Ready(());
        }

        let timer = timer();
        let mut alarm = timer.alarm.lock().unwrap();
        let id = *self.id.get_or_insert_with(|| {
            let id = alarm.next;
            alarm.next += 1;
            id
        });
        alarm.pending.insert((deadline, id), cx.waker().clone());
        timer.changed.notify_one();
        Poll::Pending
    }
}

impl Drop for Sleep {
    fn drop(&mut self) {
        if let (Some(deadline), Some(id)) = (self.deadline, self.id) {
            let timer = timer();
            timer.alarm.lock().unwrap().pending.remove(&(deadline, id));
            timer.changed.notify_one();
        }
    }
}
