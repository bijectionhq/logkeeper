//! One long-lived multiplexed connection per keeper route, shared by every stream of the
//! process. Requests queued while a frame is being written are coalesced into the next
//! `Request::Batch`, which the keeper decides in one round with one sync.

use std::{
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::Duration,
};

use parking_lot::Mutex;
use tokio::{
    io::{ReadHalf, WriteHalf},
    sync::{mpsc, oneshot},
    time::timeout,
};
use tokio_rustls::TlsConnector;

use super::{Channel, connect, connection_error, protocol};
use crate::stream::{
    codec::{batched_request_len, decode_reply, read_frame, request_write::RequestWrite},
    wire::{KeeperId, Reply, Request, TransportError},
};

/// Frames written but not yet answered on one connection.
const PIPELINE: usize = 64;
/// Upper bounds for one coalesced frame, well below the 64 MiB frame limit.
pub(super) const BATCH_BYTES: usize = 4 * 1024 * 1024;
const BATCH_REQUESTS: usize = 4096;
/// Close an unused connection before the keeper's 60 s idle limit can race a new call.
const IDLE: Duration = Duration::from_secs(30);
/// The least time a connection may wait for an answered frame before it is presumed lost.
const MIN_STALL: Duration = Duration::from_secs(1);

type Answer = Result<Reply, Failure>;

/// Why a multiplexed call produced no reply.
pub(super) enum Failure {
    /// The request was never written, so it is safe to send it on a fresh connection.
    NotSent(Request),
    Transport(TransportError),
}

struct Call {
    request: Request,
    size: usize,
    reply: oneshot::Sender<Answer>,
}

struct Connection {
    queue: mpsc::UnboundedSender<Call>,
    closed: Arc<AtomicBool>,
}

pub(super) struct Mux {
    keeper: KeeperId,
    address: String,
    tls: TlsConnector,
    stall: Duration,
    current: Mutex<Option<Connection>>,
}

impl Mux {
    pub(super) fn new(
        keeper: KeeperId,
        address: String,
        tls: TlsConnector,
        deadline: Duration,
    ) -> Self {
        Self {
            keeper,
            address,
            tls,
            stall: deadline.max(MIN_STALL),
            current: Mutex::new(None),
        }
    }

    /// Adopt an already authenticated channel, for example one opened during discovery.
    pub(super) fn adopt(&self, channel: Channel) {
        *self.current.lock() = Some(self.spawn(Some(channel)));
    }

    pub(super) async fn call(&self, mut request: Request) -> Result<Reply, TransportError> {
        let size = batched_request_len(&request);
        // A request is resent only if the connection closed before writing it.
        loop {
            let (reply, answer) = oneshot::channel();
            {
                let mut current = self.current.lock();
                let live = current
                    .as_ref()
                    .is_some_and(|connection| !connection.closed.load(Ordering::Acquire));
                if !live {
                    *current = Some(self.spawn(None));
                }
                let call = Call {
                    request,
                    size,
                    reply,
                };
                if let Err(mpsc::error::SendError(call)) =
                    current.as_ref().expect("connection").queue.send(call)
                {
                    current.take();
                    request = call.request;
                    continue;
                }
            }
            match answer.await {
                Ok(Ok(reply)) => return Ok(reply),
                Ok(Err(Failure::NotSent(unsent))) => request = unsent,
                Ok(Err(Failure::Transport(error))) => return Err(error),
                Err(_) => return Err(TransportError::Unreachable),
            }
        }
    }

    fn spawn(&self, channel: Option<Channel>) -> Connection {
        let (queue, calls) = mpsc::unbounded_channel();
        let closed = Arc::new(AtomicBool::new(false));
        tokio::spawn(run(
            self.tls.clone(),
            self.address.clone(),
            self.keeper,
            self.stall,
            channel,
            calls,
            closed.clone(),
        ));
        Connection { queue, closed }
    }
}

async fn run(
    tls: TlsConnector,
    address: String,
    keeper: KeeperId,
    stall: Duration,
    channel: Option<Channel>,
    mut calls: mpsc::UnboundedReceiver<Call>,
    closed: Arc<AtomicBool>,
) {
    let channel = match channel {
        Some(channel) => Ok(channel),
        None => match timeout(stall, connect(&tls, &address)).await {
            Ok(Ok((peer, _))) if peer != keeper => Err(TransportError::Protocol(
                "keeper URI does not match route".into(),
            )),
            Ok(Ok((_, channel))) => Ok(channel),
            Ok(Err(error)) => Err(connection_error(error)),
            Err(_) => Err(TransportError::TimedOut),
        },
    };
    let (in_flight, answers) = mpsc::channel(PIPELINE);
    let mut carry = None;
    // Calls queued behind a failed connection attempt share its error. Calls left
    // unwritten by an established connection are retried on a fresh one.
    let refused = match channel {
        Err(error) => Some(error),
        Ok(channel) => {
            let (read, write) = tokio::io::split(channel);
            tokio::select! {
                _ = send(write, &mut calls, &mut carry, in_flight) => {},
                _ = receive(read, answers, stall) => {},
            }
            None
        }
    };
    closed.store(true, Ordering::Release);
    calls.close();
    let unsent = carry
        .into_iter()
        .chain(std::iter::from_fn(|| calls.try_recv().ok()));
    for call in unsent {
        let failure = match &refused {
            Some(error) => Failure::Transport(error.clone()),
            None => Failure::NotSent(call.request),
        };
        let _ = call.reply.send(Err(failure));
    }
}

/// Write coalesced frames. Returns when the connection must close.
async fn send(
    mut write: WriteHalf<Channel>,
    calls: &mut mpsc::UnboundedReceiver<Call>,
    carry: &mut Option<Call>,
    in_flight: mpsc::Sender<Vec<oneshot::Sender<Answer>>>,
) -> TransportError {
    loop {
        let first = match carry.take() {
            Some(call) => call,
            None => match timeout(IDLE, calls.recv()).await {
                Ok(Some(call)) => call,
                Ok(None) => return TransportError::Unreachable,
                Err(_) if in_flight.capacity() == in_flight.max_capacity() => {
                    return TransportError::Unreachable;
                }
                Err(_) => continue,
            },
        };
        let mut bytes = first.size;
        let mut batch = vec![first];
        while batch.len() < BATCH_REQUESTS {
            let Ok(call) = calls.try_recv() else { break };
            if bytes + call.size > BATCH_BYTES {
                *carry = Some(call);
                break;
            }
            bytes += call.size;
            batch.push(call);
        }
        // Skip requests whose callers have already given up.
        let (requests, replies): (Vec<_>, Vec<_>) = batch
            .into_iter()
            .filter(|call| !call.reply.is_closed())
            .map(|call| (call.request, call.reply))
            .unzip();
        let request = match requests.len() {
            0 => continue,
            1 => requests.into_iter().next().unwrap(),
            _ => Request::Batch(requests),
        };
        let request = match RequestWrite::preflight(request) {
            Ok(request) => request,
            Err(error) => {
                fail(replies, TransportError::Protocol(error.to_string()));
                continue;
            }
        };
        let Ok(permit) = in_flight.reserve().await else {
            fail(replies, TransportError::Unreachable);
            return TransportError::Unreachable;
        };
        // Register the ordered reply slot before any bytes from this frame are sent.
        permit.send(replies);
        if let Err(error) = request.write(&mut write).await {
            return connection_error(error);
        }
    }
}

/// Read replies in frame order and deliver them to the callers.
async fn receive(
    mut read: ReadHalf<Channel>,
    mut answers: mpsc::Receiver<Vec<oneshot::Sender<Answer>>>,
    stall: Duration,
) -> TransportError {
    loop {
        let Some(replies) = answers.recv().await else {
            return TransportError::Unreachable;
        };
        let frame = match timeout(stall, read_frame(&mut read)).await {
            Ok(Ok(frame)) => frame,
            Ok(Err(error)) => {
                let error = connection_error(error);
                fail(replies, error.clone());
                fail_all(&mut answers, &error);
                return error;
            }
            Err(_) => {
                fail(replies, TransportError::TimedOut);
                fail_all(&mut answers, &TransportError::TimedOut);
                return TransportError::TimedOut;
            }
        };
        let reply = match decode_reply(frame) {
            Ok(reply) => reply,
            Err(error) => {
                let error = protocol(error);
                fail(replies, error.clone());
                fail_all(&mut answers, &error);
                return error;
            }
        };
        let replies_len = replies.len();
        match (reply, replies_len) {
            (Reply::Batch(batch), count) if count > 1 && batch.len() == count => {
                for (sender, reply) in replies.into_iter().zip(batch) {
                    let _ = sender.send(Ok(reply));
                }
            }
            (reply, 1) if !matches!(reply, Reply::Batch(_)) => {
                let _ = replies.into_iter().next().unwrap().send(Ok(reply));
            }
            _ => {
                let error = TransportError::Protocol("keeper batch reply mismatch".into());
                fail(replies, error.clone());
                fail_all(&mut answers, &error);
                return error;
            }
        }
    }
}

fn fail(replies: Vec<oneshot::Sender<Answer>>, error: TransportError) {
    for reply in replies {
        let _ = reply.send(Err(Failure::Transport(error.clone())));
    }
}

fn fail_all(answers: &mut mpsc::Receiver<Vec<oneshot::Sender<Answer>>>, error: &TransportError) {
    answers.close();
    while let Ok(replies) = answers.try_recv() {
        fail(replies, error.clone());
    }
}
