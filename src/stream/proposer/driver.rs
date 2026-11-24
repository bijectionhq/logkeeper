//! Interpret proposer effects and return outcomes to the originating operation.

use std::{future::Future, sync::Arc, time::Duration};

use futures::{StreamExt, stream::FuturesUnordered};
use tokio::time::Instant;

use super::{Call, Dispatch, Input, Operation, Proposer, TransportError};
use crate::stream::wire::Transport;

pub(in crate::stream) const RPC_TIMEOUT: Duration = Duration::from_secs(5);

pub(in crate::stream) async fn run<O: Operation>(
    transport: &dyn Transport,
    operation: O,
    timeout: Option<Duration>,
) -> O::Output {
    drive(operation, |started, send| {
        call(transport, started, timeout, send)
    })
    .await
}

/// Broadcasts continue on the third keeper after the operation completes.
pub(in crate::stream) async fn run_detached<O: Operation>(
    transport: Arc<dyn Transport>,
    operation: O,
) -> O::Output {
    drive(operation, |started, send| {
        let slot = send.send.slot;
        let ticket = send.ticket;
        let transport = transport.clone();
        let task =
            tokio::spawn(async move { call(&*transport, started, Some(RPC_TIMEOUT), send).await });
        async move {
            task.await
                .unwrap_or(Input::Reply(slot, ticket, Err(TransportError::Unreachable)))
        }
    })
    .await
}

async fn drive<O, F>(operation: O, send: impl Fn(Instant, Call) -> F) -> O::Output
where
    O: Operation,
    F: Future<Output = Input>,
{
    let started = Instant::now();
    let mut calls = FuturesUnordered::new();
    let mut proposer = Proposer::new(operation);
    let mut effects = proposer.step(Input::Invoke, Duration::ZERO);
    loop {
        match effects {
            Dispatch::Pending => {}
            Dispatch::Send(call) => calls.push(send(started, call)),
            Dispatch::CancelAndSend(call) => {
                calls.clear();
                calls.push(send(started, call));
            }
            Dispatch::Pair(sends) => {
                calls.extend(sends.map(|call| send(started, call)));
            }
            Dispatch::Round(sends) => {
                calls.extend(sends.map(|call| send(started, call)));
            }
            Dispatch::Sleep(duration) => {
                tokio::time::sleep(duration).await;
                effects = proposer.step(Input::Timer, started.elapsed());
                continue;
            }
            Dispatch::Complete(output) => return output,
        }
        let Some(event) = calls.next().await else {
            return O::exhausted();
        };
        effects = proposer.step(event, started.elapsed());
    }
}

async fn call(
    transport: &dyn Transport,
    started: Instant,
    timeout: Option<Duration>,
    call: Call,
) -> Input {
    let Call { send, ticket } = call;
    let wait = match send.request {
        crate::stream::wire::Request::Read { wait_ms, .. } => Duration::from_millis(wait_ms.into()),
        _ => Duration::ZERO,
    };
    let call = transport.call(send.keeper, send.request);
    if let Some(deadline) = send.deadline {
        return match tokio::time::timeout_at(started + deadline, call).await {
            Ok(reply) => Input::Reply(send.slot, ticket, reply),
            Err(_) => Input::Expired(send.slot, ticket),
        };
    }
    let reply = match timeout {
        Some(timeout) => tokio::time::timeout(timeout + wait, call)
            .await
            .unwrap_or(Err(TransportError::TimedOut)),
        None => call.await,
    };
    Input::Reply(send.slot, ticket, reply)
}
