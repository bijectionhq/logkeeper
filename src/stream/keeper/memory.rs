//! Run the keeper reducer with resident payloads and synchronous persistence in tests.

use std::collections::HashMap;


use super::{
    Limits,
    rules::Decision,
    state::{self, ExtentReader, Stream},
};
use crate::stream::{codec, wire::*};

#[derive(Default)]
pub(crate) struct Memory {
    streams: HashMap<StreamId, Stream>,
}

impl Memory {
    pub(crate) fn view(&self, id: StreamId) -> Option<&StreamView> {
        self.streams.get(&id).map(|stream| &stream.view)
    }

    pub(crate) fn call(
        &mut self,
        keeper: KeeperId,
        identity: &Identity,
        request: Request,
        limits: &Limits,
    ) -> Reply {
        let id = codec::stream(&request);
        let stream = self.streams.get(&id);
        let mut reader = ExtentReader::default();
        match state::decide(
            stream,
            keeper,
            &request,
            identity,
            true,
            limits,
            &mut reader,
        )
        .unwrap()
        {
            Decision::Reply(reply) => reply,
            Decision::Persist => self
                .streams
                .entry(id)
                .or_default()
                .apply(keeper, request, Some(identity.clone()))
                .unwrap(),
            Decision::Page { through } => {
                let (Request::Read { from, max, .. } | Request::Recover { from, max, .. }) =
                    request
                else {
                    unreachable!()
                };
                stream
                    .unwrap()
                    .page(from, max, through, &mut reader)
                    .unwrap()
            }
        }
    }
}
