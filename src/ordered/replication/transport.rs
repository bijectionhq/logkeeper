//! One bounded voter exchange over a mutually authenticated byte stream.
//!
//! The connection owner verifies the installed voter or coordinator identity
//! before passing the stream to this module. The addresses in a frame are
//! checked against that authorized scope.

use super::{
    Accepted, Ballot, DurableVoter, Error, Fingerprint, Group, Prefix, Promise, Replica, SlotImage,
    SlotPair, Vote,
};
use crate::ordered::codec::frame::{bounded_body_length, decode_flag, encode_flag};
use bytes::{Bytes, BytesMut};
use std::future::Future;
use std::io;
use std::time::Duration;
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use tokio::time::timeout;
use uuid::Uuid;

const MAGIC: &[u8; 8] = b"LKORPC04";
const PREPARE: u8 = 1;
const ACCEPT: u8 = 2;
const PROMISE: u8 = 3;
const VOTE: u8 = 4;
const DEPOSED: u8 = 5;
const REJECTED: u8 = 6;

/// Opens an authenticated channel to the exact voter for the installed group.
pub trait Connector: Sync {
    type Stream: AsyncRead + AsyncWrite + Unpin + Send;

    fn connect(
        &self,
        group: Fingerprint,
        voter: Uuid,
    ) -> impl Future<Output = Result<Self::Stream, Error>> + Send;
}

pub struct RemoteVoter<C> {
    connector: C,
    group: Fingerprint,
    voter: Uuid,
    max_prefix_bytes: usize,
    deadline: Duration,
}

impl<C: Connector> RemoteVoter<C> {
    pub fn new(
        group: &Group,
        voter: Uuid,
        connector: C,
        deadline: Duration,
    ) -> Result<Self, Error> {
        if !group.voters.contains(&voter) || deadline.is_zero() {
            return Err(Error::Group);
        }
        Ok(Self {
            connector,
            group: group.identity,
            voter,
            max_prefix_bytes: group.max_prefix_bytes,
            deadline,
        })
    }

    async fn open(
        &self,
        group: Fingerprint,
        operation: u8,
        ballot: Ballot,
    ) -> Result<C::Stream, Error> {
        if group != self.group {
            return Err(Error::Group);
        }
        let mut channel = self.connector.connect(group, self.voter).await?;
        channel.write_all(MAGIC).await?;
        channel.write_u8(operation).await?;
        channel.write_all(&group).await?;
        write_ballot(&mut channel, ballot).await?;
        Ok(channel)
    }

    async fn response(
        &self,
        channel: &mut C::Stream,
        expected: u8,
        ballot: Ballot,
    ) -> Result<(), Error> {
        check_magic(channel).await?;
        let kind = channel.read_u8().await?;
        if Uuid::from_bytes(read_array(channel).await?) != self.voter
            || read_ballot(channel).await? != ballot
        {
            return Err(Error::Group);
        }
        match kind {
            kind if kind == expected => Ok(()),
            DEPOSED => {
                let newer = read_ballot(channel).await?;
                if newer <= ballot {
                    return Err(Error::Prefix);
                }
                Err(Error::Deposed(newer))
            }
            REJECTED => Err(Error::Stopped),
            _ => Err(Error::Prefix),
        }
    }
}

impl<C: Connector> Replica for RemoteVoter<C> {
    fn identity(&self) -> Uuid {
        self.voter
    }

    async fn prepare(&self, group: Fingerprint, ballot: Ballot) -> Result<Promise, Error> {
        timeout(self.deadline, async {
            let mut channel = self.open(group, PREPARE, ballot).await?;
            channel.flush().await?;
            self.response(&mut channel, PROMISE, ballot).await?;
            let accepted = match decode_flag(channel.read_u8().await?) {
                Some(false) => None,
                Some(true) => Some(Accepted {
                    ballot: read_ballot(&mut channel).await?,
                    prefix: read_prefix(&mut channel, self.max_prefix_bytes).await?,
                }),
                None => return Err(Error::Prefix),
            };
            Ok(Promise {
                voter: self.voter,
                ballot,
                accepted,
            })
        })
        .await
        .map_err(timed_out)?
    }

    async fn accept(
        &self,
        group: Fingerprint,
        ballot: Ballot,
        prefix: &Prefix,
        read_back: bool,
    ) -> Result<Vote, Error> {
        if prefix.bytes > self.max_prefix_bytes {
            return Err(Error::Capacity);
        }
        timeout(self.deadline, async {
            let mut channel = self.open(group, ACCEPT, ballot).await?;
            channel.write_u8(u8::from(read_back)).await?;
            write_prefix(&mut channel, prefix).await?;
            channel.flush().await?;
            self.response(&mut channel, VOTE, ballot).await?;
            let digest = read_array(&mut channel).await?;
            let witnessed = channel.read_u8().await?;
            if witnessed != u8::from(read_back) {
                return Err(Error::Prefix);
            }
            let selected = channel.read_u8().await?;
            let mut read_image = async || -> Result<SlotImage, Error> {
                Ok(SlotImage {
                    generation: channel.read_u64().await?,
                    digest: read_array(&mut channel).await?,
                })
            };
            let slots = SlotPair {
                selected,
                images: [read_image().await?, read_image().await?],
            };
            Ok(Vote {
                voter: self.voter,
                ballot,
                digest,
                slots,
                read_back,
            })
        })
        .await
        .map_err(timed_out)?
    }
}

/// Serves one exchange from a coordinator already authenticated for
/// `authorized_group`. The listener owns connection admission and rate limits.
pub async fn serve_voter(
    voter: &DurableVoter,
    mut channel: impl AsyncRead + AsyncWrite + Unpin,
    authorized_group: Fingerprint,
    deadline: Duration,
) -> Result<(), Error> {
    timeout(deadline, async {
        check_magic(&mut channel).await?;
        let operation = channel.read_u8().await?;
        let group = read_array::<32>(&mut channel).await?;
        if group != authorized_group || group != voter.group() {
            return Err(Error::Group);
        }
        let ballot = read_ballot(&mut channel).await?;
        match operation {
            PREPARE => match voter.prepare(group, ballot).await {
                Ok(promise) => {
                    response_header(&mut channel, PROMISE, promise.voter, ballot).await?;
                    channel
                        .write_u8(encode_flag(promise.accepted.is_some()))
                        .await?;
                    if let Some(accepted) = promise.accepted {
                        write_ballot(&mut channel, accepted.ballot).await?;
                        write_prefix(&mut channel, &accepted.prefix).await?;
                    }
                }
                Err(error) => refuse(&mut channel, voter.identity(), ballot, error).await?,
            },
            ACCEPT => {
                let read_back = match channel.read_u8().await? {
                    0 => false,
                    1 => true,
                    _ => return Err(Error::Prefix),
                };
                let prefix = read_prefix(&mut channel, voter.max_prefix_bytes()).await?;
                match voter.accept(group, ballot, &prefix, read_back).await {
                    Ok(vote) => {
                        response_header(&mut channel, VOTE, vote.voter, ballot).await?;
                        channel.write_all(&vote.digest).await?;
                        channel.write_u8(u8::from(vote.read_back)).await?;
                        channel.write_u8(vote.slots.selected).await?;
                        for image in vote.slots.images {
                            channel.write_u64(image.generation).await?;
                            channel.write_all(&image.digest).await?;
                        }
                    }
                    Err(error) => refuse(&mut channel, voter.identity(), ballot, error).await?,
                }
            }
            _ => return Err(Error::Prefix),
        }
        channel.flush().await?;
        Ok(())
    })
    .await
    .map_err(timed_out)?
}

async fn refuse(
    channel: &mut (impl AsyncWrite + Unpin),
    voter: Uuid,
    ballot: Ballot,
    error: Error,
) -> Result<(), Error> {
    if let Error::Deposed(newer) = error {
        response_header(channel, DEPOSED, voter, ballot).await?;
        write_ballot(channel, newer).await
    } else {
        response_header(channel, REJECTED, voter, ballot).await
    }
}

async fn response_header(
    channel: &mut (impl AsyncWrite + Unpin),
    kind: u8,
    voter: Uuid,
    ballot: Ballot,
) -> Result<(), Error> {
    channel.write_all(MAGIC).await?;
    channel.write_u8(kind).await?;
    channel.write_all(voter.as_bytes()).await?;
    write_ballot(channel, ballot).await
}

async fn write_prefix(
    channel: &mut (impl AsyncWrite + Unpin),
    prefix: &Prefix,
) -> Result<(), Error> {
    let mut output = BytesMut::with_capacity(prefix.bytes);
    prefix.encode_into(&mut output);
    channel.write_u64(output.len() as u64).await?;
    channel.write_all(&output).await?;
    Ok(())
}

async fn read_prefix(
    channel: &mut (impl AsyncRead + Unpin),
    limit: usize,
) -> Result<Prefix, Error> {
    let length =
        bounded_body_length(channel.read_u64().await?, 1, limit).ok_or(Error::Capacity)?;
    let mut body = vec![0; length];
    channel.read_exact(&mut body).await?;
    Prefix::decode(Bytes::from(body), limit)
}

async fn write_ballot(
    channel: &mut (impl AsyncWrite + Unpin),
    ballot: Ballot,
) -> Result<(), Error> {
    channel.write_u64(ballot.round).await?;
    channel.write_all(ballot.nonce.as_bytes()).await?;
    Ok(())
}

async fn read_ballot(channel: &mut (impl AsyncRead + Unpin)) -> Result<Ballot, Error> {
    let round = channel.read_u64().await?;
    let nonce = Uuid::from_bytes(read_array(channel).await?);
    if round == 0 || nonce.is_nil() {
        return Err(Error::Prefix);
    }
    Ok(Ballot { round, nonce })
}

async fn check_magic(channel: &mut (impl AsyncRead + Unpin)) -> Result<(), Error> {
    if &read_array::<8>(channel).await? != MAGIC {
        return Err(Error::Prefix);
    }
    Ok(())
}

async fn read_array<const N: usize>(
    channel: &mut (impl AsyncRead + Unpin),
) -> Result<[u8; N], Error> {
    let mut value = [0; N];
    channel.read_exact(&mut value).await?;
    Ok(value)
}

fn timed_out(_: tokio::time::error::Elapsed) -> Error {
    Error::Io(io::Error::new(
        io::ErrorKind::TimedOut,
        "ordered voter exchange timed out",
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    struct ReplyBytes(Vec<u8>);

    impl Connector for ReplyBytes {
        type Stream = tokio::io::DuplexStream;

        async fn connect(&self, _: Fingerprint, _: Uuid) -> Result<Self::Stream, Error> {
            let (client, mut server) = tokio::io::duplex(4096);
            let reply = self.0.clone();
            tokio::spawn(async move {
                check_magic(&mut server).await.unwrap();
                assert_eq!(server.read_u8().await.unwrap(), ACCEPT);
                read_array::<32>(&mut server).await.unwrap();
                read_ballot(&mut server).await.unwrap();
                assert_eq!(server.read_u8().await.unwrap(), 0);
                read_prefix(&mut server, 64).await.unwrap();
                server.write_all(&reply).await.unwrap();
            });
            Ok(client)
        }
    }

    #[tokio::test]
    async fn vote_reader_leaves_trailing_bytes_and_slot_validation_to_its_caller() {
        let group = [1; 32];
        let voter = Uuid::from_u128(1);
        let ballot = Ballot {
            round: 1,
            nonce: Uuid::from_u128(2),
        };
        let prefix = Prefix::from_base(Bytes::from_static(b"compact image"), 64).unwrap();
        for selected in [1, 2] {
            let mut response = Vec::new();
            response_header(&mut response, VOTE, voter, ballot)
                .await
                .unwrap();
            response.write_all(&[2; 32]).await.unwrap();
            response.write_u8(0).await.unwrap();
            response.write_u8(selected).await.unwrap();
            for generation in [1, 2] {
                response.write_u64(generation).await.unwrap();
                response
                    .write_all(&[generation as u8; 32])
                    .await
                    .unwrap();
            }
            response.push(0xff);
            let remote = RemoteVoter {
                connector: ReplyBytes(response),
                group,
                voter,
                max_prefix_bytes: 64,
                deadline: Duration::from_secs(5),
            };
            let vote = remote.accept(group, ballot, &prefix, false).await.unwrap();
            assert_eq!(vote.slots.selected, selected);
            assert_eq!(vote.slots.is_mirrored(), selected == 1);
        }
    }
}
