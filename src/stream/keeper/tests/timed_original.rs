use journal_contract::{Journal, JournalError};
use ring::signature::{ED25519, Ed25519KeyPair, KeyPair, UnparsedPublicKey};
use sha2::{Digest, Sha256};

use crate::stream::{
    timed::{
        TimedEvidence, TimedOrigin, TimedOriginal, TimedOriginalClock, TimedOriginalVerifier,
        TimedSample,
    },
    writer::Writer,
};

use super::*;

const CERTIFICATE: [u8; 32] = [7; 32];
const SAMPLE_UPPER_MICROS: i64 = 100;

struct KeeperKeys(HashMap<KeeperId, [u8; 32]>);

impl TimedOriginalVerifier for KeeperKeys {
    fn verify(&self, keeper: KeeperId, statement: &[u8], signature: &[u8; 64]) -> bool {
        self.0.get(&keeper).is_some_and(|key| {
            UnparsedPublicKey::new(&ED25519, key)
                .verify(statement, signature)
                .is_ok()
        })
    }
}

struct Clock(Ed25519KeyPair);

impl TimedOriginalClock for Clock {
    fn authorize(&self, original: &TimedOriginal) -> bool {
        original.stream == A && original.original_receiver_certificate_sha256 == CERTIFICATE
    }

    fn sync_upper_micros(&self, _: &TimedOriginal) -> Option<i64> {
        Some(SAMPLE_UPPER_MICROS)
    }

    fn sign(&self, statement: &[u8]) -> Option<[u8; 64]> {
        self.0.sign(statement).as_ref().try_into().ok()
    }
}

struct LoseProofReplies(Arc<Local>);

impl Transport for LoseProofReplies {
    fn identity(&self) -> &Identity {
        self.0.identity()
    }

    fn call(&self, keeper: KeeperId, request: Request) -> BoxFuture<'_, CallResult> {
        if matches!(&request, Request::ProveOriginal { .. }) {
            return Box::pin(async { Err(TransportError::Unreachable) });
        }
        self.0.call(keeper, request)
    }
}

fn original(epoch: Epoch, at: Lsn, payload: &[u8], cutoff: i64) -> TimedOriginal {
    TimedOriginal {
        stream: A,
        epoch,
        at,
        payload_sha256: Sha256::digest(payload).into(),
        exclusive_journal_cutoff_micros: cutoff,
        original_receiver_certificate_sha256: CERTIFICATE,
    }
}

async fn wait_for_original_keepers(live: &Local, epoch: Epoch) {
    tokio::time::timeout(Duration::from_secs(5), async {
        loop {
            let mut ready = true;
            for keeper in &MEMBERS[..2] {
                ready &= matches!(live.call(*keeper, check(A)).await, Ok(Reply::Checked(view)) if view.synced == Some(epoch));
            }
            if ready {
                return;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .expect("the original write quorum did not sync");
}

#[test]
fn packed_plain_recovery_stops_before_the_timed_original() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"first", b"second"], 2));
    let payload = Bytes::from_static(b"timed");
    let evidence = Arc::new(TimedEvidence {
        origin: TimedOrigin {
            original: original(Epoch(1), Lsn(3), &payload, SAMPLE_UPPER_MICROS + 1),
            ensemble: MEMBERS,
            proposal: 1,
        },
        samples: [TimedSample {
            upper_micros: SAMPLE_UPPER_MICROS,
            signature: [0; 64],
        }; 2],
    });
    // Apply an admitted entry directly to exercise the checkpoint/page transition.
    test.engine
        .streams
        .get_mut(&A)
        .unwrap()
        .apply(
            MEMBERS[0],
            Request::AppendOriginal {
                stream: A,
                evidence: evidence.clone(),
                payload: payload.clone(),
                head: Lsn(3),
            },
            None,
        )
        .unwrap();
    test.engine.wal.rotate(&test.engine.streams).unwrap();

    assert_eq!(
        test.send(recover(A, 1, 1)),
        page(1, 3, &[(1, b"first"), (2, b"second")]),
    );
    assert_eq!(
        test.send(recover(A, 1, 3)),
        Reply::OriginalRecord { evidence, payload },
    );
    assert_eq!(
        test.send(read(A, 1)),
        page(1, 3, &[(1, b"first"), (2, b"second"), (3, b"timed")]),
    );
}

#[tokio::test]
async fn timed_original_proof_survives_reply_loss_and_takeover_but_an_equal_cutoff_does_not() {
    let directories = MEMBERS.map(|_| tempdir().unwrap());
    let clocks = [1, 2, 3].map(|seed| {
        Arc::new(Clock(
            Ed25519KeyPair::from_seed_unchecked(&[seed; 32]).unwrap(),
        ))
    });
    let keys = Arc::new(KeeperKeys(
        MEMBERS
            .into_iter()
            .zip(
                clocks
                    .iter()
                    .map(|clock| clock.0.public_key().as_ref().try_into().unwrap()),
            )
            .collect(),
    ));
    let live = Arc::new(Local(
        MEMBERS
            .into_iter()
            .zip(&directories)
            .zip(clocks)
            .map(|((id, directory), clock)| {
                (
                    id,
                    Keeper::open_with_timed_original(
                        directory.path(),
                        id,
                        Limits::default(),
                        Arc::new(Allow),
                        keys.clone(),
                        Some(clock),
                    )
                    .unwrap(),
                )
            })
            .collect(),
    ));
    let writer = |transport: Arc<dyn Transport>| {
        let writer = Writer::new(transport, MEMBERS)
            .unwrap()
            .with_timed_original(keys.clone(), Some(1024));
        writer.bind_ensemble(A, MEMBERS).unwrap();
        writer
    };
    let old = writer(Arc::new(LoseProofReplies(live.clone())));
    old.create(A).await.unwrap();
    assert_eq!(old.seal(A, Epoch(1)).await, Ok(Lsn(0)));
    wait_for_original_keepers(&live, Epoch(1)).await;

    let payload = Bytes::from_static(b"timely original");
    let accepted = original(Epoch(1), Lsn(1), &payload, SAMPLE_UPPER_MICROS + 1);
    assert_eq!(
        old.append_timed_original(accepted, payload).await,
        Err(JournalError::Unavailable)
    );

    let successor = writer(live.clone());
    assert_eq!(successor.head(A).await, Ok(Lsn(1)));
    let proof = successor.prove_timed_original(accepted).await.unwrap();
    assert_eq!(proof.original_quorum_sync_upper_micros, SAMPLE_UPPER_MICROS);
    assert_ne!(proof.verified_evidence_sha256, [0; 32]);
    assert_eq!(successor.seal(A, Epoch(2)).await, Ok(Lsn(1)));
    wait_for_original_keepers(&live, Epoch(2)).await;
    assert_eq!(successor.prove_timed_original(accepted).await, Ok(proof));

    let refused_payload = Bytes::from_static(b"at the cutoff");
    let refused = original(Epoch(2), Lsn(2), &refused_payload, SAMPLE_UPPER_MICROS);
    assert!(
        successor
            .append_timed_original(refused, refused_payload)
            .await
            .is_err()
    );
    let next = writer(live);
    assert_eq!(next.seal(A, Epoch(3)).await, Ok(Lsn(1)));
    assert_eq!(
        next.append(A, Epoch(3), Lsn(2), Bytes::from_static(b"settled slot"))
            .await,
        Ok(Lsn(2))
    );
    assert!(next.prove_timed_original(refused).await.is_err());
    assert_eq!(next.prove_timed_original(accepted).await, Ok(proof));
}
