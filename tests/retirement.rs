use bytes::Bytes;
use logkeeper::{
    JournalEndpoint, LocalListener, PreparedJournal, ServerOptions, StreamConfig,
    close_empty_journal, open_writer, retire_journal_copy,
};
use tokio_util::sync::CancellationToken;

#[tokio::test]
async fn an_identity_bound_retirement_allows_the_same_journal_to_close_permanently() {
    let directory = tempfile::tempdir().unwrap();
    let address = "local://identity-retirement";
    let identity = "8eee87f5-88cc-4b34-b98a-1bd681f4cd26";
    let other_identity = "3e22a08b-4792-4dd6-9cc3-2ec833d4edee";
    let options = || ServerOptions {
        data_dir: directory.path().to_owned(),
        fsync: true,
        cache_bytes: 0,
    };
    let (journal, _) = PreparedJournal::open_for_member(options(), identity.into())
        .await
        .unwrap();
    let stop = CancellationToken::new();
    let worker =
        tokio::spawn(journal.serve_local(LocalListener::bind(address).unwrap(), stop.clone()));
    let config = StreamConfig {
        servers: vec![JournalEndpoint::Member {
            address: address.into(),
            journal: identity.into(),
        }],
        stream: "retirement".into(),
        write_quorum: 1,
        maximum_message_bytes: 1024,
    };
    let writer = open_writer(config.clone(), 1, stop.clone()).await.unwrap();
    writer
        .enqueue(Bytes::from_static(b"record"), 0)
        .await
        .unwrap()
        .durable()
        .await
        .unwrap();

    assert!(close_empty_journal(address, identity).await.is_err());
    assert!(
        retire_journal_copy(address, other_identity, "retirement", 2)
            .await
            .is_err()
    );
    retire_journal_copy(address, identity, "retirement", 2)
        .await
        .unwrap();
    close_empty_journal(address, identity).await.unwrap();
    stop.cancel();
    worker.await.unwrap().unwrap();

    let journal = PreparedJournal::reopen_member(options(), identity.into())
        .await
        .unwrap();
    let stop = CancellationToken::new();
    let worker =
        tokio::spawn(journal.serve_local(LocalListener::bind(address).unwrap(), stop.clone()));
    close_empty_journal(address, identity).await.unwrap();
    assert!(open_writer(config, 3, stop.clone()).await.is_err());
    stop.cancel();
    worker.await.unwrap().unwrap();
}
