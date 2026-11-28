# Writer-driven journal vs. consensus keeper: head-to-head on separate hosts

This file reports one benchmark run of Logkeeper's two `journal_contract::Journal`
implementations on three real keeper hosts and one client host:

- **writer-driven**: the client `Writer` and proposer over plain keepers
  (`logkeeper keeper --config` with a stream `Config`), reached the way RTDB
  reaches it (`TcpTransport::discover` on `logkeeper+tls://a,b,c`);
- **consensus**: `ConsensusJournal` over consensus keepers, one OpenRaft group per
  stream, with a replicated catalog and enforced catalog leases.

Both run through one harness, `verification/measure/head_to_head.rs`
(`head-to-head` example), and through the same `Journal` calls wherever the
contract allows. The numbers come from one pass of each case. The network is
home Wi-Fi with heavy tail jitter, and the hosts ran other people's jobs during
the run. Read the tails as specific to this setup.

@@RESULTS@@
