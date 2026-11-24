# Logkeeper stream journal deployment

The module runs three keepers in the caller's VPC, with one keeper per AZ. The journal lives on EC2 NVMe instance store. Route 53 gives each endpoint a stable private DNS name. Give Bijection only the `journal_url` and its client certificate, private key and CA bundle. Pass the URL unchanged to the journal client.

```text
logkeeper+tls://keeper-1.journal.example.internal:5448,keeper-2.journal.example.internal:5448,keeper-3.journal.example.internal:5448
```

## Build the image

Build the release with Rust's `aarch64-unknown-linux-musl` and `x86_64-unknown-linux-musl` targets, a musl C toolchain for each target, and the approved guarded Cargo entry point. For a cross-build, configure Cargo's linker and the C compiler that builds `ring` for each target. The example assumes the cross-compilers are in `PATH`.

```sh
export GUARDED_CARGO=/path/to/guarded-cargo.py
export CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_LINKER=aarch64-linux-musl-gcc
export CC_aarch64_unknown_linux_musl="$CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_LINKER"
export CARGO_TARGET_X86_64_UNKNOWN_LINUX_MUSL_LINKER=x86_64-linux-musl-gcc
export CC_x86_64_unknown_linux_musl="$CARGO_TARGET_X86_64_UNKNOWN_LINUX_MUSL_LINKER"
deploy/build-binaries.sh
deploy/tests/image.sh
```

The build stages both binaries in `target/keeper-image/`. The test builds and loads the two-platform scratch image locally, checks each executable and runs it. Use a Docker image store with multi-platform support and a Docker host that can run both architectures, using emulation if needed. [Docker multi-platform builds](https://docs.docker.com/build/building/multi-platform/)

After both variants pass, set `RELEASE_IMAGE` to the tagged image in Logkeeper's private ECR repository in the module's region and account, and authenticate Docker to that registry.

```sh
docker buildx build --platform linux/arm64,linux/amd64 \
  -f deploy/Dockerfile -t "$RELEASE_IMAGE" --push target/keeper-image
docker buildx imagetools inspect "$RELEASE_IMAGE"
```

Verify the index lists `linux/arm64` and `linux/amd64`. Use the top-level `Digest` from `imagetools inspect` for `image_digests` so each host can pull its variant. The container runs as UID and GID 10001 with the configuration at `/etc/logkeeper/keeper.json` and journal data at `/var/lib/logkeeper`. The configuration uses the JSON schema in [the stream journal spec](../verification/target-journal.md#formats-shared-by-the-keeper-writer-and-deployment).

## Bootstrap

1. Select three routed private subnets in a DNS-enabled VPC with three distinct AZ IDs. The journal clients and sweeper must resolve the private zone and reach TCP 5448 from the allowed security groups. Provide HTTPS egress to the AL2023 package repositories, ECR and its layer storage, SSM and its session channels, Secrets Manager and AWS Private CA. Use Session Manager for systemd and storage checks. Grant session access only to journal operators.
2. Select a qualified Amazon Linux 2023 AMI with cloud-init and SSM Agent 3.3.40.0 or newer. The default `i8g.large` uses arm64 Graviton4 and has one 468 GB third-generation Nitro NVMe SSD. Its two vCPUs, 16 GiB of memory and disk capacity match the former default's sizing. AWS lists I8g in Stockholm (`eu-north-1`). Confirm the chosen size is offered in all three selected AZs. For an x86_64 deployment, explicitly set a qualified single-NVMe Nitro type such as `i4i.large` and supply a matching x86_64 AMI. The Terraform runner needs `ec2:DescribeImages` to check the AMI architecture. Complete [storage qualification](#qualify-fsync) before admitting production writes. [AWS I8g specifications](https://aws.amazon.com/ec2/instance-types/i8g/) · [AWS I4i specifications](https://aws.amazon.com/ec2/instance-types/i4i/) · [Stockholm availability](https://aws.amazon.com/about-aws/whats-new/2025/11/amazon-ec2-i8g-instances-additional-aws-regions/) · [AWS Session Manager message endpoints](https://docs.aws.amazon.com/systems-manager/latest/userguide/systems-manager-setting-up-messageAPIs.html)
3. Use an active AWS Private CA dedicated to this journal in the module's region. Supply its CA ARN, a matching signing algorithm such as `SHA256WITHRSA` for an RSA CA, and the PEM trust bundle containing its root. If the issuer is subordinate, test the full chain on both TLS peers. The keeper role can issue server-auth leaves and the client issuer role can issue client-auth leaves. Both templates take their SANs from the CSR. Control access to both issuing roles and keep the issuing CA dedicated to this cluster. [AWS Private CA certificate templates](https://docs.aws.amazon.com/privateca/latest/userguide/template-definitions.html)
4. Instantiate the module from a Terraform root. Fix the subnet order at bootstrap. Use the same initial image digest in all three entries and provide the client and writer names and byte limits. List an identity in both sets when it needs reads and mutations. Review the plan before provisioning. An example module call follows.

```hcl
module "logkeeper" {
  source                    = "./deploy/terraform/logkeeper-cluster"
  name                      = "production-journal"
  vpc_id                    = var.vpc_id
  private_subnet_ids        = var.private_subnet_ids
  client_security_group_ids = var.journal_client_security_group_ids
  ami_id                    = var.qualified_arm64_ami_id
  dns_zone_name             = "journal.example.internal"
  image_repository_name     = "logkeeper"
  image_digests             = [var.image_digest, var.image_digest, var.image_digest]
  client_names              = ["rtdb", "sweeper"]
  writer_names              = ["rtdb", "sweeper"]
  pki                       = var.journal_pki
  limits = {
    stream_quota_bytes     = 8589934592
    max_record_bytes       = 33554432
    round_bytes_per_stream = 4194304
    round_requests         = 64
  }
}
```

5. Check `journalctl -u logkeeper.service` on all three keepers. Record each endpoint's keeper UUID, AZ and mount source in the operator inventory. Verify that `findmnt /mnt/logkeeper` reports XFS on the local NVMe device and that the certificate has the endpoint DNS SAN and `urn:logkeeper:keeper:UUID` URI SAN. Verify three distinct authenticated IDs from the client network. Run a disposable stream through create, seal, append, head and read before giving a consumer the production URL.
6. Export the module's `journal_url`, `ca_certificate` and `client_issuance` as root outputs for the operator. Attach the issued `issuer_policy_arn` to a trusted issuance role and use its AWS CLI profile with the script. The operator needs Bash, AWS CLI v2, jq and OpenSSL.

```sh
terraform output -json client_issuance > client-issuance.json
AWS_PROFILE=logkeeper-issuer deploy/issue-client.sh client-issuance.json rtdb ./rtdb-credentials
```

The issuer puts the private key into that client's Secrets Manager secret and hands the same key to the client from the new private output directory. Deliver `certificate.pem`, `private-key.pem` and `ca.pem` through the client's credential channel, then remove the temporary issuer copy. The resource policy restricts secret reads to keeper roles and normal service roles have no grant to retrieve escrowed client keys. The issuer and consumer receive no read grant. To rotate a client, issue into a new directory and switch the consumer before the old certificate expires. For emergency removal, close that identity at every keeper and terminate existing sessions. Treat certificate revocation enforcement as a release gate if operations depend on it.

## Replace a keeper after disk loss

Local NVMe survives an EC2 reboot. EC2 stop, hibernation, termination and disk loss erase or discard it. The service reads the keeper UUID and certificate from the NVMe alongside the WAL. On a blank volume it creates a new UUID and certificate and stores the private key as a new secret version. On a retained volume it selects the exact version by the UUID already on disk. The service starts only after the new on-disk identity has been synced. Keep the identity directory and journal together. [EC2 instance-store persistence](https://docs.aws.amazon.com/AWSEC2/latest/UserGuide/instance-store-lifetime.html)

1. Identify the lost keeper UUID and affected streams. Confirm the two surviving keepers are healthy and suspend other keeper changes.
2. Replace only the failed EC2 instance. In a reviewed Terraform plan, force replacement of `module.logkeeper.aws_instance.keeper["N"]` and include its Route 53 record. Target `module.logkeeper.aws_route53_record.keeper["N"]` when a broader pending change would otherwise touch other instances. Keep the secret container, endpoint name and AZ in place. Verify the replacement's local mount and that its TLS URI presents a new UUID after DNS converges.
3. Give the Logkeeper learner sweeper the old and new keeper IDs and the affected streams. Enroll the replacement as a non-voting learner for each stream. Let its writer or the sweeper sync the stream from the two surviving ensemble members. Require the stream protocol's completed sync and membership transition before counting the learner toward quorum. DNS discovery alone confers no vote on an existing stream.
4. Track the pending, synced and promoted streams to completion. Check that each repaired ensemble contains the new ID and can serve the committed prefix. Keep the survivors in service throughout. A second loss before repair completes requires the journal's recovery procedure. Stop the rollout if any affected stream lacks the surviving quorum. The sweeper's invocation and evidence of promotion depend on the stream-journal release. Validate them end to end before using this procedure in production.

## Scale and upgrade

Use the three endpoint slots in their original order. Add capacity by provisioning a separate three-keeper cluster and assigning new streams to its journal URL, or qualify a larger single-NVMe type and replace one keeper at a time. Use the learner procedure for each instance-type, AMI or subnet replacement. Relocating a live stream to another cluster requires a stream migration procedure.

For an existing x86_64 cluster that relied on the previous default, set `instance_type = "i4i.large"` before planning with this module. To migrate to Graviton, first stage the multi-platform image on the running cluster. After qualifying Graviton, change `instance_type` and `ami_id` together and replace one keeper at a time through the learner procedure. Confirm stream repair before replacing the next keeper.

For a software upgrade, change one `image_digests` entry, review that Terraform updates only that endpoint's SSM image parameter, and restart `logkeeper.service` on the selected host. Keep the EC2 instance running. Verify that the UUID is unchanged, the expected digest is running, the journal replays and the keeper serves its existing ensembles. Check sync latency, the stream canary and errors before changing the next entry. Restore the previous digest and restart the same service for rollback if the WAL format remains compatible.

Changes to bootstrap data, including the allowlists and limits, replace the affected EC2 instances. Stage them by targeting a single DNS record and its instance per operation, using the learner procedure between operations. Review the plan for exactly one instance replacement before proceeding. For certificate renewal, restart each healthy keeper in turn during the last 30 days of its 90-day certificate and verify that the UUID is unchanged and the new expiry has advanced. Retain the old image digest until the rollout passes.

## Monitor

Collect the keeper's release-specific telemetry and service logs. Qualify the following signals in a disposable cluster before wiring production alerts.

| Signal | Check |
| --- | --- |
| Durable sync latency | Track p50, p95 and p99 per keeper and AZ from the WAL group-commit sync through completion. Alert on deviations from the qualified baseline and on sync errors. |
| Round size | Track bytes, records and streams per WAL sync round along with per-stream bytes. Investigate sustained round-cap saturation or an increasing queue. |
| `Full` refusals | Count by stream on the writer, alert on sustained refusals, and check the reported floor and the consumer's trim progress. |
| NVMe and keeper health | Track available journal space, filesystem and device errors, restarts, certificate expiry and mTLS failures. |
| Replacement progress | Track learner backlog and time to promotion. Page if only one member of any ensemble is usable or if a stream stops progressing with two survivors. |

## Qualify fsync

Before a production rollout, qualify the default `i8g.large` on arm64 and every alternative instance type you intend to operate. Record the CPU architecture, instance type and AZ, NVMe model and firmware, AMI and kernel, XFS mount options, and the release index and platform manifest digests. Verify that `findmnt --mountpoint /mnt/logkeeper` shows XFS and that the source is the single `Amazon EC2 NVMe Instance Storage` device reported by `lsblk`. Keep normal filesystem flush semantics and verify that the keeper replies only after the covering sync succeeds. Measure the sync latency distribution at expected load, including segment rotation, reclaim and near-capacity conditions.

Run a crash-and-recovery test with an independent observer that durably records each acknowledged append. Exercise process kill, abrupt host reset on the same disk, and torn writes around record and segment boundaries. After every recovery reconcile acknowledged records, their bytes and the reported floor with the observer. A graceful shutdown or a throughput benchmark cannot qualify power-loss behavior. Use AWS's documented persistence behavior as part of the evidence and obtain a failure-injection test or platform evidence covering device flush and abrupt power loss. Record any untested condition with the qualification result.

As a negative control, run the same fault and recovery check on each stack with a keeper test build that replies before sync. Inject a fault after an acknowledgement and before persistence and require the acknowledged-record reconciliation to fail. Test whole-disk loss separately with the learner procedure, including refusal to count the new UUID before sync. Retain fault settings, the acknowledgement trace, recovery results and the failing control with the qualification record. [EC2 NVMe instance store](https://docs.aws.amazon.com/AWSEC2/latest/UserGuide/ssd-instance-store.html)
