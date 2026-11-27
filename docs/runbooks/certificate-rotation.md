# Certificate rotation

Keepers read their certificates only at startup, so every rotation is a
rolling restart (TLS reload without restart is T12, not built). Peers
authenticate each other by CA and URI SAN, not by certificate bytes. A keeper
also checks its own certificate against `certificate_sha256` in its
provision file at every start.

## Keeper certificate (same UUID)

For each keeper, one at a time:

1. Issue a new leaf from the same CA, with the same URI SAN
   `urn:logkeeper:keeper:<uuid>` and both serverAuth and clientAuth.
2. Wait until it is safe to stop (`probe safe-to-stop`, as in [rolling
   upgrade](rolling-upgrade.md) step 5), then stop the keeper.
3. Replace the files at the configured `tls.certificate` and
   `tls.private_key` paths, and rewrite the digest:

   ```sh
   sudo install -o logkeeper -m 0400 new.pem /etc/logkeeper/tls/keeper.pem
   sudo install -o logkeeper -m 0400 new.key /etc/logkeeper/tls/keeper.key
   digest=$(shasum -a 256 /etc/logkeeper/tls/keeper.pem | cut -d' ' -f1)
   reg=/var/lib/logkeeper/registry/$(jq -r .keeper $CONFIG).provision.json
   jq --arg d "$digest" '.certificate_sha256 = $d' "$reg" | sudo -u logkeeper tee "$reg.new" >/dev/null
   sudo -u logkeeper mv "$reg.new" "$reg"
   ```

4. Start it and wait for `probe ready` to return 200.

If the digest does not match, the keeper refuses to start with "keeper does
not match its enrollment authorization". Fix the provision file. Do not
re-initialize.

On Kubernetes: update `keeper-N.pem` and `keeper-N.key` in the
`logkeeper-tls` Secret and `certificate_sha256` in
`keepers/keeper-N.provision.json`, then apply. The generated ConfigMap name
changes, which rolls the StatefulSet one pod at a time.

## Client certificates (RTDB, operators)

- **Same principal URI:** issue the new certificate, update the RTDB node's
  `RTDB_JOURNAL_{slot}_CERTIFICATE`, `_PRIVATE_KEY` and `_CA_CERTIFICATE`
  (PEM contents), and restart the RTDB nodes one at a time. Keepers need no
  change.
- **New principal URI:** first add the URI to the right roles (`writers` and
  `administrators` for RTDB) in every keeper config, and restart the keepers
  one at a time. Then switch the clients, and finally remove the old URI with
  another rolling restart.
- **Emergency removal:** remove the URI from every keeper's roles and restart
  the keepers. There is no revocation check and no live session termination
  without a restart.

## CA rotation

`tls.ca` may hold several PEM roots, and all of them are trusted. Rotate in
three rolling passes. Each pass covers every keeper (rolling restart) and
every RTDB node:

1. **Trust both:** set `ca` to a bundle of the old and new roots.
2. **Reissue leaves** from the new CA (keepers as above, with new digests;
   then clients).
3. **Drop the old root** from every bundle.

**Abort** if any keeper fails to become ready after a pass: `peer.unreachable`
refusals mean that a peer does not trust the new chain. Roll that pass back
before continuing.
