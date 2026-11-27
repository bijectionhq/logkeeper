# Certificate rotation

On Unix, send the keeper SIGHUP after updating the certificate, private
key and trusted CA bundle at the configured paths. A successful reload
supplies the new credentials to fresh application, peer and mTLS admin
connections. Established TLS sessions can finish on their existing
credentials. The keeper validates the leaf's URI and the provision digest
before swapping the credentials.

## Keeper certificate (same UUID)

For each keeper, one at a time:

1. Issue a new leaf with URI SAN `urn:logkeeper:keeper:<uuid>` and both
   serverAuth and clientAuth. Ensure peers already trust the new issuer.
2. Stage and rename the files into place, then update the authorization:

   ```sh
   sudo install -o logkeeper -m 0400 new.pem /etc/logkeeper/tls/keeper.pem.next
   sudo install -o logkeeper -m 0400 new.key /etc/logkeeper/tls/keeper.key.next
   sudo mv /etc/logkeeper/tls/keeper.pem.next /etc/logkeeper/tls/keeper.pem
   sudo mv /etc/logkeeper/tls/keeper.key.next /etc/logkeeper/tls/keeper.key
   digest=$(shasum -a 256 /etc/logkeeper/tls/keeper.pem | cut -d' ' -f1)
   reg=/var/lib/logkeeper/registry/$(jq -r .keeper "$CONFIG").provision.json
   jq --arg d "$digest" '.certificate_sha256 = $d' "$reg" | sudo -u logkeeper tee "$reg.new" >/dev/null
   sudo -u logkeeper mv "$reg.new" "$reg"
   sudo systemctl kill --signal=HUP "$UNIT"
   ```

3. Check for `reloaded TLS credentials` in the keeper log. Open a fresh mTLS
   connection with `logkeeper admin status --config operator.json --keeper
   "$KEEPER"`, then check readiness and writes. If the log says `TLS reload
   refused`, the keeper still uses its previous credentials. Correct the
   files and send SIGHUP again.

On Kubernetes, stage a new versioned Secret for that keeper using `tls.crt`,
`tls.key` and `ca.crt`, then update its workload's Secret reference and the
provision digest in its ConfigMap. This keeps the live certificate available
for the safe-to-stop preflight. Apply the staged configuration and use the
[guarded rollover procedure](rolling-upgrade.md#kubernetes) to load the new
files. Verify mTLS before removing the previous Secret.

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
three passes. Reload every keeper in each pass and roll the RTDB nodes
when their client credential mounts change:

1. **Trust both:** set `ca` to a bundle of the old and new roots.
2. **Reissue leaves** from the new CA (keepers as above, with new digests;
   then clients).
3. **Drop the old root** from every bundle.

**Abort** if any keeper fails to become ready after a pass: `peer.unreachable`
refusals mean that a peer does not trust the new chain. Roll that pass back
before continuing.
