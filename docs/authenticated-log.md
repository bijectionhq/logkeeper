# Authenticated streams

Logkeeper publishes verifiable facts about the records committed to its authenticated streams.
An application can select which committed stream segments survive in its own lineage.
Inclusion in a Logkeeper head certifies a commit and its durability bound.

## Leaves and heads

Each committed record in an authenticated stream contributes one leaf, including checkpoint announcements.
The leaf binds the stream, position, writer epoch, SHA-256 payload digest and a conservative upper bound on the time the exact record bytes reached a durable write quorum.
A timed leaf also binds its exclusive cutoff and receiver certificate digest.
An exact retry leaves the original leaf and durability bound intact.
Leaves are added on successful apply in position order, one leaf per position starting at one.
The committed state preserves each leaf's metadata so replay and failover derive the same tree.

Leaves use SHA-256 with distinct domains for leaf and inner node hashing.
The head identifies the catalog, stream, leaf count, tree root, catalog history revision and head timestamp.
The stream leader certifies its applied prefix when the prefix grows and when a reader asks for it, with every signature covering the same head timestamp.
One head can cover many leaves, and any later head for the same stream can prove inclusion in an earlier prefix.
A certified head serves until its roster is replaced, so an idle stream costs no signing or catalog traffic.
Voters check the exact prefix identified by the head against their applied committed state and the authorized signing configuration.
Each voter also checks the head timestamp against its own clock, within twice the configured clock error and the request timeout.
Leader transfer preserves the prefix and requires no change to its signing authority.

## Timeliness

A timed append uses a receiver certificate scoped to the source stream and its guarded journal clock.
Each durability sample binds the exact staged bytes to the stream, position, writer epoch, cutoff, receiver certificate and applicable quorum.
The timed leaf uses the largest conservative post-sync bound among the members of a verified write quorum.
Every such bound must precede the exclusive cutoff for the command to admit the timed append.
Applying a timely append can occur after its cutoff because the quorum already held the exact bytes before the cutoff.
Inclusion of a timed leaf therefore proves both that its bytes reached quorum before its cutoff and that the append committed.

## Catalog history

The verifier pins the catalog root and verifies the signed history of authorized configurations and keys from that root.
The root is the digest of the canonical genesis statement binding the catalog identity and initial catalog signing authority.
Each subsequent statement binds its predecessor, its revision and the catalog or stream membership and keys it authorizes for its effective range.
The preceding catalog authority signs each change.
A joint configuration requires a quorum from each roster when it certifies a head.
A catalog membership change is certified as a joint roster when it is staged.
A change out of a joint catalog roster is signed by a quorum of the side it keeps, so the target settles a completed move and the origin settles an abandoned or retargeted one.
Each stream's initial signing authority and subsequent changes are certified by the catalog.
Keeper replacement and signing key rotation advance the signed history before the successor authority can certify heads.
A head verifies only while its roster is current in the history presented with it.
A roster replaced later in that history signs nothing, so retired keys cannot certify a head.
A consistency proof to a current head carries an earlier head across a replacement.
Each signature counts for one distinct authorized voter and is bound to its statement and signing domain.

## Proofs outlive trim

Trim and checkpoint replacement can remove payloads once their ordinary retention conditions hold.
Leaf descriptions and Merkle proof material have independent retention and remain available after the payloads are gone.
Snapshot replacement and keeper replacement transfer the authentication state needed to extend the tree and prove earlier leaves.
Retirement archives that state and its signed heads and catalog history before removing the stream's proof-serving replicas.
The proof archive contains the data needed to open leaves at individual positions, with no dependency on the application payload store.

## Recovery cuts

Lossless writer replacement keeps the authenticated prefix and advances the writer epoch.
An authenticated stream has immutable genesis, so a recovery that accepts a lost suffix restores into a fresh stream identity.
The successor tree begins with its own committed records, including the records that install the recovered application state.
The exported predecessor tree keeps its original stream identity and positions.
The original stream's tree is append-only, including when an application selects an earlier head as its surviving cut.
An inclusion proof identifies the stream and position.
A consistency proof shows prefix extension between two heads of the same stream.
The application authority publishes the last surviving position and the successor stream in its own authenticated stream when it advances its lineage.

## Export and verification

Export an inclusion proof by stream and position.
The export contains the leaf, its inclusion path, its signed head and the catalog history needed to verify that head.
Export a consistency proof with both signed heads, the consistency path and the catalog history needed for both heads.
The verifier checks the signed history, quorum identities, signed head and the applicable Merkle path against the pinned catalog root.
A client pins the root through the journal configuration's `catalog_root`, and refuses authenticated history without one.
The exported data suffices to verify a proof after all the keepers shut down.

An authenticated cut export carries the exact signed head, catalog history and proof material through its last surviving position.
An archive consumer checks that the proof material reconstructs the signed root before restoring the archive.
The restored archive can produce and verify inclusion proofs within the retained prefix without contacting the original stream.
Producing an inclusion proof requires a surviving copy of the corresponding leaf and path data or an export that already contains the proof.
The shared proof mount retains the content-addressed catalog history pages referenced by catalog compaction so every keeper can reopen and verify the signed chain.
Use a distinct retained directory for each catalog.

## Upgrade boundary

Creating an authenticated stream requires cluster feature level 14 and a provisioned catalog root.
The catalog finalizes the feature level only once all active keepers support its durable formats and protocol.
An existing catalog establishes its authenticated genesis at finalization, and the signed history covers every subsequent membership and key change.
An authenticated stream starts at position one with a fresh immutable genesis.
Existing mutable and immutable streams retain their original protocol and retention rules.
Migration to an authenticated stream restores a verified application cut under a fresh stream identity.
The cut's legacy provenance is preserved because earlier quorum durability times, trimmed records and unsigned membership changes cannot be reconstructed.
Keepers below the finalized level use the legacy protocol and durable formats.

## Keeper provisioning

Mount an independent Ed25519 PKCS#8 signing key for every authenticated keeper using the keeper configuration's `authenticated_log.signer_pkcs8_file`.
Keep that file readable only by the daemon and its designated group.
Configure every keeper with the same independently retained filesystem mount for `authenticated_log.archive_directory`, outside all keeper data directories.
The mount must provide durable file and directory sync plus atomic hard-link creation.
Keep the mount available to current and replacement keepers and retain its contents through stream and keeper retirement.
Before deleting an authenticated stream, the leader saves its exact certified tree there, in a directory for its catalog, and the stream checks that the archived head still matches its last applied head.
Retrying an interrupted retirement reuses a verified archive at the same head.

Set `authenticated_log.maximum_clock_error_micros` to an operating bound on the keeper's synchronized UTC clock error.
Ordinary batches bind the maximum conservative clock bound from the voters that synced the exact operation before it entered Raft.
A keeper reserves temporary capacity per stream and stages each exact operation under its content digest, so a refused operation leaves the position open to different bytes.
An exact retry reuses its original staged bound while that stage is retained.
An ordinary write quorum must have overlapping retention intervals that cover the selected upper bound.
Keepers reclaim stages that are fenced, superseded by committed positions, or past their promised retention.
Timed batches keep the guarded receiver-clock admission path and record its quorum bound in the tree.
Current authenticated streams export inclusion proofs, while pre-feature immutable streams retain their level 13 attestation protocol.
Provision the catalog voters and stream voters before creating authenticated streams.
Finalize level 14 on the replicated catalog and pin the root through an independent trusted channel.
The root is the digest of the genesis authority over the catalog voters' provisioned signing keys, so an operator computes it from those keys rather than reading it from a keeper.
A catalog whose format level was finalized without signing mounts can establish its authenticated root by finalizing level 14 again after provisioning.
Rotate a keeper key by installing a new signer and restarting one keeper at a time while preserving a quorum of the preceding catalog authority.
The catalog certifies the new key before it can contribute to a new head.
