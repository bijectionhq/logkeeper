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
The stream's authorized quorum signs heads at committed apply batch boundaries, with every signature covering the same head timestamp.
One apply batch can extend the tree by many leaves, and any later head for the same stream can prove inclusion in that batch.
Voters check the exact prefix identified by the head against their applied committed state and the authorized signing configuration.
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
A joint configuration requires a quorum from each roster when it certifies a statement or head.
Each stream's initial signing authority and subsequent changes are certified by the catalog.
Keeper replacement and signing key rotation advance the signed history before the successor authority can certify heads.
Historical heads remain verifiable with the authority effective for their ranges.
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
The exported data suffices to verify a proof after all the keepers shut down.

An authenticated cut export carries the exact signed head, catalog history and proof material through its last surviving position.
An archive consumer checks that the proof material reconstructs the signed root before restoring the archive.
The restored archive can produce and verify inclusion proofs within the retained prefix without contacting the original stream.
Producing an inclusion proof requires a surviving copy of the corresponding leaf and path data or an export that already contains the proof.

## Upgrade boundary

Creating an authenticated stream requires cluster feature level 14 and a provisioned catalog root.
The catalog finalizes the feature level only once all active keepers support its durable formats and protocol.
An existing catalog establishes its authenticated genesis at finalization, and the signed history covers every subsequent membership and key change.
An authenticated stream starts at position one with a fresh immutable genesis.
Existing mutable and immutable streams retain their original protocol and retention rules.
Migration to an authenticated stream restores a verified application cut under a fresh stream identity.
The cut's legacy provenance is preserved because earlier quorum durability times, trimmed records and unsigned membership changes cannot be reconstructed.
Keepers below the finalized level use the legacy protocol and durable formats.
