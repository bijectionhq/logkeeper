# Study 87 · Authorize recovered replies in the journal order

2026-11-23

## Verdict

A fresh read-index round can prove that a preceding close belongs to the required ordered frontier.
It can also observe a live row and then lose a race to a close.
Treating the round alone as permission to begin a new delivery leaves that second race open.

The reference reissue path orders one control frame in the existing installed journal.
At that position the reducer checks the exact original invocation, live permit serial, snapshot basis, and authentic paid delivery proof.
The server searches by the original invocation when the caller lost the permit along with its first response.
Successful authorization returns the original barrier result and changes only the command position.
It consumes no new invocation nonce or logical result slot.
The chosen and applied frame authorizes the scoped reply token.
Completion still checks that token's exact independent physical borrow.

The paid physical proof binds the original operation, permit and basis.
The journal assigns the ordered position in the frame header.
An overtaken frame refuses at the new position.
The same paid operation can be reframed if the exact original row and basis are still live.
An unchanged data frontier provides no substitute for the ordered frame.

## Bounded comparison

[ReplyAdmission.tla](ReplyAdmission.tla) keeps the data frontier fixed while the logical rows, grant state, and command position can advance.
It runs the same histories with the exact ordered rule and faulty alternatives.

| Reference case | Distinct states | Checked result |
| --- | ---: | --- |
| Probe overlaps successful close | 8 | The later delivery refuses the closed row. |
| Fresh probe after an unapplied close | 5 | A lagging local result cannot serve. |
| Slot reused with a new serial | 15 | Old physical identity cannot authorize the replacement. |
| Missing paid protection | 4 | The request refuses. |
| Frame overtaken at its proposed position | 5 | The old frame refuses. |
| Sealed predecessor | 9 | The predecessor cannot authorize a new delivery. |
| Authority loss after admission | 6 | The admitted reply can complete from its exact independent borrow. |
| Prior protection survives deployment retirement | 11 | The retired current journal can reissue the exact existing protected result. |
| Reframe an already paid operation | 7 | Delivery can proceed after another command wins the earlier position. |

The completion, retirement, and reframing scenarios use weak fairness for their valid progression actions.
The other scenarios check safety.
The retired case starts with existing paid protection.

| Negative control | Shortest counterexample |
| --- | --- |
| Treat an overlapping fresh probe as permission | Probe, close, prepare, then authorize against the closed row in four transitions. |
| Match progress by data frontier | Close, take a fresh probe, and authorize from a lagging read table in four transitions. |
| Omit the exact permit serial | Authorize a recycled slot using the old physical identity in five transitions. |
| Omit paid protection | Authorize a reply without its backing in three transitions. |
| Ignore the proposed ordered position | Authorize the overtaken frame in four transitions. |
| Let the sealed predecessor authorize | Authorize a new delivery under the old sealed owner in four transitions. |

## General proofs

[OrderedReplyAdmission.lean](OrderedReplyAdmission.lean) checks thirteen theorems with standard axioms only.

- The server can find the exact live basis by the original invocation when the caller lost its initial permit.
- A successful delivery binds the exact original live result, its permit serial, its basis and a paid proof under the current journal at that ordered position.
- An earlier effective logical close, a recycled slot, an overtaken position and a sealed predecessor each prevent later authorization under the affected request.
- The command advances the ordered position and preserves the read book, nonce floor and writer authority.
- The same paid proof can support a newly framed attempt at the next position while the exact original basis and eligibility still hold. A current retired journal can authorize an earlier result with existing exact protection.
- The true read-index floor on the combined command history covers a preceding quorum choice. The positive path uses an explicit chosen frame to resolve the overlap with close and establish delivery authority.
- A successful authorization carries the full chosen command and exact applied image. A chosen refusal produces no token. The token emits the exact original canonical response using the same still-held borrow without recontacting the old journal.

Lean also rejects weakening the exact permit-serial guard in the shared reducer.
The protected token uses the constructor boundary checked in Study 86.

## Amendments and acceptance programs

[A342–A345](../amendments.md#study-87--2026-11-23) specify the ordered reissue decision, exact protected identity, reuse of paid work across frame attempts, and completion after authority loss.

- P169. Take a fresh quorum probe after a close whose command has yet to reach the endpoint. Refuse the old cached row at the unchanged data frontier. Also refuse when a probe sees the live row and its close wins before the reissue decision.
- P170. Reissue an exact live original read when its permit reply was lost. Reject a recycled permit and a sealed source. A retired current journal can issue the earlier result when its original paid backing still holds.
- P171. Reframe the same paid operation after another command overtakes it. Complete the chosen original result through authorizer loss using its exact independent borrow.

## Residue

The formal journal context carries the authentic installed scope and a quorum proof for the exact full frame.
Deployment integration still needs actual scope authentication, canonical framing, and bounded retention of chosen delivery evidence while an unfinished operation may need it.
The paid-proof rule abstracts an authentic owned physical reservation and original caller authorization.
Preparing physical protection, preventing reuse of a stopped physical identity, and retaining or releasing an unused staged reservation still require the actual provider and accounting refinements.
A retired journal reissues a protected original result under existing backing.
The rule gives no authority to open new provider access after retirement.
This study's reissue path uses the shared journal.
A read-index delivery optimization would need a separate proof that exact custody and logical closure are serialized at its admission boundary.

## Reproduction

Use TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.

~~~sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/87-ordered-reply-admission/run.py
~~~
