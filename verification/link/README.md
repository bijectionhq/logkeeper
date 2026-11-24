# Mechanical correspondence between Verus and Lean

From the Logkeeper checkout root, run both verifiers.

```sh
tools=/Users/sachaichbiah/code/codesign-agents/tools
python3 verification/verus/run.py --verus "$tools/verus"
python3 verification/link/run.py
```

The Verus runner checks the shipped functions and their production mutation
controls. The link runner checks the reference side of that evidence. It uses
the Lean package's pinned toolchain via `~/.elan/bin/lake`. Pass `--lake PATH`
to select another Lake executable or `--emit` to inspect the generated Lean
definitions.

## Coverage and maintenance

The [inventory](inventory.md) lists each harness declaration, its named Lean
counterpart where applicable, and which part of the correspondence is
mechanical. [specs.json](specs.json) names the Rust source definitions used to
generate `Logkeeper.Generated.Verus`. It also lists the helper definitions
that those specs call. The runner builds
[Equivalences.lean](Equivalences.lean) against the generated module in a
temporary copy of the Lean package.

Each linked spec requires an equivalence theorem whose statement mentions
the actual generated definition and the named reference definition. The
Lean kernel checks the theorem and the runner audits its transitive axioms
against `propext`, `Classical.choice`, and `Quot.sound`. When adding or renaming
a declaration, update the inventory. To add an equivalence, also add the
source spec and Lean name to the manifest and prove `link_<spec name>` in the
area's namespace. Unsupported syntax inside a selected spec fails generation
with its source path and line. The inventory records unsupported syntax and
projection gaps for the remaining claims.

## Representations

- Mathematical `int` and `nat` map to `Int` and `Nat`. An unsigned value
  carried as `Nat` comes from the interval `[0, 2^bits)`. The lease and
  rotation theorems use the exact `u64` maximum. Ballot order and image
  dominance use explicit nonce bounds for the lexicographic rank. Trim credit
  uses ordered byte endpoints so the cast to `nat` has a nonnegative operand.
  The `usize` width for this harness is 64 bits. Finite unsigned casts retain
  truncation. [Verus cast semantics](https://verus-lang.github.io/verus/guide/reference-as.html)
- Bytes use `UInt8`, including when carried by a list. The voter codec
  references use `BitVec 8` and the equivalences convert between them.
  Array width and slice extent come from the applicable Rust type or proof
  domain. Predicates use `Prop`, with `Bool` for stored flags and theorems
  equating Boolean references to `true` where necessary.
- `Seq` is a list, `Map` is an option-valued function, and `Set` and `ISet`
  are predicates. Linked index operations at an unspecified value remain
  opaque. The indexed membership and pairwise lemmas prove that the explicit
  bounds suffice. Map-value and hold-set correspondences use membership views.
- [mappings.py](mappings.py) and [Bridge.lean](Bridge.lean) give the concrete
  field and variant projections. In particular, a cut carries both its next
  LSN and digest, a receipt row carries the original outcome, and the compact
  image uses the Lean reducer image with its key lists embedded in `Int`.
  A rank image keeps an accepted ballot and history length. For the vote
  guard, `AtFence` checks the coordinates attested by the vote under its
  read-back flag. The physical-read proof supplies the connection to disk.

The translator and its representation mappings are part of the trusted
bridge. The Lean audit covers the emitted definitions and the stated
equivalences. Predicate links in the inventory use the existing Verus proofs
for executable obligations, including opaque foreign contracts and native
state projections wherever those are premises. The open rows delimit the
remaining compositional work.

## Mutation controls

[controls.json](controls.json) contains one comparison flip and one omitted
conjunct on the Verus side, plus a changed definition on the Lean side. Each
mutation must still build the generated module and its dependencies. The
runner then requires a Lean proof error inside the named equivalence and
rejects unrelated failures. It applies each mutation in memory or in the
temporary Lean package and leaves the checkout unchanged.

## Stream journal

The generator extracts the single result postcondition from the shipped Verus
contracts in `src/stream/keeper/rules.rs` and `src/stream/writer/decision.rs`.
The Verus runner checks those contracts against their executable bodies.
Thirteen Lean theorems link the generated definitions to Study 119. The
epoch projection reserves model epoch zero for the initial empty vote.
The acknowledgement link assumes the three slots project the observed durable
prefix witnesses, and the keeper retry link covers the model's single-record
case. Seven stream controls change the Verus postconditions or Lean model
definitions and must fail at their named equivalence.

Study 119's Lean ensemble is fixed and its Sync step preserves head and floor.
The keeper replacement and Sync head transfer predicates are generated for
inspection. The inventory records their remaining correspondence.
