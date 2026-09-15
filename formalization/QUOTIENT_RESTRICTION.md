# Quotient / Restriction Equivalence

Import `QiushiQuotientRestriction`. All declarations below are in
`QiushiMatmul.QuotientRestriction`.

For every `W : Submodule F2 Mat3`, `inputAnnihilator W` consists exactly of
matrices `X` satisfying `sum (i,j), A i j * X i j = 0` for every `A` in `W`.
The pairing is `trace (A * X.transpose)`, not `trace (A * X)`.

The module proves the canonical linear equivalence

```lean
quotientEquiv (W : Submodule F2 Mat3) :
  (Mat3 ⧸ W) ≃ₗ[F2] Module.Dual F2 (inputAnnihilator W)
```

Its value at `[A]`, evaluated at `X`, is the coordinate pairing of `A` and `X`
(`quotientEquiv_mk`). It uses Mathlib's dot-product dual equivalence,
annihilator separation, surjectivity of dual restriction, and quotient/kernel
equivalence. There is no assumed nondegeneracy, classification, or dimension fact.

## Decomposition and Rank API

`quotient_identity_iff_restricted_mul W A B C` equates the existing quotient
residual identities for the same coefficient triples with

```lean
∀ X : inputAnnihilator W, ∀ Y : Mat3,
  (X : Mat3) * Y = bilinearAlgorithm A B C X Y
```

`RestrictedDecomp W r` is an intrinsic algorithm for that restricted product:
its left forms are arbitrary elements of `Module.Dual F2 (inputAnnihilator W)`,
its right forms are arbitrary elements of `Module.Dual F2 Mat3`, and its output
coefficients are full `Mat3` matrices. The forms are not assumed to extend.

```lean
nonempty_quotient_iff_restricted (W : Submodule F2 Mat3) (r : Nat) :
  Nonempty (QuotientTensorDecomp W r) ↔ Nonempty (RestrictedDecomp W r)

quotientRankAtLeast_iff_restricted (W : Submodule F2 Mat3) (n : Nat) :
  QuotientRankAtLeast W n ↔ ∀ r : Nat, RestrictedDecomp W r -> n ≤ r
```

`toRestricted` and `toQuotient` preserve the number of summands in both
directions. The latter proves extension using Mathlib and chooses coefficient
representatives; no bijection between redundant coefficient records is claimed.
`rankAtMost_iff_restricted` equates existence of decompositions of length at
most `n`. `quotientRankAtLeast_iff_restricted_mul` exposes the lower-bound
equivalence directly in terms of the arbitrary input forms and product identity.

These statements include `W = ⊥`, `W = ⊤`, and `r = 0`, allow zero summands,
and assume neither a basis nor a strict/proper-subspace condition on `W`.

## Verification

From this worktree's `formalization` directory:

```sh
python3 tools/build_quotient_restriction.py --environment "$BUILD_ENVIRONMENT" \
  --output .local/quotient-restriction
```

`--environment` is required. Supply the `environment.json` emitted by the clean
source-build helper, with fields `lean`, `lean_path`, `objects`,
`source_snapshot`, and `manifest`. The manifest must identify Mathlib's pinned
revision. Compiler, library, object, and snapshot paths come only from this JSON;
relative paths inside it resolve against its containing directory. `lean_path`
uses the platform's path separator and cannot contain empty entries.

`--output` defaults to `.local/quotient-restriction`, relative to the invocation
directory. It must be separate from the input libraries, snapshot, and environment
file. No host paths or package locations are built into the helper.

The builder compiles only the module and `tests/QuotientRestriction.lean`,
sequentially with `lean -j1`. It prepends its private `lib` directory to the
supplied `lean_path`; the clean dependencies must not be shadowed. It writes
neither input sources nor imported objects. An optional positional selection
can build just one of the two source files, but does not emit a public receipt.

Tests pin the exact public types and expanded coordinate identity, test both
endpoint subspaces and a zero-term algorithm, and distinguish the two possible
off-diagonal pairing conventions. A failing Lean command rejects any transitive
axiom outside `{propext, Classical.choice, Quot.sound}` for all 24 public
declarations. The main endpoints also have printed axiom dependencies.

The output's `environment.json` retains the full resolved environment and is
private: do not publish it. After both compilations and the axiom guard succeed,
`receipt.json` records source/object/log hashes, toolchain identity, Mathlib's
revision, exact-type test success, and observed axiom results. It contains no
host paths, raw environment, or package paths. Environment and manifest identities
are retained only as hashes; `manifest_canonical_sha256` hashes sorted, compact
JSON, not the original manifest bytes. A new build removes any previous success
receipt before compiling, so failed or partial builds cannot leave stale success.

The committed `evidence/quotient-restriction/receipt.json` is the public record of
the recorded successful local run, not a claim about another host's independent
rebuild. Its accompanying axiom log contains declaration names and results only.
This addition does not change or prove any frozen-table or calibration claim.
