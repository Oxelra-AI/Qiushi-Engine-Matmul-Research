# General Matrix Saturation

`QiushiGeneralSaturation.lean` closes the arbitrary-field, arbitrary-dimension
matrix bridge for the report's rank-additive decomposition lemma (English
`main.tex`, Lemma `lem:saturation`). It imports `QiushiSaturationShared` and
reuses `orthogonal_idempotents`, Mathlib matrix rank, unit-determinant rank
preservation, and the actual matrix nonsingular inverse.

In namespace `QiushiMatmul.GeneralSaturation`, with independent types
`k n i`, a field `k`, and finite decidable index types `n` and `i`:

```lean
rank_additive_saturation
  (P : Matrix n n k) (M : i -> Matrix n n k)
  (hP : IsUnit P.det) (hsum : ∑ t, M t = P)
  (hrank : ∑ t, (M t).rank = P.rank) :
  ∀ t s, M t * P⁻¹ * M s = if t = s then M t else 0
```

`IsUnit P.det` is equivalent to matrix invertibility, including dimension
zero. `rank_additive_saturation_of_rank_sum_card` accepts the rank sum as
`Fintype.card n` instead. `normalized_products` proves both the normalized
sum and pairwise products. `complete_orthogonal_idempotents` proves, for
`E t = M t * P⁻¹`, all three report conclusions: `E t * E t = E t`,
`E t * E s = 0` for distinct indices, and the sum of the `E t` is `1`.

No nonempty index, positive dimension, nonzero summand, characteristic,
permutation, symmetry, or involution assumption is imposed. The test proves
the zero-dimensional case for arbitrary finite families; an empty family
with invertible sum forces dimension zero. It also instantiates both empty
indices, a zero-padded family, and the non-involutory rational matrix `[2]`.

## Verification

Pinned Lean 4.33.1; Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`. Read-only imports came from the
parent's `build-20260914-125249/environment.json`. Both files compile with
warnings treated as errors, using one Lean process at a time. The test
prints the exact types and transitive axiom sets of all four API theorems
and four named regression theorems, and enforces an axiom whitelist.
All eight depend on exactly `propext`, `Classical.choice`, and `Quot.sound`.
No additional axioms or unchecked proof evaluation are used.

From `formalization`, with `ENVIRONMENT` pointing to that read-only manifest:

```sh
python3 tools/build_cnf_semantics.py --environment "$ENVIRONMENT" \
  --output .local/general-saturation-clean \
  QiushiGeneralSaturation tests/GeneralSaturation
```

Exact compiler type/axiom output is written to
`.local/general-saturation-clean/logs/tests_GeneralSaturation.log`;
adjacent JSON records contain source/object hashes and the build command.
Only this note, the new module, and its test are committed. Parent sources,
research programs, reports, existing main-theorem closure, and certificates
are unchanged by this work. This bridge makes no CNF-byte or DRAT claim.
