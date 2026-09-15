# Node 87: Nine-Source Cover

Import `QiushiGlobalOrbitUnused87`; namespace `QiushiMatmul.GlobalOrbit.Unused`:

```lean
node87_bound : QuotientRankAtLeast (spanCodes [64,8,4,2,1]) 11
rep087 : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 87))
  (frozenWangTable.lower 87)
```

Nine explicit GL/transpose images of the proved orbit-5 rank-nine source all
contain this target subspace and together cover every matrix. The transport,
containment and complete `Fin 512` coverage checks are Lean kernel proofs.
No other unbound representative, including node 24, is used.

The proof reuses `decomp_length_le_cover_capacity` from
`QiushiFrozenRankCover`, without introducing a new foundational theorem.
For a putative decomposition of length `r >= 9`, the cover implies
`r <= 9 * (r - 9)`. This is impossible at `r = 9` or `r = 10`.
For `r < 9`, the existing quotient bound for any source rules it out directly.
The coverage includes the zero fiber, so no dead-witness or preceding-bound
assumption is needed.

## Certificate

The existing bounded `global_orbit_unused_certificate.py` producer inspected
only the 67 subspaces of this four-dimensional quotient, using the shared
explicit extension words. Of the available proved sources, precisely the nine
orbit-5 rows suffice. `cover.json` records their ordered bases, preimages,
extension words, explicit matrices and source declaration, with input hashes.
It is geometry/transport evidence, not a historical backtracking trace or a
claim of global frozen-table soundness.

To reproduce discovery from `formalization`:

```sh
python tools/global_orbit_unused_certificate.py \
  --bases "$BASES" --transitions "$TRANSITIONS" --registry "$CHECKED_REGISTRY" \
  --node 87 --bound 11 --output "$STAGING/search.json"
python -B certificates/rank-cover87/test_cover87.py
python tools/build_global_orbits.py --environment "$ENVIRONMENT" --jobs 2 \
  QiushiGlobalOrbitUnused87.lean QiushiGlobalOrbitUnused87Tests.lean
```

Do not pass `--emit`: the existing dead-witness branch extractor is not the
proof route for this node. Select the returned rows whose `orbit` is 5; their
ordered bases are `sources087`. The environment must include compiled core,
frozen data and `QiushiFrozenRankCover`. Use private output or an otherwise
unoccupied builder output. The Python test accepts `--helpers FORMALIZATION`
to use external read-only producer helpers from a separate checkout.

## Verification

Both Lean modules passed with Lean 4.33.1 and the pinned Mathlib revision.
The five declaration guards allow only `propext`, `Classical.choice`, and
`Quot.sound`; both rank theorems have exactly those three axioms. All five
Python tests passed, including rejection of a corrupted matrix and removal
of any of the nine covering rows. `verification.json` records source, object,
log, direct-import and environment hashes without private paths.
