# Node 88: Quotient Rank at Least 13

Import `QiushiGlobalOrbitUnused88`; namespace `QiushiMatmul.GlobalOrbit.Unused`:

```lean
rep088 : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 88))
  (frozenWangTable.lower 88)
```

The concrete theorem is `QiushiMatmul.plane88UnusedGen_lb13`:

```lean
QuotientRankAtLeast (spanCodes [80,8,4,2,1]) 13
```

## Argument

The bounded producer routes the 67 subspaces of this four-dimensional quotient
using the existing explicit extension transports. Its admissible predecessor
pool is exactly nodes 5, 20, 23, 25, whose proved bounds are 9, 12, 12, 12.
Node 24 is not used. Node 20 imports `GlobalOrbit.Unused.node20_bound` directly;
there is no dependency on the registry or its future integration of node 88.

The certificate retains 13 source rows and 12 dead witnesses. At putative
decomposition length 12, those witnesses eliminate 12 nonzero quotient cosets,
leaving three live cosets. Their combined count is at most 3 by the remaining
bound-9 source, whereas the total count is at least 12. The single Farkas leaf
uses multipliers 1 and 1, with final right-hand side -9.

Lean checks all source transports, source strengths, quotient sections, dead
witnesses, Boolean tables and the exact leaf, then applies the existing
`generic_plane_qra`. The public theorem has no predecessor or numerical-table
hypotheses. This is a newly regenerated certificate, not a replay of historical
backtracking bytes, DRAT, or a proof that the entire frozen table is rank-sound.

## Reproduce

From `formalization`, supply the 496-basis JSON array, the shared masked
transition JSONL and a fresh private staging path:

```sh
python tools/global_orbit_unused_certificate.py \
  --bases "$BASES" --transitions "$TRANSITIONS" \
  --registry certificates/global-unused88/closed-predecessors.json \
  --node 88 --bound 13 --output "$STAGING/search.json" --emit "$STAGING/emitted"
python -B certificates/global-unused88/test_certificate88.py
python tools/build_global_orbits.py --environment "$ENVIRONMENT" --jobs 2 \
  QiushiGlobalOrbitUnused88*.lean
```

The environment must include the already compiled core, frozen data and
`QiushiGlobalOrbitUnused20`. Do not rebuild or modify a shared output directory
concurrently. The private implementation build calls the existing helper's
`build` function with a separate root/output and an explicit pinned environment.
`--helpers FORMALIZATION` selects an external read-only copy of the producer
and test helpers for the data tests; default is this checkout.

`closed-predecessors.json` fixes the admissible source declarations.
`tables.json`, `branch.json`, `sources.json`, `source-modules.json`, and
`transport-witnesses.json` are generated inputs. The data tests replay all
explicit matrix transports and exact leaf arithmetic, reject a corrupt
multiplier, and compare all 51 emitted Lean files byte-for-byte. Lean's final
tests check both theorem types and audit their transitive axioms.

## Verification

All 53 Lean modules compiled with Lean 4.33.1, at most two compiler processes
and one thread per process. Both final declarations have exactly the axioms
`propext`, `Classical.choice`, `Quot.sound`. All six node-specific Python tests
passed. `verification.json` binds the current source, object and log hashes,
direct external imports, producer inputs, helpers, toolchain and Mathlib
revision. Full path-bearing build/environment records remain in private output.

For integration, the shared `tests/test_global_orbit_unused_certificate.py`
packaged-node dictionary must also allow node 88 with basis `[80,8,4,2,1]`,
target 12 and predecessors `{5,20,23,25}`. That shared file is not changed by
this node-specific package.
