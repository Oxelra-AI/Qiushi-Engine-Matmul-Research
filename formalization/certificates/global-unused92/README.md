# Node 92: Quotient Rank at Least 13

Import `QiushiGlobalOrbitUnused92`; namespace `QiushiMatmul.GlobalOrbit.Unused`:

```lean
rep092 : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 92))
  (frozenWangTable.lower 92)
```

The concrete theorem `QiushiMatmul.plane92UnusedGen_lb13` has type:

```lean
QuotientRankAtLeast (spanCodes [160,80,4,2,1]) 13
```

## Argument

The existing bounded producer routes the 67 subspaces of the four-dimensional
quotient using the shared extension words. Only proved predecessors 8, 9, 25
are admitted, at bounds 9, 9, 12. Nodes 24, 27, 28 are not used. There are no
imports from `FrozenRegistry` and no dependency on node 87 or node 88.

At a putative decomposition length 12, six dead witnesses eliminate six
nonzero quotient cosets. Nine live cosets remain. The selected certificate has
11 source rows and one Farkas leaf: five occupation rows with multipliers
`1,1,2,1,1`, plus the total row with multiplier 2, give right-hand side -6.
The source transports, section/dead/source tables, exact arithmetic and final
`generic_plane_qra` invocation are checked by Lean. No unproved table labels
or predecessor bounds are hypotheses of the exported theorem.

This is an alternative finite proof, not a historical backtracking-byte/DRAT
replay or a proof of rank soundness for the entire frozen table.

## Reproduce

From `formalization`, supply the 496-basis JSON, existing masked transition
JSONL, clean import environment and a new private staging path:

```sh
python tools/global_orbit_unused_certificate.py \
  --bases "$BASES" --transitions "$TRANSITIONS" \
  --registry certificates/global-unused92/closed-predecessors.json \
  --node 92 --bound 13 --output "$STAGING/search.json" --emit "$STAGING/emitted"
python -B certificates/global-unused92/test_certificate92.py
python tools/build_global_orbits.py --environment "$ENVIRONMENT" --jobs 2 \
  QiushiGlobalOrbitUnused92*.lean
```

The Python test also accepts `--helpers FORMALIZATION` for external read-only
producer helpers. It checks the closed source pool, all explicit transports,
dead bounds, exact leaf arithmetic, rejection of a corrupt multiplier, and
byte-identical regeneration of all 51 generated Lean files. The two additional
Lean modules export and test the frozen-table interface and collect transitive
axioms for both final declarations.

Use private output or an otherwise unoccupied builder output. Full environment
paths remain private; public verification records bind hashes and toolchain
identity. The shared packaged-certificate test dictionary must include node 92
with basis `[160,80,4,2,1]`, target 12 and predecessors `{8,9,25}`; that shared
test is outside this package's edits.

## Verification

All 53 Lean modules and five Python tests passed. Both final declarations
have exactly `propext`, `Classical.choice`, `Quot.sound` as their transitive
axioms. The build used Lean 4.33.1, pinned Mathlib, no more than two compiler
processes and one thread per process. `verification.json` binds the current
source, object, log, helper, producer-input and external-import hashes;
path-bearing environment and full build receipts remain private.
