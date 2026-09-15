# Frozen Rank-17 Certificates: 382, 383

Import `QiushiGlobalOrbitUnused382` or `QiushiGlobalOrbitUnused383`. Each
`QiushiMatmul.GlobalOrbit.Unused.repNNN` unconditionally proves:

```lean
QuotientRankAtLeast (spanCodes (frozenWangTable.basis NNN))
  (frozenWangTable.lower NNN)
```

The concrete declaration is `QiushiMatmul.planeNNNUnusedGen_lb17`.

| Node | Actual basis | Source rows | Dead rows | Live cosets | Leaf RHS |
| --- | --- | ---: | ---: | ---: | ---: |
| 382 | `[262,68,19,10]` | 23 | 19 | 12 | -5 |
| 383 | `[289,68,19,10]` | 28 | 19 | 12 | -14 |

Both proofs are single exact Farkas leaves at putative length 16, without
branch assumptions. Every source bound is closed; node 382 uses the already
closed concrete source-240 theorem. There is no registry import, target
interdependency, or assumed global table soundness.

## Reproduction and Scope

Follow [the 371 batch](../global-unused371/README.md), substituting these node
indices. Discovery inspected 374 quotient superspaces per node. Both use
width-128 checks and have 31 modules including wrapper and tests, 62 total.

```sh
python -B tools/test_global_unused371383.py --node 382 --node 383
python tools/build_global_orbits.py --environment "$ENVIRONMENT" --jobs 2 \
  QiushiGlobalOrbitUnused382*.lean QiushiGlobalOrbitUnused383*.lean
```

`--helpers FORMALIZATION` permits external read-only Python helpers. Tests
replay exact rays, contexts, all transports/containments, complete live/dead
partitions and byte-identical emission, and reject corrupt multipliers/paths.
The existing Lean extraction and transport theorems give the final bounds;
no foundation is duplicated. Historical BTP/DRAT byte reproduction and table
file identity are outside this alternative proof's claim. Per-node
`verification.json` records actual source/object/log/input hashes and axioms
without host paths. Full environment identities remain private. The parent
owns shared test integration and registry updates.

## Verification

All 62 Lean modules passed with at most two compiler processes and one thread
each. The six Python tests passed. Both concrete bounds and both frozen-table
bounds reported exactly `propext`, `Classical.choice`, and `Quot.sound` under
`Lean.collectAxioms`. Each `verification.json` contains the observed statement
types, results, toolchain/Mathlib identity and source/object/log/input hashes;
the path-bearing build environment is retained only in private output.
