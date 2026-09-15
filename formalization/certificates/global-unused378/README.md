# Frozen Rank-17 Certificates: 378, 379, 380

Import `QiushiGlobalOrbitUnusedNNN` for the corresponding unconditional
`QiushiMatmul.GlobalOrbit.Unused.repNNN`:

```lean
QuotientRankAtLeast (spanCodes (frozenWangTable.basis NNN))
  (frozenWangTable.lower NNN)
```

The concrete declaration is `QiushiMatmul.planeNNNUnusedGen_lb17`.

| Node | Actual basis | Source rows | Dead rows | Live cosets | Leaf RHS |
| --- | --- | ---: | ---: | ---: | ---: |
| 378 | `[162,68,19,10]` | 17 | 16 | 15 | -3 |
| 379 | `[164,68,19,10]` | 22 | 15 | 16 | -4 |
| 380 | `[258,68,19,10]` | 26 | 21 | 10 | -6 |

Each has a single exact Farkas contradiction at putative length 16, with no
branch assumptions. Every source bound is an existing closed theorem; the
targets are independent. Source declarations, strengths, bases and explicit
matrix transports are listed in each package's JSON files. There are no
`FrozenRegistry` imports or global table soundness assumptions.

## Reproduction

The same bounded producer and width-128 deterministic generation described
in [the 371 batch](../global-unused371/README.md) apply, with these node indices.
Each discovery inspected 374 quotient superspaces. The 29, 31 and 31 Lean
modules respectively total 91, including wrappers and tests.

```sh
python -B tools/test_global_unused371383.py --node 378 --node 379 --node 380
python tools/build_global_orbits.py --environment "$ENVIRONMENT" --jobs 2 \
  QiushiGlobalOrbitUnused378*.lean QiushiGlobalOrbitUnused379*.lean \
  QiushiGlobalOrbitUnused380*.lean
```

The Python tests also accept `--helpers FORMALIZATION`. They verify exact rays,
all branch contexts, explicit transports, containment, complete live/dead
partitions, closed predecessors, corrupt-input rejection and byte-identical
regeneration from the committed certificate inputs.

For 379 only, the producer's source-203 registry adapter is replaced by its
underlying theorem `QiushiMatmul.plane203UnusedGen_lb16`, imported directly from
`QiushiGlobalOrbitUnused203Final`. `generation.json` records both source
descriptors. This retains the same basis, rank, transports and integer ray;
it removes an unnecessary aggregate registry dependency. Apply this recorded
descriptor substitution to the source row, source ledger and selected-source
record before deterministic emission. No parent registry source is changed.

Lean checks the finite predicates and exact arithmetic and applies the
existing extraction theorem. The proof neither replays historical BTP/DRAT
bytes nor identifies a historical table file. Full environment/build records
stay private; per-node verification receipts contain hashes and actual results
without host paths. The parent owns shared test and registry integration.

## Verification

All 91 Lean modules passed with at most two compiler processes and one thread
each. The six Python tests passed after replacing the source-203 alias; no
test was weakened. All six concrete/table bounds reported exactly `propext`,
`Classical.choice`, and `Quot.sound` under `Lean.collectAxioms`. Per-node
`verification.json` records actual results, statement types, toolchain/Mathlib
identity and source/object/log/input hashes. Full import paths remain private.
