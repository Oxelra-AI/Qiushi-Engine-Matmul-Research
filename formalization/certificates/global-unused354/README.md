# Frozen Rank-17 Certificates: 354, 355, 356

Import the corresponding `QiushiGlobalOrbitUnusedNNN` module. In namespace
`QiushiMatmul.GlobalOrbit.Unused`, each exports the unconditional theorem:

```lean
repNNN : QuotientRankAtLeast (spanCodes (frozenWangTable.basis NNN))
  (frozenWangTable.lower NNN)
```

The concrete declarations are `QiushiMatmul.planeNNNUnusedGen_lb17`.

| Node | Actual basis | Source rows | Dead rows | Live cosets | Leaf RHS |
| --- | --- | ---: | ---: | ---: | ---: |
| 354 | `[136,96,20,1]` | 30 | 11 | 20 | -31 |
| 355 | `[164,96,20,1]` | 21 | 9 | 22 | -2 |
| 356 | `[290,96,20,1]` | 27 | 11 | 20 | -2 |

Each proof uses a single exact Farkas leaf at putative decomposition length 16.
There are no integer branch assumptions. All selected source ranks are already
proved, and the three nodes are independent. Node 354 uses the closed
`FrozenRank.span162_lb16`; all source declarations, bases, strengths and
explicit GL/transpose witnesses are listed in each package's JSON files.
There is no `FrozenRegistry` import or assumed global frozen-table soundness.

## Scope and Reproduction

The existing bounded producer inspected only the 374 subspaces above each
target, reusing the shared masked extension words. The emitted source proofs
check each explicit transport; Lean also checks source containment, quotient
sections, dead witnesses, live-row coefficients and exact leaf arithmetic.
The existing `generic_plane_qra` gives each final rank bound. No new base
mathematics is introduced. This is an alternative finite proof, not a replay
of original backtracking bytes, DRAT or historical table files.

From `formalization`, with explicit inputs and fresh private output:

```sh
python tools/global_orbit_unused_certificate.py \
  --bases "$BASES" --transitions "$TRANSITIONS" --registry "$CLOSED_REGISTRY" \
  --node 354 --bound 17 --output "$STAGING/search.json" --emit "$STAGING/emitted"
python -B tools/test_global_unused354356.py
python tools/build_global_orbits.py --environment "$ENVIRONMENT" --jobs 2 \
  QiushiGlobalOrbitUnused354*.lean QiushiGlobalOrbitUnused355*.lean \
  QiushiGlobalOrbitUnused356*.lean
```

Use node 355 or 356 for the other discovery runs. The original discovery
registry is hash-bound in `generation.json`; `closed-predecessors.json`
records the smaller selected proof dependency set. Pruning unused LP inputs
can change the discovered ray, but regeneration from the committed branch
and transport inputs is deterministic.

As recorded in `generation.json`, the supported
`emit_checks(meta, output, width=128)` interface groups the finite predicates
more coarsely than the default width 32. The same exhaustive block-assembly
theorem applies. Each node has 29 generated modules plus its wrapper and tests,
31 modules each, 93 total. The Python tests re-emit at width 128 and compare
all generated sources byte-for-byte. They also check closed predecessors,
explicit transports, complete live/dead partitions, exact rays with no branch
assumptions, and rejection of corrupted multipliers.

The test helper supports external read-only helpers via
`--helpers FORMALIZATION`, and repeated `--node NNN` for individual packages.
The compiler uses a pinned private environment, read-only cached imports,
at most two processes and one thread per process. Never build into output
another invocation owns. Source, object, log and input hash receipts accompany
the package; path-bearing full environment records remain private.

For integration, the shared packaged-certificate test dictionary should add
these nodes with their actual bases, target 16 and the predecessor sets in
`closed-predecessors.json`. That shared test and the registry are not edited
by this package.

## Verification

All 93 Lean modules passed with two compiler processes and one thread each.
The six Python tests passed. All six final concrete/table declarations were
checked with `Lean.collectAxioms`; each reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. The per-node `verification.json` records
the actual source/object/log hashes, direct imported object hashes, toolchain,
Mathlib revision, and input identities without host paths. Full compiler
environment and invocation records remain in the private build output.
