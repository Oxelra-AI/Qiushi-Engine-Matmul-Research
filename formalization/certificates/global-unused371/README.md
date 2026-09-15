# Frozen Rank-17 Certificates: 371, 372, 376

Import `QiushiGlobalOrbitUnused371`, `QiushiGlobalOrbitUnused372`, or
`QiushiGlobalOrbitUnused376`. The corresponding unconditional declaration is:

```lean
QiushiMatmul.GlobalOrbit.Unused.repNNN :
  QuotientRankAtLeast (spanCodes (frozenWangTable.basis NNN))
    (frozenWangTable.lower NNN)
```

The concrete declarations are `QiushiMatmul.planeNNNUnusedGen_lb17`.

| Node | Actual basis | Source rows | Dead rows | Live cosets | Leaves | Leaf RHS |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| 371 | `[290,224,20,1]` | 38 | 14 | 18 | 2 | -1, -3 |
| 372 | `[298,224,20,1]` | 37 | 5 | 26 | 2 | -5, -2 |
| 376 | `[160,68,19,10]` | 15 | 10 | 21 | 1 | -1 |

The first two proofs make one exhaustive integer split: quotient label 1 at
floor 1 for 371, and label 31 at floor 0 for 372. Each branch has an exact
Farkas contradiction. Node 376 needs no split. The final theorems have no
branch or rank hypotheses: every source bound is an already proved theorem.
The selected declarations, strengths, actual bases and explicit matrix
transports appear in each package's JSON files. None imports `FrozenRegistry`
or assumes global frozen-table soundness; the three targets are independent.

## Reproduction and Scope

The existing bounded producer inspected 374 quotient superspaces per target,
using the shared explicit extension words. Lean checks transport, source
containment, sections, dead witnesses, live-row coefficients, exact integer
rays and exhaustive branching. The existing `generic_plane_qra` supplies the
final rank bound; this package adds no foundational mathematics. This is not
a replay of historical BTP/DRAT bytes or a historical table identity claim.

From `formalization`, use fresh private staging and a pinned environment:

```sh
python tools/global_orbit_unused_certificate.py \
  --bases "$BASES" --transitions "$TRANSITIONS" --registry "$CLOSED_REGISTRY" \
  --node 371 --bound 17 --output "$STAGING/search.json" --emit "$STAGING/emitted"
python -B tools/test_global_unused371383.py --node 371 --node 372 --node 376
python tools/build_global_orbits.py --environment "$ENVIRONMENT" --jobs 2 \
  QiushiGlobalOrbitUnused371*.lean QiushiGlobalOrbitUnused372*.lean \
  QiushiGlobalOrbitUnused376*.lean
```

Repeat discovery with node 372 or 376. `generation.json` hashes the discovery
inputs; `closed-predecessors.json` contains only selected dependencies. A
different source pool can select a different valid ray. The deterministic
regeneration tests instead use the committed branch and transport inputs.

Checks are regrouped with `emit_checks(meta, output, width=128)` after removing
the default generated `Section`, `Dead`, `Source`, `DeadSource`, and
`Indicator` block files from private staging. This changes only grouping,
not the checked predicates or exhaustive assembly theorem. There are 34, 34,
and 29 Lean modules respectively, 97 total including wrappers and tests.

The six Python tests check closed sources, all explicit transports and
containments, the complete live/dead partition, exact rays and branch
contexts, malformed multiplier/path rejection, and byte-identical emission.
Use `--helpers FORMALIZATION` to read helpers from another checkout.

Use at most two Lean processes and one thread per process, with read-only
cached imports. Do not reuse another build's writable output. Per-node
verification receipts record actual results and hashes without host paths;
the full environment and invocation records remain private. The parent owns
shared certificate-test integration and registry updates.

## Verification

All 97 Lean modules passed with two compiler processes and one thread each.
The six Python tests passed. `Lean.collectAxioms` reported exactly `propext`,
`Classical.choice`, and `Quot.sound` for all six final concrete/table bounds.
The per-node `verification.json` records the observed results and hashes of
sources, objects, logs, direct imported objects, helpers and discovery inputs,
plus the actual Lean version and Mathlib revision. No host path is published.
