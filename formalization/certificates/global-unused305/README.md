# Frozen Rank-17 Certificates: 305, 306, 307

Each module `QiushiGlobalOrbitUnusedNNN` exports, in namespace
`QiushiMatmul.GlobalOrbit.Unused`:

```lean
repNNN : QuotientRankAtLeast (spanCodes (frozenWangTable.basis NNN))
  (frozenWangTable.lower NNN)
```

The concrete declarations are `QiushiMatmul.planeNNNUnusedGen_lb17`.

| Node | Actual basis | Source rows | Dead rows | Live cosets | Exact leaves |
| --- | --- | ---: | ---: | ---: | ---: |
| 305 | `[258,84,10,1]` | 84 | 1 | 30 | 7 |
| 306 | `[132,96,10,1]` | 30 | 14 | 17 | 1 |
| 307 | `[272,96,10,1]` | 20 | 12 | 19 | 1 |

All three exclude decomposition lengths below 17. Their selected source pools
contain only existing closed quotient-rank declarations and do not depend on
each other. Node 305 uses `FrozenRank.span109_lb14`; node 306 uses
`FrozenRank.span162_lb16`. All other imports are previously closed sources.
Every source theorem, actual basis, bound and explicit transport is listed in
the corresponding `sources.json`, `tables.json` and `transport-witnesses.json`.
There is no import of `FrozenRegistry` or assumed rank soundness of the table.

## Finite Proof

The bounded producer enumerated only the 374 subspaces above each target,
reusing the shared masked one-vector extension words. It did not run a new
global orbit search. Linear programming found exact Farkas contradictions for
306 and 307, with right-hand sides -14 and -3. For 305, six integer binary
splits close seven leaves, with right-hand sides
`[-32,-116,-3,-30,-2,-10,-10]`.

The generated Lean leaves check nonnegative integer multipliers and exact
coefficient cancellation. Its tree proves every required branch assumption,
and eliminates the branch hypotheses before `generic_plane_qra` is applied.
The final declarations have no source, finite-search or numerical-label
hypotheses. This is an alternative finite proof, not a replay of historical
backtracking bytes or DRAT and not a proof of the entire frozen rank table.

## Reproduction

From `formalization`, use the existing producer with explicit bases,
transitions, closed source registry and fresh private staging output:

```sh
python tools/global_orbit_unused_certificate.py \
  --bases "$BASES" --transitions "$TRANSITIONS" --registry "$CLOSED_REGISTRY" \
  --node 305 --bound 17 --output "$STAGING/search.json" --emit "$STAGING/emitted"
python -B tools/test_global_unused305307.py
python tools/build_global_orbits.py --environment "$ENVIRONMENT" --jobs 2 \
  QiushiGlobalOrbitUnused305*.lean QiushiGlobalOrbitUnused306*.lean \
  QiushiGlobalOrbitUnused307*.lean
```

Repeat discovery with node 306 or 307 as needed. `closed-predecessors.json`
records the exact selected proof prerequisites, not a universal rank registry.
The broader original discovery input is hash-bound in `generation.json`;
removing unused LP rows can change which exact certificate the solver finds.
The committed branch and transport certificates regenerate deterministically.

The existing emitter's `emit_checks(meta, output, width=128)` is used instead
of its default width 32, reducing repeated compiler imports. It retains the
same checked predicates and exhaustive block-assembly theorem. There are
47/29/27 generated modules, plus two wrapper/test modules per node, 109 total.
The test helper re-emits each package with this recorded width and compares
every generated source byte-for-byte. It also checks every exact ray, branch
context, explicit matrix transport, source bound, dead witness and live-coset
partition, with corrupt-multiplier and corrupt-path negative controls.

The tests accept `--helpers FORMALIZATION` for external read-only producer
helpers and repeated `--node NNN` to select an individual certificate. The
private build uses an explicit pinned environment, cached closed imports,
at most two compiler processes, one thread each, and separate output.
Do not run the builder against an output directory another build owns.

The shared packaged-certificate test dictionary should include the three
bases above, target 16, and the predecessor sets in their respective
`closed-predecessors.json` files. That shared test and the registry are not
modified by this package.

## Verification

All 109 Lean modules compiled: 49 for 305, 31 for 306 and 29 for 307.
Both final declarations for each node have exactly the transitive axioms
`propext`, `Classical.choice`, `Quot.sound`. The six batch Python regression
tests passed across all three certificates. No unproved assumptions were
introduced, and no parent source, shared object or registry file was changed.

Each certificate directory contains a path-free `verification.json` binding
its current source, object, log, input, helper and direct external-import
hashes. It also records Lean 4.33.1, the pinned Mathlib revision, two compiler
processes maximum and one thread per process. The full build receipt and
path-bearing environment identity remain in private output.
