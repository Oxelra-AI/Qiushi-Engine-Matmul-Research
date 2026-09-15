# Formalization Status

The main theorem and every frozen representative bound
are closed Lean proofs. All 13,438 registered modules have successful
source-matched build outputs. All six
kernel replay groups passed. The formalization and its verification are complete
for the mathematical scope in [COVERAGE.md](COVERAGE.md).

## Proved Results

`QiushiFinalTheorem.lean` proves, without finite-bound hypotheses:

- `rank_ge_21 : RankAtLeast 21`;
- `rank_between_21_and_23 : RankAtLeast 21 ∧ TensorEntryRankAtMost 23`;
- `bilinear_mul_requires_21`: every exact bilinear algorithm for ordinary
  3-by-3 matrix multiplication over `ZMod 2` uses at least 21 products.

All finite premises are proved, including the eight high-pair quotient bounds
at 19. Exact interfaces and transitive axioms passed inspection.
The withdrawn plane-479-at-19 shortcut is not used.

All **496 of 496** frozen representative bounds have passed compilation
and exact-type/axiom checks. `FrozenRegistry.all_representatives` assembles
these proofs. `FrozenRegistry.L0_rank_sound` then proves the recorded bound
for every actual matrix subspace, without assuming any representative bound.
The three global API guards and the empty-complement check also passed.
The main theorem uses directly proved selected bounds; the complete registry
is a downstream result.

The remaining report-level results include:

- arbitrary-subspace quotient/restriction equivalence, the E11 three-term
  lift, and ordinary matrix-multiplication semantics;
- general affine row/column geometry, general matrix saturation, and the
  full three-parameter tensor symmetry with its coefficient pullback;
- actual subspace counts, all fourteen two-plane orbits and their sizes,
  all-dimensional frozen coverage, and global label consistency;
- all 233,680 actual-row orbit bindings, complete target-19 occupation
  controls, projected rank-23 controls and exact singleton capacities;
- the eight full occupation no-model theorems, Boolean multiplicity copies
  and disjoint sequential-counter encoding semantics.

[COVERAGE.md](COVERAGE.md) states the precise hypotheses and declarations.
All inspected proof dependencies use only `propext`, `Classical.choice`
and `Quot.sound`.

## Verification Results

Every group in `verification.json` passed the unchanged pinned Lean
`Environment.replay` from an empty kernel environment, including the full
dependency closure and constructor/recursor checks. All replay subprocesses
exited successfully. Exact root types and transitive axioms were checked
separately. The six independently completed runs were matched to the same
source-built artifact tree and the 89-root manifest.

Publication cleanup changed comments in 22 modules. Recompilation preserved
every kernel payload, including declaration types and proof bodies; only
documentation and linter metadata differ. The
[source map](publication-source-map.json) links these sources to the accepted
build and replay results without replacing the original verification record.

| Group | Terminal roots | Replayed declarations | Seconds | Result |
| --- | ---: | ---: | ---: | --- |
| Main theorem and global finite bounds | 6 | 143,943 | 13,913.845 | Pass |
| Complete calibration | 7 | 37,629 | 10,631.735 | Pass |
| Orbit classification and exact labels | 12 | 33,687 | 3,914.665 | Pass |
| Full occupation systems | 8 | 47,338 | 2,830.106 | Pass |
| Structural results and consequences | 51 | 36,421 | 1,862.878 | Pass |
| Boolean encodings | 5 | 6,713 | 5.121 | Pass |

Dependency counts overlap across groups. The replayer uses the official Lean
kernel. [verification-results.json](verification-results.json)
records the accepted source identity, dependency pins and measured outcomes.

The publication checks also exercise the certificate translators, finite
registries and build/replay drivers: 106 core tests, 30 registry tests and
32 auxiliary tests passed. Four optional generator checks require local
orbit-export snapshots and were skipped in the publication run; the compiled
Lean proofs and kernel replay include the corresponding mathematical results.
See [README.md](README.md) for reproduction commands.

## Build Configuration

Two report entry points and bounded worker counts keep import memory manageable.
The complete replay command allows twelve hours per process; the measured
times above help readers choose a resource budget.

## Scope

The formalization supplies fully proved integer certificates for the finite
premises. It does not formally verify the implementation of historical Python,
PySAT or CaDiCaL programs, nor the exact bytes of every saved pickle, DIMACS
or DRAT artifact. Those historical computations remain separately reproducible.
The E11 result proves a three-term lifting implication from a core witness.
For padded length-22 decompositions, the profile results distinguish nonzero
factors from a length-21 decomposition extended by a zero term. These
conditions are stated in [COVERAGE.md](COVERAGE.md).
