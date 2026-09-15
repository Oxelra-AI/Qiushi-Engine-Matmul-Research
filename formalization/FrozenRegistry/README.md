# Frozen Representative Rank Registry

This module binds all 496 frozen representatives to established rank
proofs. Each `repNNN` has exactly the type

```lean
QuotientRankAtLeast (spanCodes (frozenWangTable.basis NNN))
  (frozenWangTable.lower NNN)
```

Validated checkpoint: **496 of 496** entries, comprising 395 equal-span bindings,
77 containment bindings, the zero-label entry, exact orbit reversal for 416,
and the zero-quotient adapter for 495, plus 21 exact-orbit/containment bindings.
All previous 466 bindings retain their source choices. `TransportBindings.lean`
checks an exact image of the frozen space, its containment in a proved source,
both invertibilities, and the bound strength; reversal uses only the exact image,
never the generally larger proved source. These transport bindings reuse existing
proofs; the new 227 binding replays its archived BTP trace as described below.
All 496 exact-type/axiom guards and the three unconditional global API guards
passed. The seven driver, three global-audit, six transport-discovery, twelve
BTP translator, and nine BTP reader tests passed. These focused checks compile
proofs against clean imports. The complete registry also passed the separate
main/registry fresh kernel replay: all six public roots and 143,943 declarations
were checked from an empty environment. See [verification results](../STATUS.md).

`checked.json` records the selected bases, frozen labels, source declarations,
source bounds, and binding methods. Python span comparison is only discovery;
Lean checks the actual source type, both containments for equal spans, the
appropriate containment for monotonicity, and the bound inequality.

`Bridge.lean` also supplies reversible exact orbit transport (including both
invertibilities and optional transpose), the explicit column permutation for
416, and the zero-quotient adapter to the existing unconditional `rank_ge_21`.
No frozen numeric L0 evaluation is used as a rank proof. The complete registry
establishes global frozen-L0 rank soundness, without claiming a new orbit
classification or replay of all original binary certificates.
The registry is downstream of the completed main theorem, not a premise of
that theorem; the use of `rank_ge_21` for the zero quotient is therefore acyclic.

## Unconditional API

`All.lean` assembles the checked declarations for every index; `Global.lean`
applies the existing `GlobalOrbit.L0_rank_sound_of_representatives` theorem:

```lean
QiushiMatmul.FrozenRegistry.all_representatives (i : Fin 496) :
  QuotientRankAtLeast (spanCodes (frozenWangTable.basis i)) (frozenWangTable.lower i)

QiushiMatmul.FrozenRegistry.L0_rank_sound (W : Submodule F2 Mat3) :
  QuotientRankAtLeast W (frozenWangTable.L0 W)
```

Neither theorem assumes any representative rank bound. `coverage_with_rank_bound`
also combines these bounds with the existing all-dimensional orbit coverage.
All three declarations have exactly `propext`, `Classical.choice`, and
`Quot.sound` as transitive axioms. `Remaining.lean` checks that the complement
is empty. Overlapping-label consistency is not needed for supremum rank soundness.

## Focused Replay

Prerequisites: Python 3.10+, Lean 4.33.1, and compatible clean compiled imports
for `QiushiMatmul`, `QiushiFrozenWangData`, `QiushiGlobalOrbitRankSoundness`,
the independent bound packages named in `checked.json`, and their dependencies. Supply an
environment JSON containing `lean` and `lean_path`; additional read-only import
directories are optional and precede its search path. From `formalization`:

```sh
python3 tools/test_frozen_registry.py
python3 FrozenRegistry/test_global_audit.py
python3 tools/frozen_registry.py replay \
  --environment "$CLEAN_ENVIRONMENT_JSON" \
  --import-dir "$FROZEN_TABLE_IMPORTS" \
  --output "$PRIVATE_REPLAY_OUTPUT"
```

Repeat `--import-dir` when needed. The driver sequentially compiles the registry's
source dependency closure, reusing existing external imports. Registry modules
use one compiler thread and warnings as errors. Existing Qiushi sources needed
by optional discovery roots retain their legacy warning policy. All outputs
go to the supplied directory, never an import library. `Tests.lean` independently
checks every declared representative type and guards all transitive axioms
against `propext`, `Classical.choice`, and `Quot.sound`. A successful replay emits
exact types, axiom logs, source/object hashes, a checked count, and remaining IDs.
For a complete registry, replay also compiles `GlobalTests.lean` and
`Remaining.lean`, requires all global guards and an empty complement, and records
`global_rank_sound: true` only after those checks succeed.
Any failed replay removes the previous success receipt.

`Inspect.lean` and the driver's `generate` action are optional discovery tools,
not prerequisites for replaying this checkpoint. Discovery examines closed
`QuotientRankAtLeast` declarations imported by `QiushiMatmul`; it is not exhaustive
over parameterized theorems, other modules, or non-definitionally represented
spaces. Unbound entries therefore need interface review, not necessarily new
mathematics. Private discovery ledgers and machine-specific receipts are omitted.
The 21 transport additions use the original 28,742-declaration pool. Its 201
non-span expressions and parameterized theorem applications are separate mapping
work, not presumed missing mathematics. Optional witness discovery uses NumPy and
the existing `generate_certificate.actions`; run its six regression tests with
`python3 FrozenRegistry/test_transport_search.py`.

## Additional Reuse

The separate `KernelBindings.lean` module provides **225 checked span bounds**
from existing functional-kernel bounds. Each proof checks the original source
type and membership of every proposed generator; it uses only containment and
does not assert an unproved equality between the kernel and the chosen span.
All 225 transitive axiom guards passed. This does not increase the registered
representatives.

`Seed020.lean` only adapts `GlobalOrbit.Unused.node20_bound` from
`QiushiGlobalOrbitUnused20`; it does not duplicate that proof. This supplies
representatives 20 and 86 and raises the prior 404 checkpoint to 406. Supply
that module's clean import directory when replaying against an older environment.

The extended inspector includes the unused plane413 source and dead-row helpers and explicit
single-`Fin`-argument theorem applications with at most 4096 arguments per family.
The completed run found 45,017 candidate applications, including 16,133 such
finite instantiations. All 580 previously unresolved inline-match applications
now expose their bases; the resulting spaces add no stronger span bound to the
prior pool. Kernel extraction still gives the same 225 adapters. Arbitrary
theorem premises and parameter types are not synthesized or assumed.

No additional adequate transport/containment witness was found for the then-unbound
92 indices in this expanded pool. This is a discovery limitation, not a formal
nonexistence theorem or a claim that all 92 require new mathematics. The existing
E11 restoration theorem adds three tensor summands for one rank-one A-slice; it
does not provide a general restoration cost equal to the sum of matrix-basis ranks.

To compile these optional helpers separately, use the driver's `build-missing`
action with root `FrozenRegistry.KernelBindings` and the same explicit environment,
read-only imports, and private output arguments as above. This leaves the main
theorem and the registry replay independent of the extra inspection helpers.

## Unused-Node Certificates

`UnusedAdapters.lean` reuses `QiushiFrozenRank24` and the completed
`QiushiGlobalOrbitUnused` packages for 181, 184, 203, 273, 284, and 291. Their
actual bounds are 11, 15, 15, 16, 16, 17, and 16 on the respective frozen bases.
Entry 418 follows by checked containment from the bound-17 source for 284.
Supply those
packages' clean import directory when replaying against an older environment.
This registry does not duplicate their certificate generation or proofs.

The next six bindings reuse `QiushiFrozenRank27`, `QiushiFrozenRank28`,
`QiushiFrozenRank33`, and the completed 88/289 packages. Their respective bounds
are 11, 11, 14, 13, and 17; 441 follows by containment from 289 at bound 17.
The manifest names their independent source declarations directly, so these
proofs can also serve as BTP prerequisites without importing the aggregate registry.

`Btp227Final.lean` proves the bound 15 on `[294,140,96,16,1]` by translating
the archived 277-leaf BTP trace into 520 checked integer-system leaves.
`PaddedExtraction.lean` connects these occupation constraints to arbitrary
short decompositions, retaining zero fibers and repeated-label multiplicities.
Its eight source representatives have existing closed rank proofs; no source
rank label is used as an assumption. See `BtpSemantics.md` for exact types,
semantic obligations, translation regressions, and focused replay commands.

The 430 checkpoint adds 87/92, 109/162, 224, 240/248/249, and 341.
The first eight reuse their independently closed source declarations, including
the archived BTP proof for 224. `ClosedReductions.bound341` applies the existing
exact invertible orbit/containment reduction to the completed 162 theorem.
Thus no degeneration prerequisite remains open in this registry.

The 433 checkpoint additionally imports the independent bounds for 301, 302,
and 304, at labels 17, 17, and 16. The manifest names their closed final
declarations directly; no proof generation or additional rank premise is used.

The 436 checkpoint adds the independent 308, 309, and 312 bounds at labels
16, 17, and 17, again using their closed source declarations directly.

The 446 checkpoint additionally registers 260/261/263/265, 305/306/307, and
314/316/318. All four first bounds are 16; the other six are 17. Entry 260
uses the compact seven-space `QiushiMatmul.FrozenRank.rep260`, not BTP260.
The already checked BTP260 modules remain an independent reproducible alternative.
Entries 261 and 263 use single-leaf compression of their archived source rows;
265 uses its checked archived branch translation. The other six entries name
their independent closed source declarations directly.

The 454 checkpoint adds exactly 354/355/356/357/358/359/366 at bound 17 and
410 at bound 15. It preserves every prior 446 source choice. The first seven
use their independent closed source declarations; 410 uses its checked
single-leaf archived-source proof. Independently checked 285 and 420 packages
are not yet registered in this checkpoint.

The 466 checkpoint adds 337/339 at bound 16, 353/386/387/388/389/390/392
at bound 17, and the independent BTP285/BTP287/BTP420 proofs at bounds
17/17/18. All 454 previous choices are retained. Each BTP addition uses
one checked Farkas leaf from its archived source rows, without lowering its target.

The final 496 checkpoint registers all remaining independently proved rows.
`Remaining.lean` now proves that no goals remain; it supplies no rank assumptions.
`Reductions.lean` checks 162 -> 341, 284 -> 418, and 289 -> 441. See
`UnusedNodes.md` for archive reuse and prerequisite interfaces. The protobuf
records store proof sizes; the separate pinned BTP archive contains actual DFS
leaf traces for those original backtracking entries. A decoded trace or a
successful external verifier run is not itself a Lean quotient-rank theorem.
