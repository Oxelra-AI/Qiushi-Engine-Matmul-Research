# Global Frozen-Orbit Coverage

This extension owns only new `QiushiGlobalOrbit*` modules and matching tools.
The main proof and existing plane modules are unchanged. Overlap-label
consistency is a separate task and is not an assumption here.

## Proven Coverage

Namespace: `QiushiMatmul.GlobalOrbit`.

```lean
-- Import QiushiGlobalOrbitCoverage.
frozen_coverage (W : Submodule F2 Mat3) :
  ∃ i : Fin 496, frozenWangTable.OrbitImage i W

Covered (W : Space) := ∃ i : Fin 496, frozenWangTable.OrbitImage i W
ExtensionChecks := ∀ i : Fin 496, ∀ c : Fin 512,
  Covered (spanCodes (c.val :: frozenWangBasis i))

global_coverage_iff_extensions : (∀ W : Space, Covered W) ↔ ExtensionChecks
coverage_of_extensions (h : ExtensionChecks) (W : Space) : Covered W
dual_dimension (W : Space) : finrank F2 (dual W) + finrank F2 W = 9
dual_equivalent_iff (W V : Space) : Equivalent (dual W) (dual V) ↔ Equivalent W V
```

`coverage_of_low_dimensions` also reduces coverage to dimensions 0--4,
conditional on coverage of the annihilators of the 496 frozen representatives.
`BasisCheck` proves rank from a small dual-frame certificate. `dual_eq_word`
proves annihilator equality from ranks and orthogonality of generator images.
`word_spanCodes` and `wordSpace_equivalent` reuse the existing verified
generator/codeMat bridge without changing the plane engine.

The extension theorem proves that representative-extension closure transfers
to every covered subspace: the new vector is pulled back through the invertible
generator. Finite spanning-set induction then proves global coverage. It does
not assume global classification or add a premise to the main theorem.

## Concrete Certificates

`ExtensionChecks` is discharged by 31 compiled certificate shards. The 15,311
nontrivial extension transports use explicit XOR masks in both directions;
496 identity cases handle in-span additions. Nine coordinate checks per
representative extend to all 512 matrix codes by proved XOR linearity.
No enumeration of 8,283,458 subspaces is replayed in Lean.
The exported frozen basis-length distribution is
`[1,3,14,68,162,162,68,14,3,1]` for dimensions 0 through 9. Quotient residues
give 15,807 representative/coset cases, versus 496*512 raw vector cases.
These producer counts describe the certificate layout, not additional Lean
cardinality theorems. Coverage is unconditional; 496-way inequivalence and
label consistency are not claimed.

## Verification

All 71 global-orbit modules at the coverage checkpoint pass kernel checking;
five certificate-consumer tests pass, including malformed-input rejection.
Printed dependencies of the reduction, duality, and certificate-soundness
theorems are exactly `propext`, `Classical.choice`, and `Quot.sound`.

The runner `tools/build_global_orbits.py` writes only `.local/global-orbits`,
uses one Lean thread per compiler (default two jobs, up to eight), and imports the
previously verified private plane objects plus the pinned clean environment.
`QiushiQuotientRestriction.lean` was copied unchanged from parent HEAD ba42394
and compiled privately against that environment; it supplies the existing
coordinate annihilator. Its source hash and all result hashes are retained in
timestamped receipts. No mutable parent object directory is imported.

The runner invalidates all selected objects before a build, removes failed
partial outputs, and starts dependencies only after successful selected builds.
Unselected objects are imports, not replay results. Each invocation has its own
receipt and retained logs; `--run` receipts do not claim an object build.
Concurrent invocations sharing the output directory are rejected before
invalidation. Nine focused runner tests cover failure, blocked stale dependents,
source mutation, missing output, cycles, and receipt isolation.

## Rank-Soundness Handoff

Import `QiushiGlobalOrbitRankSoundness`, namespace `QiushiMatmul.GlobalOrbit`:

```lean
frozen_L0_rank_sound_iff_representatives :
  (forall W : Submodule F2 Mat3,
    QuotientRankAtLeast W (frozenWangTable.L0 W)) <->
  forall i : Fin 496,
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis i))
      (frozenWangTable.lower i)
```

`L0_rank_sound_of_representatives` proves the forward construction for any
`FrozenOrbitTable`: transport every sound representative label and bound the
finite maximum. It requires neither coverage nor overlap-label consistency.
`frozen_coverage_with_rank_bound` additionally supplies an actual orbit witness
and its transported label bound using the unconditional coverage theorem.
All four new theorem axiom lists are exactly `propext`, `Classical.choice`,
and `Quot.sound`; exact-type tests compile.

For Fermat's integration: these are completed reductions, not unconditional
global rank soundness. The inspected parent `FrozenRegistry` has 404 of 496
representative bounds, leaving 92 finite rank obligations. Label consistency
alone cannot fill those bounds, and no new enumeration is needed for this
interface. The registry and Fermat-owned label modules are unchanged.
