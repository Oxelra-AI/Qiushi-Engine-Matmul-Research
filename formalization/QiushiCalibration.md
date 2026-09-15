# Concrete Calibration Controls

This extension proves the report's eight target-19 occupation controls and the
projected 23-term fixture controls. `QiushiCalibrationClosed` proves the exact
binding between stored public LUT labels and the mathematical
`frozenWangTable.L0` for all 233,680 actual rows, then discharges the full-system
constraints without certificate hypotheses.

## Mathematical Objects

- `QiushiCalibrationData`: literal point lists, with repetitions preserving
  multiplicities. Public direction `q` is index `q - 1`. Orbit 491 uses the
  later completed witness, not the earlier timeout record.
- `QiushiCalibrationFixture`: all 729 canonical `tensorEntry` coordinates of
  the actual transformed 23-term fixture, using full `codeMat` conventions.
- `QiushiCalibrationCoordinates`: an adapter for the eight proved charts,
  not a replacement coordinate system.
- `QiushiCalibrationProjection`: all 184 A-factor quotient equalities, no
  killed terms, and equality with frozen Wang plane bases 484 through 491.
- `QiushiCalibrationControls`: integer occupation weights on actual nonzero
  quotient elements, totals 19/23, and their equality with the finite row sums.
- `QiushiCalibrationTable000` through `114`: all 29,210 masks and eight labels
  per mask. Each chunk checks both controls for all eight orbits in the kernel.
- `QiushiCalibrationTable`: combines these proofs and sorts by numeric mask.
  Sorting preserves every row and its proved inequalities.
- `QiushiCalibrationCatalogue`: matches the complete sorted mask list with
  the semantic catalogue and reuses its unique actual-subspace coverage.
- `QiushiCalibrationActual`: full-system feasibility conditional only on
  the explicit `ExactL0` numerical binding below.
- `QiushiCalibrationRowOrbit`: exact two-sided XOR span checks for a word in
  the existing matrix-action generators, together with a representative label.
- `QiushiCalibrationRowSource`: ordered equality of the producer's source
  lists with the coordinate-transported catalogue bases.
- `QiushiCalibrationRowL0`: turns checked transports into actual L0 equalities
  using `FrozenLabel.L0_exact_of_orbit`.
- `QiushiCalibrationOrbitChunk000` through `114`: eight transports for each
  of the 29,210 rows, checked against the actual source lists in Lean.
- `QiushiCalibrationOrbitTable`: all 29,210 records, their validity, and
  equality of every mask and packed label with the sorted public table.
- `QiushiCalibrationOrbitBinding`: the precise all-record validity, basis,
  and packed-row equalities sufficient to prove `ExactL0`.
- `QiushiCalibrationFixtureOccupation`: equality of point-list weights with
  occupation counts of the actual 23-term quotient tensor decomposition.
- `QiushiCalibrationActualCaps`: actual singleton superspaces, characterized
  by their one nonzero quotient direction, and cap counts conditional on `ExactL0`.
- `QiushiCalibrationClosed`: equality of all record bases with the actual
  catalogue, the proof `exactL0 : ExactL0`, and unconditional feasibility and
  actual cap distributions.

```lean
def ExactL0 : Prop := forall i : Fin 8, forall j : Fin 29210,
  frozenWangTable.L0 (actualRows i j).space = (tableRow j).storedLabel i
```

The reusable `target19_fullOccupation` and `projected_fullOccupation` lemmas
require this hypothesis. The closing module proves it from every checked
record, with exact basis and table joins; no saved success flag or lower-bound
soundness assumption is substituted for the equality.

The final entry points are `target19_feasible`, `projected23_feasible`, and
`projectedFixture_feasible`. They use `FullOccupation`, including nonnegativity,
the exact total, and caps for every actual strict proper superspace of the
chosen plane. The last theorem uses occupation counts of the tensor fixture
itself, not just its exported point list.

The mathematical `L0` here is the fixed frozen orbit-maximum function.
Identifying its value exactly does not prove that every frozen lower bound is
a sound lower bound on tensor rank. That global soundness task is separate.
The target-19 witnesses are occupation models, not claimed 19-term tensor
decompositions. The projected 23-term witness comes from the proved tensor fixture.

`QiushiCalibrationSingletons` first counts stored singleton caps.
`actual_cap_distribution` identifies the corresponding actual `L0` caps and
proves cardinalities of subtypes of the actual quotient directions.
`actual_seven_boolean_caps` proves that all caps in the seven other planes are
0 or 1. `actual_orbit489_unique_cap_two` identifies the unique cap-2 direction
in orbit 489, whose cap-0/1/2 counts are 95/31/1.

## Reproduction

Dependencies include the parent at `ba42394`, first increment `d3e6dbe`, the
coordinate/catalogue modules (`b6c8bd9`), the global orbit normalizer, and
frozen label consistency (`59d7770`). Lean is 4.33.1, with Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`.

Generate controls with `tools/generate_calibration_lean.py --repo REPO --output
OUT`. Generate rows with `tools/generate_calibration_table.py --repo REPO --lut
LUT --output OUT`. The generators read public scientific artifacts and verify
the manifest hashes. The table generator also matches every full target-18 row
digest. Generated row chunks are in `(dimension, RREF basis)` order; the
mathematical consumer uses their derived numeric-mask order.

`tools/generate_calibration_orbits.py` consumes the supplied transport JSONL,
sorted quotient bases, and sorted `(mask, packedLabels)` table JSON. It performs
no orbit search. Query `i * 29210 + j` has plane index `i` and ascending-mask row
index `j`. Its source basis is the plane basis in its given order, followed by
the quotient basis lifted by `coordinateLift`, without RREF or reordering.
Forward and backward masks use that exact list order. `wordCode` applies the
tail of a generator word first. The terminal producer success record is not
a theorem premise; every span and representative-label check is repeated in Lean.

The existing mathematical `orderedTable` retains the library's stable
`List.mergeSort`. `QiushiCalibrationSort` supplies a structurally recursive
evaluator proved equal to it, solely to permit efficient kernel reduction.
No native evaluation oracle is used for the list-identification proofs.

Compile modules in import order. The 115 numerical table chunks and 115 orbit
chunks are independent within each family. After the geometry and generic
consumers, compile `QiushiCalibrationOrbitTable`, `QiushiCalibrationClosed`,
and `QiushiCalibrationClosedTests`. The final tests include exact theorem-type
examples and seven guarded axiom audits, all passed with only `propext`,
`Classical.choice`, and `Quot.sound`.

Use the pinned clean-build `environment.json` and explicit extension library
paths, with private output directories and a bounded compiler pool. No shared
oleans are written. All finite certificates use ordinary kernel-checked proofs, never
`native_decide`, custom axioms, a solver, or the historical DRAT proof.

The transformed control's available SHA-256 is
`5221a6ef2e8d7398c02a83a37532da0acc18883c29f51980ad17cea75923bc70`.
It differs from the historical summary's byte receipt. Its actual tensor
identity and all projected point coordinates are proved; historical byte
identity is not claimed.
