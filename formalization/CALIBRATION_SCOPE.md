# Occupation Calibration

## Assessment

The report's calibration sentence concerns full systems on all 127 nonzero
quotient directions, with 29,210 strict proper superspace rows per orbit.
It does not concern only the compressed live variables or selected source rows.

`QiushiCalibrationClosed.lean` now proves these positive calibration claims
against the mathematical `frozenWangTable.L0`. Its proof resolves the following
distinctions:

- `FrozenOrbitTable.L0` is a noncomputable maximum over exact invertible
  matrix/transpose orbit images of all 496 representatives. It permits
  overlapping orbits and takes zero outside their union.
- `FrozenWangBindings` establishes **lower** bounds for selected rows. These
  justify necessary caps and infeasibility, but cannot prove a witness satisfies
  the full system: increasing L0 tightens a cap.
- Full positive feasibility needs an upper bound
  `L0(U) <= target - quotientMass(weight,U)` for every strict proper row U.
  Exact singleton-cap distributions need exact L0 values on those singleton
  quotient rows. One orbit witness, hence one lower bound, is insufficient.
- A finite replay additionally needs a proved correspondence between its row
  masks and all actual subspaces U, and between encoded quotient points and
  `OccupationSystemBridge.Direction W`. A cardinality theorem alone is not
  that correspondence.
- Merely changing target 18 to 19 in a compressed configuration is not valid:
  target-18 dead directions can acquire positive capacity at target 19.

## Formalized Layers

The concrete rank-23 control, its projection through all eight quotients,
the quotient coordinate equivalences and the occupation-sum correspondence
have passed parent compilation. `Calibration.tableRow_controls` verifies
both control families against the stored labels on every one of the 29,210
rows in each quotient. `Calibration.singleton_cap_distribution` proves the
eight finite histograms below. All use only the standard Lean axioms.

Global frozen-label consistency is now proved:
`FrozenLabel.L0_exact_of_orbit` identifies L0 on any certified representative
orbit. The concrete row catalogue and its eight geometric transports have
passed parent compilation and exact-type/axiom guards. All 233,680 actual-row
orbit bindings have also passed parent compilation. `Calibration.exactL0`
identifies each stored label with the mathematical L0 value on its actual
superspace. The following unconditional calibration results and their exact-type
and transitive-axiom tests passed in the combined project:

- `target19_feasible`: all eight target-19 weights satisfy every row of the
  full occupation system.
- `projected23_feasible` and `projectedFixture_feasible`: both the saved
  projected point list and the actual projected rank-23 decomposition satisfy
  the full system.
- `actual_cap_distribution`: the singleton histograms below count actual
  nonzero quotient directions with their mathematical L0 capacities.
- `actual_seven_boolean_caps` and `actual_orbit489_unique_cap_two`: the seven
  Boolean-cap cases and the unique cap-two direction of orbit 489.

These proofs use only `propext`, `Classical.choice`, and `Quot.sound` and do
not assume global rank soundness. A feasible target-19 occupation weight is
not asserted to be a rank-19 tensor decomposition.

The complete seven-root calibration group passed fresh kernel replay on
2026-09-15: 37,629 declarations, including all 233,680 actual-row bindings,
were checked from an empty environment. See [STATUS.md](STATUS.md).

## Replayed Evidence

`tools/replay_occupation_calibration.py` reads the actual public frozen LUT
bytes, verifies the proof-manifest SHA-256, and rejects non-primitive pickle
objects. It reuses `proof/assets/occupation/scripts/dim2_independent_semantics.py`
to reconstruct all rows, without a solver or original DRAT proof. All rebuilt
row digests must match the public receipts. Recorded success flags are not used.

The replay passes both control families for all eight orbits: 233,680 rows
per family. Each target-19 support is checked for complete weight 19 and then
against every row. The later `orbit491_target19_long.json` supplies orbit 491's
witness; the initial summary's `UNKNOWN` is not treated as success.

The transformed rank-23 control is checked on all 729 tensor coefficients,
then projected using the existing quotient-coordinate implementation. Every
projected support must equal the complete support in the public summary.
All eight projected lengths are 23, with no killed terms or row violations.

At target 18, the complete singleton-cap histograms are:

| Orbit | Cap 0 | Cap 1 | Cap 2 |
| --- | ---: | ---: | ---: |
| 484 | 84 | 43 | 0 |
| 485 | 86 | 41 | 0 |
| 486 | 87 | 40 | 0 |
| 487 | 79 | 48 | 0 |
| 488 | 86 | 41 | 0 |
| 489 | 95 | 31 | 1 |
| 490 | 84 | 43 | 0 |
| 491 | 78 | 49 | 0 |

These are recomputed from all 127 singleton rows, not accepted from histogram
metadata. They match the hash-bound certificate histograms. They are not
target-19 Booleanity claims: the saved target-19 witness for orbit 486 uses two
multiplicities of 2, and orbit 489 also uses multiplicity 2.

## Provenance Limitation

The relocated control is
`research/materials/quotient_cores/results/pivot_fixed/pivot17_rank23_transformed_control.json`.
Its available hash is
`5221a6ef2e8d7398c02a83a37532da0acc18883c29f51980ad17cea75923bc70`,
while the historical summary records
`8c3288d011a5548d494c73e0913fdbfc5a8a919b94a1e0f3b30174cc4e90205e`.
The replay reports this mismatch rather than asserting historical byte identity.
The available tensor identity and its exact projected supports are independently
revalidated, which suffices for the computational controls reported above.

The LUT itself matches the manifest hash
`542df1f30fc362b292438696d90b76fb532093a431f8309e283aac83ebd6ac02`
and contains 8,283,458 entries. Checked-out LFS pointers are not table data;
the replay may read the matching local LFS object without materializing it in
the parent worktree. Nothing here proves equality of that file with Lean L0.

## Reproduction

The mathematical calibration results are included by `QiushiReportSupplement` and tested
in `QiushiCalibrationClosedTests`. The complete table proof uses the compiler
stack setting already recorded in `lakefile.toml` and `tools/build.py`.

From `formalization/`, supplying the actual LUT bytes:

```sh
python3 -B tools/replay_occupation_calibration.py \
  --repo /path/to/repository \
  --lut /path/to/hash-matching-LUT-object \
  --output /path/to/private/replay.json
python3 -B -m unittest discover -s tests -p test_occupation_calibration.py
```

The output JSON records input hashes, complete target-19 supports, row digests,
both full-row scans, exceptional cap-2 directions, and the formal limitation.
No Lean compiler, parent-source edit, shared olean write, or service action is
needed for this replay.
