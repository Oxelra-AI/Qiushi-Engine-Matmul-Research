# Calibration Row Geometry

Namespace: `QiushiMatmul.CalibrationRows`.

## Coordinates

`QiushiCalibrationRowsPlane484` through `QiushiCalibrationRowsPlane491` export
`coordinates484 : Coordinates plane484GenConfig.planeBasis`, and similarly
for the other seven configurations. These are checked whole-quotient charts,
not the reduced live-variable classifier. `liftNNN` uses the public ascending
free-bit order; `labelNNN` clears the two RREF pivots and packs those free bits.
All 128 labels are distinct quotient classes and every matrix code is covered.

For `C : Coordinates bs`:

```lean
C.directionEquiv : Fin 127 ≃ OccupationSystemBridge.Direction (spanCodes bs)
C.weight (x : Fin 127 → Int) :
  OccupationSystemBridge.Direction (spanCodes bs) → Int
```

Position `j` denotes label `j.val + 1`. Its quotient representative is exactly
`codeMat (C.lift ⟨j.val + 1, ...⟩).val`. `C.label_correct` identifies the actual
quotient class of every matrix code, including the zero class.
`C.weight_total` and `C.weight_nonneg_iff` transfer totals and nonnegativity.

`maskMass mask x` is `∑ j with mask.testBit j.val = true, x j`.
`Row C` records a mask, an actual matrix subspace, both strict endpoints, and
exact mask/direction incidence. `Row.ofCheck` constructs one from a matrix
basis using executable span checks plus a nonempty and nonfull mask.
`row.maskMass_eq x` identifies its finite sum with `quotientMass (C.weight x)`.

`rows_complete` proves unique coverage of every strict proper supermodule from
29,210 checked rows with pairwise distinct 127-bit signatures and plane
dimension two. It does not accept raw-integer distinctness in place of bit
signature distinctness. `row_caps_iff` transfers arbitrary finite row caps to
all-subspace caps. `fullOccupation_iff` also transfers nonnegativity and total
weight to the existing `FullOccupation` predicate.

## Concrete Catalogue

`QiushiCalibrationRowsAll` supplies all 29,210 rows for every orbit 484--491.
`rowMask : Fin 29210 -> Nat` uses ascending numeric mask order, independently
of the numeric L0 labels. This need not be a historical file's cap-sorted order.
The 58 data chunks check actual XOR spans, a present direction, an absent
direction, and the 127-bit mask bound. Chunk ordering and boundary comparisons
prove distinctness; the mathematical subspace count then proves coverage.

For each orbit, for example 484:

```lean
rowBasis484 : Fin 29210 -> List Nat
rows484 : Fin 29210 -> Row coordinates484
rows484_space i : (rows484 i).space = spanCodes (rowBasis484 i)
rows484_mass i x : maskMass (rowMask i) x =
  quotientMass (coordinates484.weight x) (spanCodes (rowBasis484 i))
rowBasis484_complete U hWU hU : ∃! i : Fin 29210,
  spanCodes (rowBasis484 i) = U
```

Here `hWU` and `hU` assert exactly `plane484GenConfig.W < U` and `U < top`.
No row-domain, coverage, or rank premise remains in this concrete interface.
`caps484_iff L target x` identifies all finite row inequalities with all-subspace
caps, for an arbitrary label function and integer target. The same declarations
are exported through orbit 491.

The ambient linear map sends code 256 to `W[0]`, 128 to `W[1]`, and code `2^k`
to `2^free_bits[k]` for `k < 7`. Thus the raw basis order is
`[W[0], W[1]] ++ quotientBasis.map(lift_q)`. It is not RREF-reduced or sorted
again. This linear change of complement preserves row incidence, not matrix
rank or L0 labels.

`Coordinates.labelCounts_correct` identifies integer histograms of concrete
matrix codes with their actual nonzero quotient-direction weights.
`labelCounts_total` subtracts precisely the weights of matrices in W.

## Numeric Boundary

`QiushiCalibrationRowsLabels` provides `LabelsExact table rows labels` for the
explicit equations `labels i = table.L0 (rows i).space`.
`LabelsExact.of_orbitImages` requires global orbit-label consistency, a frozen
index for each row, checked stored-label/index equalities, and actual exact
orbit witnesses. `labeled_row_caps_iff` then transfers stored numeric caps to
mathematical frozen-L0 caps. These hypotheses are explicit and are not proved
by row geometry. This work does not instantiate those numeric equalities,
generate positive controls, assert rank soundness, or identify historical bytes.

## Verification

The toolchain is Lean 4.33.1 / Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The two test modules pin exact types,
endpoint/index examples, invalid masks, and transitive axiom guards for 21 and
40 declarations. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
`QiushiCalibrationRowsVerification.json` records completed source/object/log
hash checks and the actual guard results; it contains no host paths.

Generate charts with `tools/generate_calibration_rows_coordinates.py --summary
SUMMARY.json`, and the shared catalogue with
`tools/generate_calibration_rows_catalogue.py --certificate-generator
tools/generate_certificate.py`. The latter enumerates pivot patterns directly
and reuses the existing RREF/span routines. It performs no orbit search.

Build with `tools/build_calibration_rows.py --environment ENVIRONMENT.json
--output OUTPUT --jobs 2 --library EXTENSION_LIB --library FROZEN_LIB
QiushiCalibrationRows*.lean`.
The supplied environment uses the parent clean-build JSON schema. Additional
libraries are explicit; no host/package path is embedded in either helper.
Private output holds objects, logs, per-source hashes, and full environment
identity. Selected modules are scheduled by their local import dependencies;
unselected imports use supplied libraries. `--jobs` defaults to one and is
bounded by two. Failed dependencies block consumers, old selected receipts and
objects are removed, and running compilers finish before the helper returns.
No supplied input object cache is overwritten.

Export all 233,680 exact raw-basis queries using
`tools/export_calibration_rows.py --catalogue QiushiCalibrationRowsCatalogue.json
--summary SUMMARY.json --output ROWS.jsonl`. Records contain `orbit`, zero-based
`row_index`, `mask`, and ordered `basis`; the sidecar receipt hashes the inputs
and export. The exporter consumes no numeric labels or positive controls.
