import QiushiCalibrationFormula
import QiushiCalibrationFixture

open BigOperators QiushiMatmul QiushiMatmul.Calibration

example : TensorEntryDecomp 23 := fixture
example : fixture.A 0 = codeMat 261 := rfl
example : fixture.B 0 = codeMat 388 := rfl
example : fixture.C 0 = codeMat 310 := rfl
example : planeBasis 7 = [163, 84] := rfl
example : pointMass (target19Points 2) (2 ^ 35) = 2 := by decide +kernel
example : pointMass (target19Points 2) (2 ^ 67) = 2 := by decide +kernel
example : pointMass (target19Points 5) (2 ^ 1) = 2 := by decide +kernel
example : ∀ i, pointMass (target19Points i) (2 ^ 127 - 1) = 19 := by decide +kernel
example : ∀ i, pointMass (projectedPoints i) (2 ^ 127 - 1) = 23 := by decide +kernel
example (i : Fin 8) (mask : Nat) : mass19Eval i mask = pointMass (target19Points i) mask :=
  mass19Eval_eq i mask
example (row : TableRow) : row.check = true ↔ ∀ i,
    pointMass (target19Points i) row.mask + row.storedLabel i ≤ 19 ∧
    pointMass (projectedPoints i) row.mask + row.storedLabel i ≤ 23 := row.check_iff

/-- info: 'QiushiMatmul.Calibration.fixture_entry_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixture_entry_identity
/-- info: 'QiushiMatmul.Calibration.mass19Eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mass19Eval_eq
/-- info: 'QiushiMatmul.Calibration.mass23Eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mass23Eval_eq
/-- info: 'QiushiMatmul.Calibration.TableRow.check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TableRow.check_iff
