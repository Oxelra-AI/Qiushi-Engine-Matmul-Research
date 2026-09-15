import QiushiCalibration
import QiushiCalibrationSingletons

open QiushiMatmul QiushiMatmul.Calibration
open QiushiMatmul.OccupationSystemBridge

example : table.length = 29210 := table_length
example : orderedTable.length = 29210 := orderedTable_length
example (i : Fin 8) (j : Fin 29210) :
    pointMass (target19Points i) (tableRow j).mask + (tableRow j).storedLabel i ≤ 19 :=
  (tableRow_controls j i).1
example (i : Fin 8) (j : Fin 29210) :
    pointMass (projectedPoints i) (tableRow j).mask + (tableRow j).storedLabel i ≤ 23 :=
  (tableRow_controls j i).2
example (i : Fin 8) (rows : Fin 29210 → CalibrationRows.Row (coordinates i))
    (hMask : ∀ j, (rows j).mask = (tableRow j).mask)
    (hCover : ∀ U : Submodule F2 Mat3, W i < U → U < ⊤ → ∃ j, (rows j).space = U)
    (hExact : ∀ j, frozenWangTable.L0 (rows j).space = (tableRow j).storedLabel i) :
    FullOccupation (controlConfig i 19) frozenWangTable.L0 (weight i (target19Points i)) :=
  target19_fullOccupation_of_exactL0 i rows hMask hCover hExact
example : (TableRow.mk 0 20).check = false := by decide +kernel

/-- info: 'QiushiMatmul.Calibration.tableRow_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tableRow_controls
/-- info: 'QiushiMatmul.Calibration.target19_finite_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms target19_finite_caps
/-- info: 'QiushiMatmul.Calibration.projected_finite_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms projected_finite_caps
/-- info: 'QiushiMatmul.Calibration.target19_fullOccupation_of_exactL0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms target19_fullOccupation_of_exactL0
