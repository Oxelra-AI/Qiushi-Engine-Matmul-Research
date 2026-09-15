import QiushiCalibrationActual
import QiushiCalibrationSingletons

open BigOperators QiushiMatmul QiushiMatmul.Calibration
open QiushiMatmul.OccupationSystemBridge

example : table.length = 29210 := table_length
example : orderedTable.length = 29210 := orderedTable_length
example (i : Fin 8) (j : Fin 29210) :
    pointMass (target19Points i) (tableRow j).mask + (tableRow j).storedLabel i ≤ 19 :=
  (tableRow_controls j i).1
example (i : Fin 8) (j : Fin 29210) :
    pointMass (projectedPoints i) (tableRow j).mask + (tableRow j).storedLabel i ≤ 23 :=
  (tableRow_controls j i).2
example (i : Fin 8) (U : Submodule F2 Mat3) (hWU : W i < U) (hU : U < ⊤) :
    ∃! j : Fin 29210, (actualRows i j).space = U := actualRows_complete i U hWU hU
example (hExact : ∀ i : Fin 8, ∀ j : Fin 29210,
    frozenWangTable.L0 (actualRows i j).space = (tableRow j).storedLabel i) (i : Fin 8) :
    FullOccupation (controlConfig i 19) frozenWangTable.L0 (weight i (target19Points i)) :=
  target19_fullOccupation hExact i
example (hExact : ExactL0) (i : Fin 8) :
    FullOccupation (controlConfig i 23) frozenWangTable.L0 (weight i (projectedPoints i)) :=
  projected_fullOccupation hExact i
example : (TableRow.mk 0 20).check = false := by decide +kernel
example : CalibrationRows.maskMass 2 (pointWeights (target19Points 5)) = 2 := by decide +kernel

/-- info: 'QiushiMatmul.Calibration.tableRow_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tableRow_controls
/-- info: 'QiushiMatmul.Calibration.catalogue_masks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms catalogue_masks
/-- info: 'QiushiMatmul.Calibration.actualRows_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualRows_complete
/-- info: 'QiushiMatmul.Calibration.target19_fullOccupation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms target19_fullOccupation
/-- info: 'QiushiMatmul.Calibration.projected_fullOccupation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms projected_fullOccupation
