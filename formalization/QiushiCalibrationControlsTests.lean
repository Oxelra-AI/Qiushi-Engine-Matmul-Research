import QiushiCalibrationControls

open BigOperators QiushiMatmul QiushiMatmul.Calibration

example (i : Fin 8) :
    (∑ q : OccupationSystemBridge.Direction (W i), weight i (target19Points i) q) = 19 :=
  target19_total i
example (i : Fin 8) :
    (∑ q : OccupationSystemBridge.Direction (W i), weight i (projectedPoints i) q) = 23 :=
  projected_total i
example (i : Fin 8) (q) : 0 ≤ weight i (target19Points i) q := weight_nonneg i _ q
example (i : Fin 8) (mask : Nat) :
    CalibrationRows.maskMass mask (pointWeights (target19Points i)) =
      (pointMass (target19Points i) mask : Int) := maskMass_pointWeights _ _
example (i : Fin 8) : weight i (target19Points i) =
    (coordinates i).weight (pointWeights (target19Points i)) := weight_eq_coordinateWeight _ _

/-- info: 'QiushiMatmul.Calibration.target19_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms target19_total
/-- info: 'QiushiMatmul.Calibration.projected_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms projected_total
/-- info: 'QiushiMatmul.Calibration.quotientMass_eq_pointMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quotientMass_eq_pointMass
/-- info: 'QiushiMatmul.Calibration.weight_eq_coordinateWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms weight_eq_coordinateWeight
