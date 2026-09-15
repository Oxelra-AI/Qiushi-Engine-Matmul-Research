import QiushiCalibrationFixtureOccupation

open BigOperators QiushiMatmul QiushiMatmul.Calibration

example (i : Fin 8) : projectedOccupation i = weight i (projectedPoints i) :=
  projectedOccupation_eq i
example (i : Fin 8) : (∑ q, projectedOccupation i q) = 23 := projectedOccupation_total i

/-- info: 'QiushiMatmul.Calibration.projectedOccupation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms projectedOccupation_eq
