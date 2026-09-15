import QiushiCalibrationProjection

open QiushiMatmul QiushiMatmul.Calibration

noncomputable section

example (i : Fin 8) : CalibrationRows.Coordinates (planeBasis i) := coordinates i
example (i : Fin 8) : Fin 127 ≃ OccupationSystemBridge.Direction (W i) :=
  (coordinates i).directionEquiv
example (i : Fin 8) : QuotientTensorDecomp (W i) 23 := projectedDecomp i
example (i : Fin 8) (t : Fin 23) :
    (W i).mkQ ((projectedDecomp i).A t) = (directionSection i (projectedPoints i t)).val :=
  projected_A_eq i t
example (i : Fin 8) (t : Fin 23) : (projectedDecomp i).A t ∉ W i := projected_A_not_mem i t
example (i : Fin 8) : planeBasis i = frozenWangBasis ⟨484 + i.val, by omega⟩ :=
  planeBasis_frozen i

/-- info: 'QiushiMatmul.Calibration.coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coordinates
/-- info: 'QiushiMatmul.Calibration.projected_A_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms projected_A_eq
/-- info: 'QiushiMatmul.Calibration.projected_A_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms projected_A_not_mem
