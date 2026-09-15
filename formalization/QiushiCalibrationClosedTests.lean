import QiushiCalibrationClosed

open QiushiMatmul QiushiMatmul.Calibration
open QiushiMatmul.OccupationSystemBridge

example : allOrbitRecords.length = 29210 := allOrbitRecords_length
example (i : Fin 8) (j : Fin 29210) :
    frozenWangTable.L0 (actualRows i j).space = (tableRow j).storedLabel i := exactL0 i j
example (i : Fin 8) :
    FullOccupation (controlConfig i 19) frozenWangTable.L0 (weight i (target19Points i)) :=
  target19_feasible i
example (i : Fin 8) :
    FullOccupation (controlConfig i 23) frozenWangTable.L0 (weight i (projectedPoints i)) :=
  projected23_feasible i
example (i : Fin 8) :
    FullOccupation (controlConfig i 23) frozenWangTable.L0 (projectedOccupation i) :=
  projectedFixture_feasible i
example (i : Fin 8) (U : Submodule F2 Mat3) (hWU : W i < U) (hU : U < ⊤) :
    quotientMass (weight i (target19Points i)) U ≤ 19 - (frozenWangTable.L0 U : Int) :=
  (target19_feasible i).cap U hWU hU
example (i : Fin 8) (U : Submodule F2 Mat3) (hWU : W i < U) (hU : U < ⊤) :
    quotientMass (projectedOccupation i) U ≤ 23 - (frozenWangTable.L0 U : Int) :=
  (projectedFixture_feasible i).cap U hWU hU
example : Nat.card {q : Direction (W 5) // L0SingletonCap 5 q = 2} = 1 := by
  simpa using (actual_cap_distribution 5).2.2
example (i : Fin 8) (hi : i ≠ 5) (q : Direction (W i)) :
    L0SingletonCap i q = 0 ∨ L0SingletonCap i q = 1 := actual_seven_boolean_caps i hi q
example (q : Direction (W 5)) : L0SingletonCap 5 q = 2 ↔ q = directionSection 5 1 :=
  actual_orbit489_unique_cap_two q

/-- info: 'QiushiMatmul.Calibration.exactL0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exactL0
/-- info: 'QiushiMatmul.Calibration.target19_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms target19_feasible
/-- info: 'QiushiMatmul.Calibration.projected23_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms projected23_feasible
/-- info: 'QiushiMatmul.Calibration.projectedFixture_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms projectedFixture_feasible
/-- info: 'QiushiMatmul.Calibration.actual_cap_distribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actual_cap_distribution
/-- info: 'QiushiMatmul.Calibration.actual_seven_boolean_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actual_seven_boolean_caps
/-- info: 'QiushiMatmul.Calibration.actual_orbit489_unique_cap_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actual_orbit489_unique_cap_two
