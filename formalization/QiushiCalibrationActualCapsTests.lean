import QiushiCalibrationActualCaps

open QiushiMatmul QiushiMatmul.Calibration
open QiushiMatmul.OccupationSystemBridge

example (i : Fin 8) (q d : Fin 127) :
    (directionSection i d).val ∈ (singletonSpace i q).map (W i).mkQ ↔ d = q :=
  singletonSpace_directions i q d
example (hExact : ExactL0) :
    Nat.card {q : Direction (W 5) // L0SingletonCap 5 q = 2} = 1 := by
  simpa using (L0_cap_distribution hExact 5).2.2
example (hExact : ExactL0) (q : Direction (W 5)) :
    L0SingletonCap 5 q = 2 ↔ q = directionSection 5 1 :=
  L0_orbit489_unique_cap_two hExact q

/-- info: 'QiushiMatmul.Calibration.singletonSpace_directions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms singletonSpace_directions
/-- info: 'QiushiMatmul.Calibration.L0_cap_distribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms L0_cap_distribution
