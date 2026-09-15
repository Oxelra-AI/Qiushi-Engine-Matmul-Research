import QiushiCalibrationSingletons

open QiushiMatmul QiushiMatmul.Calibration

example (q : Fin 127) : (singletonRow q).mask = 2 ^ q.val := singleton_masks q
example (i : Fin 8) (h : i ≠ 5) (q : Fin 127) :
    singletonCap i q = 0 ∨ singletonCap i q = 1 := seven_boolean_caps i h q
example (q : Fin 127) : singletonCap 5 q = 2 ↔ q = 1 := orbit489_unique_cap_two q
example : capCount 5 0 = 95 ∧ capCount 5 1 = 31 ∧ capCount 5 2 = 1 :=
  singleton_cap_distribution 5
example (i : Fin 8) (cap : Int) :
    Nat.card {q : OccupationSystemBridge.Direction (W i) // actualSingletonCap i q = cap} =
      capCount i cap := actual_cap_count i cap

/-- info: 'QiushiMatmul.Calibration.singleton_cap_distribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms singleton_cap_distribution
/-- info: 'QiushiMatmul.Calibration.actual_cap_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actual_cap_count
