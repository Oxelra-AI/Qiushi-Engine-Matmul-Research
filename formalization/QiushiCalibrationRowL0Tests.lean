import QiushiCalibrationRowL0
import QiushiCalibrationRowSource

open QiushiMatmul QiushiMatmul.Calibration

example (source : List Nat) (label : Nat) (t : GlobalOrbit.Transition)
    (h : RowOrbitCheck source label t) : frozenWangTable.L0 (spanCodes source) = label :=
  rowOrbitCheck_L0 source label t h

example : frozenWangTable.L0 (spanCodes (rowSource 0 [1])) = 17 :=
  rowOrbitCheck_L0 _ _ ⟨417, [2], [5, 6, 4], [5, 6, 4]⟩ (by decide +kernel)

/-- info: 'QiushiMatmul.Calibration.rowOrbitCheck_L0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rowOrbitCheck_L0
/-- info: 'QiushiMatmul.Calibration.orbitRecord_L0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orbitRecord_L0
