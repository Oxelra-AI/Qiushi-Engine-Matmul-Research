import QiushiCalibrationRowOrbit

open QiushiMatmul QiushiMatmul.Calibration QiushiMatmul.GlobalOrbit

example (source : List Nat) (label : Nat) (t : Transition)
    (h : RowOrbitCheck source label t) :
    frozenWangTable.OrbitImage t.target (spanCodes source) :=
  rowOrbitCheck_orbit source label t h

example (hExactOrbit : ∀ k : Fin 496, ∀ U : Submodule F2 Mat3,
    frozenWangTable.OrbitImage k U → frozenWangTable.L0 U = frozenWangLower k)
    (source : List Nat) (label : Nat) (t : Transition)
    (h : RowOrbitCheck source label t) : frozenWangTable.L0 (spanCodes source) = label :=
  rowOrbitCheck_exact hExactOrbit source label t h

example : RowOrbitCheck [1, 2, 4, 8, 16, 32, 64, 128, 256] 0
    ⟨0, [], [256, 128, 64, 32, 16, 8, 4, 2, 1],
      [256, 128, 64, 32, 16, 8, 4, 2, 1]⟩ := by decide +kernel

example : ¬ RowOrbitCheck [1] 0 ⟨0, [], [0], []⟩ := by decide +kernel

/-- info: 'QiushiMatmul.Calibration.rowOrbitCheck_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rowOrbitCheck_orbit
/-- info: 'QiushiMatmul.Calibration.rowOrbitCheck_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rowOrbitCheck_exact
