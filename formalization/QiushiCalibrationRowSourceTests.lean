import QiushiCalibrationRowSource

open QiushiMatmul QiushiMatmul.Calibration

example (i : Fin 8) (bs : List Nat) (hb : ∀ c ∈ bs, c < 128) :
    rowSource i bs = ([256, 128] ++ bs).map
      (fun c => matrixCodeNat (CalibrationRows.codeLinear (rowImages i) (codeMat c))) :=
  rowSource_eq_map i bs hb

example : rowSource 0 [1] = [19, 10, 1] := by decide +kernel
example : RowOrbitCheck (rowSource 0 [1]) 17
    ⟨417, [2], [5, 6, 4], [5, 6, 4]⟩ := by decide +kernel
example : ¬ RowOrbitCheck (rowSource 0 [1]) 18
    ⟨417, [2], [5, 6, 4], [5, 6, 4]⟩ := by decide +kernel

/-- info: 'QiushiMatmul.Calibration.rowSource_eq_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rowSource_eq_map
/-- info: 'QiushiMatmul.Calibration.orbitRecord_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orbitRecord_exact
