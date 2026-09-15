import QiushiFrozenL0LinesAffine

open QiushiMatmul QiushiMatmul.FrozenL0Report

example (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hM : M ≠ 0) :
    frozenWangTable.L0 (Submodule.span (ZMod 2) {M}) = 19 := nonzero_line_L0_exact M hM

example (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hW : Module.finrank (ZMod 2) W = 1) : frozenWangTable.L0 W = 19 :=
  one_dimensional_L0_exact W hW

example (i : Fin 14) : frozenWangTable.L0 (affineHyperplane i) = 17 :=
  affine_hyperplane_L0_exact i

example (i : Fin 14) : frozenWangTable.L0 (spanCodes (codexAffineBasis i)) = 17 := by
  rw [← codex_affineHyperplane_eq_basis]
  exact affine_hyperplane_L0_exact i

-- Cardinality eight alone cannot prove the hyperplane upper bound.
example : frozenWangLower 450 = 18 ∧ (spanEnum (frozenWangBasis 450)).card = 8 := by
  decide +kernel

/-- info: 'QiushiMatmul.FrozenL0Report.nonzero_line_L0_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonzero_line_L0_exact

/-- info: 'QiushiMatmul.FrozenL0Report.one_dimensional_L0_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_dimensional_L0_exact

/-- info: 'QiushiMatmul.FrozenL0Report.affine_hyperplane_L0_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms affine_hyperplane_L0_exact
