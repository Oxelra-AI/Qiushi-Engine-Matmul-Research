import QiushiFrozenL0Exact

open QiushiMatmul QiushiMatmul.FrozenL0Report

example : frozenWangTable.L0 (spanCodes [272,4,2,1]) = 14 := normalized_L0_exact
example : frozenWangTable.L0 (spanCodes [4,2,1]) = 15 := first_row_L0_exact
example (i : Fin 8) : frozenWangTable.L0
    (Submodule.span (ZMod 2)
      ({codeMat (ahPlaneCode1 i), codeMat (ahPlaneCode2 i)} :
        Set (Matrix (Fin 3) (Fin 3) (ZMod 2)))) = 18 :=
  all_high_representative_L0_exact i

example : frozenWangTable.basis 249 = [80,4,2,1] ∧ frozenWangTable.lower 249 = 14 :=
  normalized_basis_label
example : frozenWangTable.basis 410 = [4,2,1] ∧ frozenWangTable.lower 410 = 15 :=
  first_row_basis_label
example (i : Fin 8) :
    frozenWangBasis ⟨484 + i.val, by omega⟩ = [ahPlaneCode1 i, ahPlaneCode2 i] ∧
      frozenWangLower ⟨484 + i.val, by omega⟩ = 18 := all_high_basis_labels i
example (i : Fin 8) :
    ahPlaneW i = spanCodes (frozenWangBasis ⟨484 + i.val, by omega⟩) :=
  all_high_actual_basis i

/-- info: 'QiushiMatmul.FrozenL0Report.normalized_L0_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normalized_L0_exact

/-- info: 'QiushiMatmul.FrozenL0Report.first_row_L0_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_row_L0_exact

/-- info: 'QiushiMatmul.FrozenL0Report.all_high_representative_L0_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms all_high_representative_L0_exact
