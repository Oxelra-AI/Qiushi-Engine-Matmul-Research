import QiushiNormalizedCosetCount

noncomputable section

open QiushiMatmul QiushiMatmul.NormalizedCosetCount

example : Module.finrank F2 (spanCodes [272,4,2,1]) = 4 :=
  normalizedCosetSpan_finrank

example : Module.finrank F2 (spanCodes [4,2,1]) = 3 := firstRowFamily_finrank

example : Nat.card {U : Submodule F2 Mat3 //
    U ≤ spanCodes [272,4,2,1] ∧ Module.finrank F2 U = 3} = 15 :=
  normalizedCosetSpan_hyperplane_count

example : Nat.card {U : Submodule F2 Mat3 //
    U ≤ spanCodes [272,4,2,1] ∧ Module.finrank F2 U = 3 ∧
      U ≠ spanCodes [4,2,1]} = 14 := affine_hyperplane_count

example : Fin 14 ≃ {U : Submodule F2 Mat3 //
    U ≤ spanCodes [272,4,2,1] ∧ Module.finrank F2 U = 3 ∧
      U ≠ spanCodes [4,2,1]} := affineHyperplanesEquiv

example (i : Fin 14) : (affineHyperplanesEquiv i).val = affineHyperplane i := rfl

example : reportHyperplane 0 = firstRowFamily := rfl

example (i : Fin 14) : reportHyperplane i.succ = affineHyperplane i := rfl

example (i : Fin 14) : affineHyperplane i ≤ normalizedCosetSpan :=
  reportHyperplane_le i.succ

example (i : Fin 14) : Module.finrank F2 (affineHyperplane i) = 3 :=
  reportHyperplane_finrank i.succ

example : Function.Injective affineHyperplane := by
  intro i j h
  exact Fin.succ_injective _ (reportHyperplane_injective
    (show reportHyperplane i.succ = reportHyperplane j.succ from h))

example (U : Submodule F2 Mat3) (hU : U ≤ normalizedCosetSpan)
    (hd : Module.finrank F2 U = 3) : ∃! i : Fin 15, reportHyperplane i = U :=
  report_hyperplane_complete U hU hd

example (U : Submodule F2 Mat3) (hU : U ≤ normalizedCosetSpan)
    (hd : Module.finrank F2 U = 3) (hne : U ≠ firstRowFamily) :
    ∃! i : Fin 14, affineHyperplane i = U := affine_hyperplane_complete U hU hd hne

/-- info: 'QiushiMatmul.NormalizedCosetCount.normalizedCosetSpan_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.NormalizedCosetCount.normalizedCosetSpan_finrank

/-- info: 'QiushiMatmul.NormalizedCosetCount.firstRowFamily_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.NormalizedCosetCount.firstRowFamily_finrank

/-- info: 'QiushiMatmul.NormalizedCosetCount.normalizedCosetSpan_hyperplane_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.NormalizedCosetCount.normalizedCosetSpan_hyperplane_count

/-- info: 'QiushiMatmul.NormalizedCosetCount.reportHyperplane_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.NormalizedCosetCount.reportHyperplane_le

/-- info: 'QiushiMatmul.NormalizedCosetCount.reportHyperplane_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.NormalizedCosetCount.reportHyperplane_finrank

/-- info: 'QiushiMatmul.NormalizedCosetCount.reportHyperplane_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.NormalizedCosetCount.reportHyperplane_injective

/-- info: 'QiushiMatmul.NormalizedCosetCount.report_hyperplane_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.NormalizedCosetCount.report_hyperplane_complete

/-- info: 'QiushiMatmul.NormalizedCosetCount.affineHyperplanesEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.NormalizedCosetCount.affineHyperplanesEquiv

/-- info: 'QiushiMatmul.NormalizedCosetCount.affine_hyperplane_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.NormalizedCosetCount.affine_hyperplane_count

/-- info: 'QiushiMatmul.NormalizedCosetCount.affine_hyperplane_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.NormalizedCosetCount.affine_hyperplane_complete

end
