import QiushiReportSupplement

set_option autoImplicit false

noncomputable section

open QiushiMatmul

example : TensorEntryDecomp 23 := Calibration.fixture

example : Calibration.ExactL0 := Calibration.exactL0

example (i : Fin 8) :
    OccupationSystemBridge.FullOccupation (Calibration.controlConfig i 19)
      frozenWangTable.L0 (Calibration.weight i (Calibration.target19Points i)) :=
  Calibration.target19_feasible i

example (i : Fin 8) :
    OccupationSystemBridge.FullOccupation (Calibration.controlConfig i 23)
      frozenWangTable.L0 (Calibration.projectedOccupation i) :=
  Calibration.projectedFixture_feasible i

/-- info: 'QiushiMatmul.Calibration.target19_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Calibration.target19_feasible

/-- info: 'QiushiMatmul.Calibration.projectedFixture_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Calibration.projectedFixture_feasible

example (i : Fin 496) (hi : 478 ≤ i.val) :
    frozenWangTable.L0 (spanCodes (frozenWangBasis i)) = frozenWangLower i :=
  FrozenLabel.small_representative_exact i hi

example (i : Fin 496) (W : Submodule F2 Mat3)
    (hi : frozenWangTable.OrbitImage i W) :
    frozenWangTable.L0 W = frozenWangLower i :=
  FrozenLabel.L0_exact_of_orbit i W hi

/-- info: 'QiushiMatmul.FrozenLabel.frozen_labels_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FrozenLabel.frozen_labels_consistent

example (i : Fin 8) (j : Fin 29210) :
    Calibration.pointMass (Calibration.target19Points i) (Calibration.tableRow j).mask +
      (Calibration.tableRow j).storedLabel i ≤ 19 :=
  (Calibration.tableRow_controls j i).1

example (U : Submodule F2 Mat3) (hWU : plane491GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, spanCodes (CalibrationRows.rowBasis491 i) = U :=
  CalibrationRows.rowBasis491_complete U hWU hU

example : Fin 127 ≃ OccupationSystemBridge.Direction plane491GenConfig.W :=
  CalibrationRows.coordinates491.directionEquiv

example (i : Fin 8) (t : Fin 23) :
    (Calibration.W i).mkQ ((Calibration.projectedDecomp i).A t) =
      (Calibration.directionSection i (Calibration.projectedPoints i t)).val :=
  Calibration.projected_A_eq i t

example : Nat.card (Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2))) = 8283458 :=
  FullSubspaceCount.mat3_all_subspace_count

example : Nat.card {W : Submodule F2 Mat3 // Module.finrank F2 W = 2} = 43435 :=
  FullSubspaceCount.mat3_two_plane_count

example : Nat.card {W : Submodule F2 Mat3 // Module.finrank F2 W = 2 ∧
    ∀ A ∈ W, A ≠ 0 → 2 ≤ A.rank} = 32018 := AllHighCount.all_high_plane_count

example (W : Submodule F2 Mat3) (hW : Module.finrank F2 W = 2) :
    ∃! i : Fin 14, frozenWangTable.OrbitImage ⟨478 + i.val, by omega⟩ W :=
  PlaneOrbit.FullClassification.frozen_classification W hW

example (i : Fin 14) :
    Nat.card {W : Submodule F2 Mat3 // frozenWangTable.OrbitImage ⟨478 + i.val, by omega⟩ W} =
      PlaneOrbit.FullClassification.sizes i :=
  PlaneOrbit.FullClassification.frozen_orbit_sizes i

/-- info: 'QiushiMatmul.PlaneOrbit.FullClassification.frozen_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.PlaneOrbit.FullClassification.frozen_classification

/-- info: 'QiushiMatmul.PlaneOrbit.FullClassification.frozen_orbit_sizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.PlaneOrbit.FullClassification.frozen_orbit_sizes

/-- info: 'QiushiMatmul.AllHighCount.all_high_plane_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.AllHighCount.all_high_plane_count

example (W : Submodule F2 Mat3) (hW : Module.finrank F2 W = 2) :
    Nat.card {S : Submodule F2 (Mat3 ⧸ W) // S ≠ ⊥ ∧ S ≠ ⊤} = 29210 :=
  FullSubspaceCount.plane_quotient_nonzero_proper_subspace_count W hW

example (H : Set Mat3) (hn : 4 ≤ H.ncard)
    (hp : ∀ a ∈ H, ∀ b ∈ H, a ≠ b → (a - b).rank = 1) :
    (∃ p : Mat3, ∃ u : I3 → F2, u ≠ 0 ∧
      ∀ a ∈ H, ∃ v : I3 → F2, a = p + outerMat u v) ∨
    (∃ p : Mat3, ∃ v : I3 → F2, v ≠ 0 ∧
      ∀ a ∈ H, ∃ u : I3 → F2, a = p + outerMat u v) :=
  set_affine_row_or_column_coset H hn hp

/-- info: 'QiushiMatmul.set_affine_row_or_column_coset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.set_affine_row_or_column_coset

/-- info: 'QiushiMatmul.FullSubspaceCount.mat3_all_subspace_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.FullSubspaceCount.mat3_all_subspace_count

/-- info: 'QiushiMatmul.plane484SourceStrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.plane484SourceStrict

/-- info: 'QiushiMatmul.plane491DeadStrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.plane491DeadStrict
