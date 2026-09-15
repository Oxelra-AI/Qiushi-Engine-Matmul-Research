import QiushiCalibrationControls
import QiushiCalibrationTable

open BigOperators

namespace QiushiMatmul.Calibration

open CalibrationRows OccupationSystemBridge

def baseConfig : Fin 8 → PlaneExtConfig := ![
  plane484GenConfig, plane485GenConfig, plane486GenConfig, plane487GenConfig,
  plane488GenConfig, plane489GenConfig, plane490GenConfig, plane491GenConfig]

theorem baseConfig_basis : ∀ i, (baseConfig i).planeBasis = planeBasis i := by decide +kernel

/-- `FullOccupation` uses only the plane and target. No assertion is made that
the old compressed target-18 extraction certificate is valid at this target. -/
def controlConfig (i : Fin 8) (target : Nat) : PlaneExtConfig :=
  {baseConfig i with planeBasis := planeBasis i, target := target}

theorem target19_finite_caps (i : Fin 8) (j : Fin 29210) :
    maskMass (tableRow j).mask (pointWeights (target19Points i)) ≤
      19 - ((tableRow j).storedLabel i : Int) := by
  rw [maskMass_pointWeights]
  have h := (tableRow_controls j i).1
  have hc : (pointMass (target19Points i) (tableRow j).mask : Int) +
      ((tableRow j).storedLabel i : Int) ≤ 19 := by exact_mod_cast h
  omega

theorem projected_finite_caps (i : Fin 8) (j : Fin 29210) :
    maskMass (tableRow j).mask (pointWeights (projectedPoints i)) ≤
      23 - ((tableRow j).storedLabel i : Int) := by
  rw [maskMass_pointWeights]
  have h := (tableRow_controls j i).2
  have hc : (pointMass (projectedPoints i) (tableRow j).mask : Int) +
      ((tableRow j).storedLabel i : Int) ≤ 23 := by exact_mod_cast h
  omega

/-- Row geometry and the exact L0 binding are separate, explicit obligations.
The 29,210 numeric inequalities themselves have already been kernel checked. -/
theorem target19_actual_caps_of_exactL0 (i : Fin 8)
    (rows : Fin 29210 → Row (coordinates i))
    (hMask : ∀ j, (rows j).mask = (tableRow j).mask)
    (hCover : ∀ U : Submodule F2 Mat3, W i < U → U < ⊤ → ∃ j, (rows j).space = U)
    (hExact : ∀ j, frozenWangTable.L0 (rows j).space = (tableRow j).storedLabel i) :
    ∀ U : Submodule F2 Mat3, W i < U → U < ⊤ →
      quotientMass (weight i (target19Points i)) U ≤ 19 - (frozenWangTable.L0 U : Int) := by
  rw [weight_eq_coordinateWeight]
  apply (row_caps_iff rows hCover frozenWangTable.L0 19 _).mp
  intro j
  rw [hMask, hExact]
  exact target19_finite_caps i j

theorem projected_actual_caps_of_exactL0 (i : Fin 8)
    (rows : Fin 29210 → Row (coordinates i))
    (hMask : ∀ j, (rows j).mask = (tableRow j).mask)
    (hCover : ∀ U : Submodule F2 Mat3, W i < U → U < ⊤ → ∃ j, (rows j).space = U)
    (hExact : ∀ j, frozenWangTable.L0 (rows j).space = (tableRow j).storedLabel i) :
    ∀ U : Submodule F2 Mat3, W i < U → U < ⊤ →
      quotientMass (weight i (projectedPoints i)) U ≤ 23 - (frozenWangTable.L0 U : Int) := by
  rw [weight_eq_coordinateWeight]
  apply (row_caps_iff rows hCover frozenWangTable.L0 23 _).mp
  intro j
  rw [hMask, hExact]
  exact projected_finite_caps i j

theorem target19_fullOccupation_of_exactL0 (i : Fin 8)
    (rows : Fin 29210 → Row (coordinates i))
    (hMask : ∀ j, (rows j).mask = (tableRow j).mask)
    (hCover : ∀ U : Submodule F2 Mat3, W i < U → U < ⊤ → ∃ j, (rows j).space = U)
    (hExact : ∀ j, frozenWangTable.L0 (rows j).space = (tableRow j).storedLabel i) :
    FullOccupation (controlConfig i 19) frozenWangTable.L0 (weight i (target19Points i)) :=
  ⟨weight_nonneg i _, target19_total i, target19_actual_caps_of_exactL0 i rows hMask hCover hExact⟩

theorem projected_fullOccupation_of_exactL0 (i : Fin 8)
    (rows : Fin 29210 → Row (coordinates i))
    (hMask : ∀ j, (rows j).mask = (tableRow j).mask)
    (hCover : ∀ U : Submodule F2 Mat3, W i < U → U < ⊤ → ∃ j, (rows j).space = U)
    (hExact : ∀ j, frozenWangTable.L0 (rows j).space = (tableRow j).storedLabel i) :
    FullOccupation (controlConfig i 23) frozenWangTable.L0 (weight i (projectedPoints i)) :=
  ⟨weight_nonneg i _, projected_total i, projected_actual_caps_of_exactL0 i rows hMask hCover hExact⟩

end QiushiMatmul.Calibration
