import QiushiCalibrationFormula
import QiushiCalibrationProjection

open BigOperators

namespace QiushiMatmul.Calibration

set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

noncomputable def weight {n : Nat} (i : Fin 8) (points : Fin n → Fin 127)
    (q : OccupationSystemBridge.Direction (W i)) : Int := by
  classical
  exact ∑ t with directionSection i (points t) = q, 1

theorem weight_nonneg {n : Nat} (i : Fin 8) (points : Fin n → Fin 127) (q) :
    0 ≤ weight i points q := by
  classical
  unfold weight
  exact Finset.sum_nonneg (fun _ _ => by norm_num)

theorem weight_total {n : Nat} (i : Fin 8) (points : Fin n → Fin 127) :
    (∑ q, weight i points q) = (n : Int) := by
  classical
  simpa [weight] using Finset.sum_fiberwise Finset.univ
    (fun t => directionSection i (points t)) (fun _ => (1 : Int))

theorem target19_total (i : Fin 8) : (∑ q, weight i (target19Points i) q) = 19 :=
  weight_total i _

theorem projected_total (i : Fin 8) : (∑ q, weight i (projectedPoints i) q) = 23 :=
  weight_total i _

def pointWeights {n : Nat} (points : Fin n → Fin 127) (q : Fin 127) : Int :=
  ∑ t with points t = q, 1

theorem pointWeights_nonneg {n : Nat} (points : Fin n → Fin 127) (q) :
    0 ≤ pointWeights points q := Finset.sum_nonneg (fun _ _ => by norm_num)

theorem pointWeights_total {n : Nat} (points : Fin n → Fin 127) :
    (∑ q, pointWeights points q) = (n : Int) := by
  simpa [pointWeights] using Finset.sum_fiberwise Finset.univ points (fun _ => (1 : Int))

theorem maskMass_pointWeights {n : Nat} (points : Fin n → Fin 127) (mask : Nat) :
    CalibrationRows.maskMass mask (pointWeights points) = (pointMass points mask : Int) := by
  unfold CalibrationRows.maskMass pointWeights
  rw [Finset.sum_fiberwise_eq_sum_filter]
  simp [pointMass]

theorem weight_eq_coordinateWeight {n : Nat} (i : Fin 8) (points : Fin n → Fin 127) :
    weight i points = (coordinates i).weight (pointWeights points) := by
  classical
  funext q
  obtain ⟨j, rfl⟩ := (coordinates i).directionEquiv.surjective q
  rw [CalibrationRows.Coordinates.weight_direction]
  unfold weight pointWeights
  apply Finset.sum_congr
  · ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (coordinates i).directionEquiv.injective.eq_iff
  · intro _ _
    rfl

/-- Exact interface for the independently owned row/quotient geometry bridge. -/
theorem quotientMass_eq_pointMass {n : Nat} (i : Fin 8) (points : Fin n → Fin 127)
    (U : Submodule F2 Mat3) (mask : Nat)
    (hmem : ∀ q, (directionSection i q).val ∈ U.map (W i).mkQ ↔
      mask.testBit q.val = true) :
    OccupationSystemBridge.quotientMass (weight i points) U = (pointMass points mask : Int) := by
  classical
  unfold OccupationSystemBridge.quotientMass weight
  rw [Finset.sum_fiberwise_eq_sum_filter]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem, Finset.sum_filter]
  simp [pointMass]

end QiushiMatmul.Calibration
