import QiushiCalibrationControls

open BigOperators

namespace QiushiMatmul.Calibration

noncomputable def projectedOccupation (i : Fin 8)
    (q : OccupationSystemBridge.Direction (W i)) : Int := by
  classical
  exact ∑ t with (W i).mkQ ((projectedDecomp i).A t) = q.val, 1

theorem projectedOccupation_eq (i : Fin 8) :
    projectedOccupation i = weight i (projectedPoints i) := by
  classical
  funext q
  unfold projectedOccupation weight
  apply Finset.sum_congr
  · ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, projected_A_eq, Subtype.val_inj]
  · intro _ _
    rfl

theorem projectedOccupation_total (i : Fin 8) : (∑ q, projectedOccupation i q) = 23 := by
  rw [projectedOccupation_eq]
  exact projected_total i

end QiushiMatmul.Calibration
