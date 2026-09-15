import QiushiCalibrationRowsTransport
import QiushiCalibrationRowsPlane487

namespace QiushiMatmul.CalibrationRows

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def images487 : Fin 9 → Nat := ![1, 2, 4, 16, 32, 128, 256, 10, 84]

theorem kernel487 : ∀ c : Fin 512,
    codeLinear images487 (codeMat c.val) = 0 → c = 0 := by decide

theorem section487 : ∀ j : Fin 127,
    codeLinear images487 (codeMat (j.val + 1)) =
      codeMat (lift487 ⟨j.val + 1, by omega⟩).val := by decide

noncomputable def transport487 : RowTransport standardCoordinates coordinates487 where
  linear := codeLinearEquiv images487 kernel487
  base := by
    change (spanCodes [256, 128]).map (codeLinear images487) = spanCodes [84, 10]
    exact (spanCodes_map_eq_of_code_pairs [256, 128]
      [(84, 256), (10, 128)] (codeLinear images487)
      (by decide) (by decide)).symm
  lift_eq := section487

end QiushiMatmul.CalibrationRows
