import QiushiPlane486GenSources26
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane486GenBound0260 :
    QuotientRankAtLeast (spanCodes (plane486GenSourceBasis (260 : Fin 262))) (plane486GenSourceLb (260 : Fin 262)) := by
  rw [show plane486GenSourceBasis (260 : Fin 262) = [260, 128, 68, 36, 20, 8, 2, 1] from rfl,
      show plane486GenSourceLb (260 : Fin 262) = 9 from rfl]
  exact plane486GenSource0260
theorem plane486GenBound0261 :
    QuotientRankAtLeast (spanCodes (plane486GenSourceBasis (261 : Fin 262))) (plane486GenSourceLb (261 : Fin 262)) := by
  rw [show plane486GenSourceBasis (261 : Fin 262) = [256, 128, 64, 32, 8, 4, 2, 1] from rfl,
      show plane486GenSourceLb (261 : Fin 262) = 3 from rfl]
  exact plane486GenSource0261
end QiushiMatmul
