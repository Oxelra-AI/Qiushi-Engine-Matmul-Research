import QiushiPlane489GenSources37
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane489GenBound0370 :
    QuotientRankAtLeast (spanCodes (plane489GenSourceBasis (370 : Fin 371))) (plane489GenSourceLb (370 : Fin 371)) := by
  rw [show plane489GenSourceBasis (370 : Fin 371) = [256, 132, 68, 32, 20, 8, 2, 1] from rfl,
      show plane489GenSourceLb (370 : Fin 371) = 9 from rfl]
  exact plane489GenSource0370
end QiushiMatmul
