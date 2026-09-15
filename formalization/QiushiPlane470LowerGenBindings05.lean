import QiushiPlane470LowerGenSources05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane470LowerGenBound0050 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenSourceBasis (50 : Fin 52))) (plane470LowerGenSourceLb (50 : Fin 52)) := by
  rw [show plane470LowerGenSourceBasis (50 : Fin 52) = [259, 133, 84, 53, 10] from rfl,
      show plane470LowerGenSourceLb (50 : Fin 52) = 15 from rfl]
  exact plane470LowerGenSource0050
theorem plane470LowerGenBound0051 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenSourceBasis (51 : Fin 52))) (plane470LowerGenSourceLb (51 : Fin 52)) := by
  rw [show plane470LowerGenSourceBasis (51 : Fin 52) = [256, 68, 16, 8, 2, 1] from rfl,
      show plane470LowerGenSourceLb (51 : Fin 52) = 12 from rfl]
  exact plane470LowerGenSource0051
end QiushiMatmul
