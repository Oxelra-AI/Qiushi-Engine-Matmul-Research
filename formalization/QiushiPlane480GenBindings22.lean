import QiushiPlane480GenSources22
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane480GenBound0220 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (220 : Fin 221))) (plane480GenSourceLb (220 : Fin 221)) := by
  rw [show plane480GenSourceBasis (220 : Fin 221) = [256, 128, 96, 16, 8, 4, 2, 1] from rfl,
      show plane480GenSourceLb (220 : Fin 221) = 6 from rfl]
  exact plane480GenSource0220
end QiushiMatmul
