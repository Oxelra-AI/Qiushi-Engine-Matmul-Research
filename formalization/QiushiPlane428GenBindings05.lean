import QiushiPlane428GenSources05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane428GenBound0050 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (50 : Fin 51))) (plane428GenSourceLb (50 : Fin 51)) := by
  rw [show plane428GenSourceBasis (50 : Fin 51) = [256, 134, 70, 38, 16, 14, 1] from rfl,
      show plane428GenSourceLb (50 : Fin 51) = 12 from rfl]
  exact plane428GenSource0050
end QiushiMatmul
