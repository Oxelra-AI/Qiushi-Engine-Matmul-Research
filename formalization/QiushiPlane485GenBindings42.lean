import QiushiPlane485GenSources42
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane485GenBound0420 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (420 : Fin 421))) (plane485GenSourceLb (420 : Fin 421)) := by
  rw [show plane485GenSourceBasis (420 : Fin 421) = [260, 128, 68, 36, 20, 8, 2, 1] from rfl,
      show plane485GenSourceLb (420 : Fin 421) = 9 from rfl]
  exact plane485GenSource0420
end QiushiMatmul
