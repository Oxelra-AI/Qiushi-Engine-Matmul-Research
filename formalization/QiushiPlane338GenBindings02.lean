import QiushiPlane338GenSources02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane338GenBound0020 :
    QuotientRankAtLeast (spanCodes (plane338GenSourceBasis (20 : Fin 21))) (plane338GenSourceLb (20 : Fin 21)) := by
  rw [show plane338GenSourceBasis (20 : Fin 21) = [258, 138, 64, 34, 16, 6, 1] from rfl,
      show plane338GenSourceLb (20 : Fin 21) = 12 from rfl]
  exact plane338GenSource0020
end QiushiMatmul
