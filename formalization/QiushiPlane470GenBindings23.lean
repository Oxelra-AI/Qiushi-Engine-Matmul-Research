import QiushiPlane470GenSources23
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane470GenBound0230 :
    QuotientRankAtLeast (spanCodes (plane470GenSourceBasis (230 : Fin 232))) (plane470GenSourceLb (230 : Fin 232)) := by
  rw [show plane470GenSourceBasis (230 : Fin 232) = [256, 132, 64, 32, 20, 8, 2, 1] from rfl,
      show plane470GenSourceLb (230 : Fin 232) = 6 from rfl]
  exact plane470GenSource0230
theorem plane470GenBound0231 :
    QuotientRankAtLeast (spanCodes (plane470GenSourceBasis (231 : Fin 232))) (plane470GenSourceLb (231 : Fin 232)) := by
  rw [show plane470GenSourceBasis (231 : Fin 232) = [259, 84, 10] from rfl,
      show plane470GenSourceLb (231 : Fin 232) = 17 from rfl]
  exact plane470GenSource0231
end QiushiMatmul
