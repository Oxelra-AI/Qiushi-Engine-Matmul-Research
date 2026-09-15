import QiushiPlane459GenSources04
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane459GenBound0040 :
    QuotientRankAtLeast (spanCodes (plane459GenSourceBasis (40 : Fin 42))) (plane459GenSourceLb (40 : Fin 42)) := by
  rw [show plane459GenSourceBasis (40 : Fin 42) = [256, 132, 68, 36, 17, 10] from rfl,
      show plane459GenSourceLb (40 : Fin 42) = 15 from rfl]
  exact plane459GenSource0040
theorem plane459GenBound0041 :
    QuotientRankAtLeast (spanCodes (plane459GenSourceBasis (41 : Fin 42))) (plane459GenSourceLb (41 : Fin 42)) := by
  rw [show plane459GenSourceBasis (41 : Fin 42) = [257, 135, 68, 39, 17, 10] from rfl,
      show plane459GenSourceLb (41 : Fin 42) = 15 from rfl]
  exact plane459GenSource0041
end QiushiMatmul
