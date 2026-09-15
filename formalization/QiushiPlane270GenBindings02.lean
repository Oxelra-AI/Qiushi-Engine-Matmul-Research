import QiushiPlane270GenSources02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane270GenBound0020 :
    QuotientRankAtLeast (spanCodes (plane270GenSourceBasis (20 : Fin 22))) (plane270GenSourceLb (20 : Fin 22)) := by
  rw [show plane270GenSourceBasis (20 : Fin 22) = [320, 32, 4, 2, 1] from rfl,
      show plane270GenSourceLb (20 : Fin 22) = 12 from rfl]
  exact plane270GenSource0020
theorem plane270GenBound0021 :
    QuotientRankAtLeast (spanCodes (plane270GenSourceBasis (21 : Fin 22))) (plane270GenSourceLb (21 : Fin 22)) := by
  rw [show plane270GenSourceBasis (21 : Fin 22) = [256, 128, 64, 32, 16, 8, 2, 1] from rfl,
      show plane270GenSourceLb (21 : Fin 22) = 3 from rfl]
  exact plane270GenSource0021
end QiushiMatmul
