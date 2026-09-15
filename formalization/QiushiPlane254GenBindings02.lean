import QiushiPlane254GenSources02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane254GenBound0020 :
    QuotientRankAtLeast (spanCodes (plane254GenSourceBasis (20 : Fin 26))) (plane254GenSourceLb (20 : Fin 26)) := by
  rw [show plane254GenSourceBasis (20 : Fin 26) = [288, 164, 68, 16, 8, 2, 1] from rfl,
      show plane254GenSourceLb (20 : Fin 26) = 12 from rfl]
  exact plane254GenSource0020
theorem plane254GenBound0021 :
    QuotientRankAtLeast (spanCodes (plane254GenSourceBasis (21 : Fin 26))) (plane254GenSourceLb (21 : Fin 26)) := by
  rw [show plane254GenSourceBasis (21 : Fin 26) = [416, 80, 8, 4, 2, 1] from rfl,
      show plane254GenSourceLb (21 : Fin 26) = 12 from rfl]
  exact plane254GenSource0021
theorem plane254GenBound0022 :
    QuotientRankAtLeast (spanCodes (plane254GenSourceBasis (22 : Fin 26))) (plane254GenSourceLb (22 : Fin 26)) := by
  rw [show plane254GenSourceBasis (22 : Fin 26) = [256, 160, 68, 16, 8, 2, 1] from rfl,
      show plane254GenSourceLb (22 : Fin 26) = 12 from rfl]
  exact plane254GenSource0022
theorem plane254GenBound0023 :
    QuotientRankAtLeast (spanCodes (plane254GenSourceBasis (23 : Fin 26))) (plane254GenSourceLb (23 : Fin 26)) := by
  rw [show plane254GenSourceBasis (23 : Fin 26) = [260, 160, 68, 16, 8, 2, 1] from rfl,
      show plane254GenSourceLb (23 : Fin 26) = 12 from rfl]
  exact plane254GenSource0023
theorem plane254GenBound0024 :
    QuotientRankAtLeast (spanCodes (plane254GenSourceBasis (24 : Fin 26))) (plane254GenSourceLb (24 : Fin 26)) := by
  rw [show plane254GenSourceBasis (24 : Fin 26) = [432, 80, 8, 4, 2, 1] from rfl,
      show plane254GenSourceLb (24 : Fin 26) = 12 from rfl]
  exact plane254GenSource0024
theorem plane254GenBound0025 :
    QuotientRankAtLeast (spanCodes (plane254GenSourceBasis (25 : Fin 26))) (plane254GenSourceLb (25 : Fin 26)) := by
  rw [show plane254GenSourceBasis (25 : Fin 26) = [288, 160, 64, 16, 8, 4, 2, 1] from rfl,
      show plane254GenSourceLb (25 : Fin 26) = 6 from rfl]
  exact plane254GenSource0025
end QiushiMatmul
