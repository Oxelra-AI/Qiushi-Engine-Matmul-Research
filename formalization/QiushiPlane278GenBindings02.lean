import QiushiPlane278GenSources02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane278GenBound0020 :
    QuotientRankAtLeast (spanCodes (plane278GenSourceBasis (20 : Fin 28))) (plane278GenSourceLb (20 : Fin 28)) := by
  rw [show plane278GenSourceBasis (20 : Fin 28) = [264, 88, 56, 4, 2, 1] from rfl,
      show plane278GenSourceLb (20 : Fin 28) = 12 from rfl]
  exact plane278GenSource0020
theorem plane278GenBound0021 :
    QuotientRankAtLeast (spanCodes (plane278GenSourceBasis (21 : Fin 28))) (plane278GenSourceLb (21 : Fin 28)) := by
  rw [show plane278GenSourceBasis (21 : Fin 28) = [256, 132, 64, 32, 16, 12, 2, 1] from rfl,
      show plane278GenSourceLb (21 : Fin 28) = 9 from rfl]
  exact plane278GenSource0021
theorem plane278GenBound0022 :
    QuotientRankAtLeast (spanCodes (plane278GenSourceBasis (22 : Fin 28))) (plane278GenSourceLb (22 : Fin 28)) := by
  rw [show plane278GenSourceBasis (22 : Fin 28) = [260, 132, 64, 32, 20, 12, 2, 1] from rfl,
      show plane278GenSourceLb (22 : Fin 28) = 9 from rfl]
  exact plane278GenSource0022
theorem plane278GenBound0023 :
    QuotientRankAtLeast (spanCodes (plane278GenSourceBasis (23 : Fin 28))) (plane278GenSourceLb (23 : Fin 28)) := by
  rw [show plane278GenSourceBasis (23 : Fin 28) = [260, 132, 68, 36, 16, 12, 2, 1] from rfl,
      show plane278GenSourceLb (23 : Fin 28) = 9 from rfl]
  exact plane278GenSource0023
theorem plane278GenBound0024 :
    QuotientRankAtLeast (spanCodes (plane278GenSourceBasis (24 : Fin 28))) (plane278GenSourceLb (24 : Fin 28)) := by
  rw [show plane278GenSourceBasis (24 : Fin 28) = [256, 128, 68, 36, 20, 12, 2, 1] from rfl,
      show plane278GenSourceLb (24 : Fin 28) = 9 from rfl]
  exact plane278GenSource0024
theorem plane278GenBound0025 :
    QuotientRankAtLeast (spanCodes (plane278GenSourceBasis (25 : Fin 28))) (plane278GenSourceLb (25 : Fin 28)) := by
  rw [show plane278GenSourceBasis (25 : Fin 28) = [256, 128, 64, 32, 16, 8, 2, 1] from rfl,
      show plane278GenSourceLb (25 : Fin 28) = 3 from rfl]
  exact plane278GenSource0025
theorem plane278GenBound0026 :
    QuotientRankAtLeast (spanCodes (plane278GenSourceBasis (26 : Fin 28))) (plane278GenSourceLb (26 : Fin 28)) := by
  rw [show plane278GenSourceBasis (26 : Fin 28) = [276, 68, 36, 8, 2, 1] from rfl,
      show plane278GenSourceLb (26 : Fin 28) = 15 from rfl]
  exact plane278GenSource0026
theorem plane278GenBound0027 :
    QuotientRankAtLeast (spanCodes (plane278GenSourceBasis (27 : Fin 28))) (plane278GenSourceLb (27 : Fin 28)) := by
  rw [show plane278GenSourceBasis (27 : Fin 28) = [264, 128, 64, 32, 24, 2, 1] from rfl,
      show plane278GenSourceLb (27 : Fin 28) = 9 from rfl]
  exact plane278GenSource0027
end QiushiMatmul
