import QiushiPlane292GenSources02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane292GenBound0020 :
    QuotientRankAtLeast (spanCodes (plane292GenSourceBasis (20 : Fin 28))) (plane292GenSourceLb (20 : Fin 28)) := by
  rw [show plane292GenSourceBasis (20 : Fin 28) = [128, 32, 16, 10, 1] from rfl,
      show plane292GenSourceLb (20 : Fin 28) = 14 from rfl]
  exact plane292GenSource0020
theorem plane292GenBound0021 :
    QuotientRankAtLeast (spanCodes (plane292GenSourceBasis (21 : Fin 28))) (plane292GenSourceLb (21 : Fin 28)) := by
  rw [show plane292GenSourceBasis (21 : Fin 28) = [128, 32, 18, 10, 1] from rfl,
      show plane292GenSourceLb (21 : Fin 28) = 14 from rfl]
  exact plane292GenSource0021
theorem plane292GenBound0022 :
    QuotientRankAtLeast (spanCodes (plane292GenSourceBasis (22 : Fin 28))) (plane292GenSourceLb (22 : Fin 28)) := by
  rw [show plane292GenSourceBasis (22 : Fin 28) = [256, 128, 32, 10, 1] from rfl,
      show plane292GenSourceLb (22 : Fin 28) = 14 from rfl]
  exact plane292GenSource0022
theorem plane292GenBound0023 :
    QuotientRankAtLeast (spanCodes (plane292GenSourceBasis (23 : Fin 28))) (plane292GenSourceLb (23 : Fin 28)) := by
  rw [show plane292GenSourceBasis (23 : Fin 28) = [128, 32, 8, 2, 1] from rfl,
      show plane292GenSourceLb (23 : Fin 28) = 12 from rfl]
  exact plane292GenSource0023
theorem plane292GenBound0024 :
    QuotientRankAtLeast (spanCodes (plane292GenSourceBasis (24 : Fin 28))) (plane292GenSourceLb (24 : Fin 28)) := by
  rw [show plane292GenSourceBasis (24 : Fin 28) = [258, 128, 66, 32, 10, 4, 1] from rfl,
      show plane292GenSourceLb (24 : Fin 28) = 12 from rfl]
  exact plane292GenSource0024
theorem plane292GenBound0025 :
    QuotientRankAtLeast (spanCodes (plane292GenSourceBasis (25 : Fin 28))) (plane292GenSourceLb (25 : Fin 28)) := by
  rw [show plane292GenSourceBasis (25 : Fin 28) = [258, 128, 64, 32, 10, 6, 1] from rfl,
      show plane292GenSourceLb (25 : Fin 28) = 12 from rfl]
  exact plane292GenSource0025
theorem plane292GenBound0026 :
    QuotientRankAtLeast (spanCodes (plane292GenSourceBasis (26 : Fin 28))) (plane292GenSourceLb (26 : Fin 28)) := by
  rw [show plane292GenSourceBasis (26 : Fin 28) = [258, 128, 64, 32, 10, 4, 1] from rfl,
      show plane292GenSourceLb (26 : Fin 28) = 12 from rfl]
  exact plane292GenSource0026
theorem plane292GenBound0027 :
    QuotientRankAtLeast (spanCodes (plane292GenSourceBasis (27 : Fin 28))) (plane292GenSourceLb (27 : Fin 28)) := by
  rw [show plane292GenSourceBasis (27 : Fin 28) = [258, 128, 66, 32, 16, 10, 6, 1] from rfl,
      show plane292GenSourceLb (27 : Fin 28) = 9 from rfl]
  exact plane292GenSource0027
end QiushiMatmul
