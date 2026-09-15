import QiushiPlane275GenSources02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane275GenBound0020 :
    QuotientRankAtLeast (spanCodes (plane275GenSourceBasis (20 : Fin 29))) (plane275GenSourceLb (20 : Fin 29)) := by
  rw [show plane275GenSourceBasis (20 : Fin 29) = [312, 160, 84, 2, 1] from rfl,
      show plane275GenSourceLb (20 : Fin 29) = 15 from rfl]
  exact plane275GenSource0020
theorem plane275GenBound0021 :
    QuotientRankAtLeast (spanCodes (plane275GenSourceBasis (21 : Fin 29))) (plane275GenSourceLb (21 : Fin 29)) := by
  rw [show plane275GenSourceBasis (21 : Fin 29) = [316, 160, 84, 2, 1] from rfl,
      show plane275GenSourceLb (21 : Fin 29) = 15 from rfl]
  exact plane275GenSource0021
theorem plane275GenBound0022 :
    QuotientRankAtLeast (spanCodes (plane275GenSourceBasis (22 : Fin 29))) (plane275GenSourceLb (22 : Fin 29)) := by
  rw [show plane275GenSourceBasis (22 : Fin 29) = [272, 160, 84, 2, 1] from rfl,
      show plane275GenSourceLb (22 : Fin 29) = 14 from rfl]
  exact plane275GenSource0022
theorem plane275GenBound0023 :
    QuotientRankAtLeast (spanCodes (plane275GenSourceBasis (23 : Fin 29))) (plane275GenSourceLb (23 : Fin 29)) := by
  rw [show plane275GenSourceBasis (23 : Fin 29) = [292, 160, 84, 2, 1] from rfl,
      show plane275GenSourceLb (23 : Fin 29) = 14 from rfl]
  exact plane275GenSource0023
theorem plane275GenBound0024 :
    QuotientRankAtLeast (spanCodes (plane275GenSourceBasis (24 : Fin 29))) (plane275GenSourceLb (24 : Fin 29)) := by
  rw [show plane275GenSourceBasis (24 : Fin 29) = [140, 72, 44, 28, 2, 1] from rfl,
      show plane275GenSourceLb (24 : Fin 29) = 12 from rfl]
  exact plane275GenSource0024
theorem plane275GenBound0025 :
    QuotientRankAtLeast (spanCodes (plane275GenSourceBasis (25 : Fin 29))) (plane275GenSourceLb (25 : Fin 29)) := by
  rw [show plane275GenSourceBasis (25 : Fin 29) = [128, 64, 32, 20, 2, 1] from rfl,
      show plane275GenSourceLb (25 : Fin 29) = 12 from rfl]
  exact plane275GenSource0025
theorem plane275GenBound0026 :
    QuotientRankAtLeast (spanCodes (plane275GenSourceBasis (26 : Fin 29))) (plane275GenSourceLb (26 : Fin 29)) := by
  rw [show plane275GenSourceBasis (26 : Fin 29) = [276, 148, 84, 52, 2, 1] from rfl,
      show plane275GenSourceLb (26 : Fin 29) = 12 from rfl]
  exact plane275GenSource0026
theorem plane275GenBound0027 :
    QuotientRankAtLeast (spanCodes (plane275GenSourceBasis (27 : Fin 29))) (plane275GenSourceLb (27 : Fin 29)) := by
  rw [show plane275GenSourceBasis (27 : Fin 29) = [288, 160, 80, 4, 2, 1] from rfl,
      show plane275GenSourceLb (27 : Fin 29) = 11 from rfl]
  exact plane275GenSource0027
theorem plane275GenBound0028 :
    QuotientRankAtLeast (spanCodes (plane275GenSourceBasis (28 : Fin 29))) (plane275GenSourceLb (28 : Fin 29)) := by
  rw [show plane275GenSourceBasis (28 : Fin 29) = [272, 128, 80, 32, 4, 2, 1] from rfl,
      show plane275GenSourceLb (28 : Fin 29) = 9 from rfl]
  exact plane275GenSource0028
end QiushiMatmul
