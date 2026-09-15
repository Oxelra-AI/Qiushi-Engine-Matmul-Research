import QiushiPlane298GenSources02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane298GenBound0020 :
    QuotientRankAtLeast (spanCodes (plane298GenSourceBasis (20 : Fin 28))) (plane298GenSourceLb (20 : Fin 28)) := by
  rw [show plane298GenSourceBasis (20 : Fin 28) = [384, 64, 32, 10, 1] from rfl,
      show plane298GenSourceLb (20 : Fin 28) = 14 from rfl]
  exact plane298GenSource0020
theorem plane298GenBound0021 :
    QuotientRankAtLeast (spanCodes (plane298GenSourceBasis (21 : Fin 28))) (plane298GenSourceLb (21 : Fin 28)) := by
  rw [show plane298GenSourceBasis (21 : Fin 28) = [256, 128, 32, 10, 1] from rfl,
      show plane298GenSourceLb (21 : Fin 28) = 14 from rfl]
  exact plane298GenSource0021
theorem plane298GenBound0022 :
    QuotientRankAtLeast (spanCodes (plane298GenSourceBasis (22 : Fin 28))) (plane298GenSourceLb (22 : Fin 28)) := by
  rw [show plane298GenSourceBasis (22 : Fin 28) = [384, 32, 18, 10, 4, 1] from rfl,
      show plane298GenSourceLb (22 : Fin 28) = 12 from rfl]
  exact plane298GenSource0022
theorem plane298GenBound0023 :
    QuotientRankAtLeast (spanCodes (plane298GenSourceBasis (23 : Fin 28))) (plane298GenSourceLb (23 : Fin 28)) := by
  rw [show plane298GenSourceBasis (23 : Fin 28) = [384, 66, 32, 18, 10, 6, 1] from rfl,
      show plane298GenSourceLb (23 : Fin 28) = 12 from rfl]
  exact plane298GenSource0023
theorem plane298GenBound0024 :
    QuotientRankAtLeast (spanCodes (plane298GenSourceBasis (24 : Fin 28))) (plane298GenSourceLb (24 : Fin 28)) := by
  rw [show plane298GenSourceBasis (24 : Fin 28) = [258, 130, 66, 32, 10, 4, 1] from rfl,
      show plane298GenSourceLb (24 : Fin 28) = 12 from rfl]
  exact plane298GenSource0024
theorem plane298GenBound0025 :
    QuotientRankAtLeast (spanCodes (plane298GenSourceBasis (25 : Fin 28))) (plane298GenSourceLb (25 : Fin 28)) := by
  rw [show plane298GenSourceBasis (25 : Fin 28) = [258, 130, 64, 32, 10, 4, 1] from rfl,
      show plane298GenSourceLb (25 : Fin 28) = 12 from rfl]
  exact plane298GenSource0025
theorem plane298GenBound0026 :
    QuotientRankAtLeast (spanCodes (plane298GenSourceBasis (26 : Fin 28))) (plane298GenSourceLb (26 : Fin 28)) := by
  rw [show plane298GenSourceBasis (26 : Fin 28) = [260, 132, 80, 32, 8, 2, 1] from rfl,
      show plane298GenSourceLb (26 : Fin 28) = 12 from rfl]
  exact plane298GenSource0026
theorem plane298GenBound0027 :
    QuotientRankAtLeast (spanCodes (plane298GenSourceBasis (27 : Fin 28))) (plane298GenSourceLb (27 : Fin 28)) := by
  rw [show plane298GenSourceBasis (27 : Fin 28) = [260, 132, 68, 32, 20, 8, 2, 1] from rfl,
      show plane298GenSourceLb (27 : Fin 28) = 9 from rfl]
  exact plane298GenSource0027
end QiushiMatmul
