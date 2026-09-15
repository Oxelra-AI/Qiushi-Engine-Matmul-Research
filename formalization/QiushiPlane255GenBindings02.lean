import QiushiPlane255GenSources02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane255GenBound0020 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (20 : Fin 25))) (plane255GenSourceLb (20 : Fin 25)) := by
  rw [show plane255GenSourceBasis (20 : Fin 25) = [388, 68, 36, 20, 8, 2, 1] from rfl,
      show plane255GenSourceLb (20 : Fin 25) = 12 from rfl]
  exact plane255GenSource0020
theorem plane255GenBound0021 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (21 : Fin 25))) (plane255GenSourceLb (21 : Fin 25)) := by
  rw [show plane255GenSourceBasis (21 : Fin 25) = [260, 132, 64, 32, 8, 2, 1] from rfl,
      show plane255GenSourceLb (21 : Fin 25) = 9 from rfl]
  exact plane255GenSource0021
theorem plane255GenBound0022 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (22 : Fin 25))) (plane255GenSourceLb (22 : Fin 25)) := by
  rw [show plane255GenSourceBasis (22 : Fin 25) = [256, 132, 64, 32, 8, 2, 1] from rfl,
      show plane255GenSourceLb (22 : Fin 25) = 9 from rfl]
  exact plane255GenSource0022
theorem plane255GenBound0023 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (23 : Fin 25))) (plane255GenSourceLb (23 : Fin 25)) := by
  rw [show plane255GenSourceBasis (23 : Fin 25) = [260, 148, 64, 32, 8, 2, 1] from rfl,
      show plane255GenSourceLb (23 : Fin 25) = 9 from rfl]
  exact plane255GenSource0023
theorem plane255GenBound0024 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (24 : Fin 25))) (plane255GenSourceLb (24 : Fin 25)) := by
  rw [show plane255GenSourceBasis (24 : Fin 25) = [256, 148, 64, 32, 8, 2, 1] from rfl,
      show plane255GenSourceLb (24 : Fin 25) = 9 from rfl]
  exact plane255GenSource0024
end QiushiMatmul
