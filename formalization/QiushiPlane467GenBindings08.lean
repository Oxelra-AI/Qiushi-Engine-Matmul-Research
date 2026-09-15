import QiushiPlane467GenSources08
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane467GenBound0080 :
    QuotientRankAtLeast (spanCodes (plane467GenSourceBasis (80 : Fin 84))) (plane467GenSourceLb (80 : Fin 84)) := by
  rw [show plane467GenSourceBasis (80 : Fin 84) = [258, 128, 64, 34, 16, 10, 4, 1] from rfl,
      show plane467GenSourceLb (80 : Fin 84) = 9 from rfl]
  exact plane467GenSource0080
theorem plane467GenBound0081 :
    QuotientRankAtLeast (spanCodes (plane467GenSourceBasis (81 : Fin 84))) (plane467GenSourceLb (81 : Fin 84)) := by
  rw [show plane467GenSourceBasis (81 : Fin 84) = [256, 128, 66, 34, 16, 10, 6, 1] from rfl,
      show plane467GenSourceLb (81 : Fin 84) = 9 from rfl]
  exact plane467GenSource0081
theorem plane467GenBound0082 :
    QuotientRankAtLeast (spanCodes (plane467GenSourceBasis (82 : Fin 84))) (plane467GenSourceLb (82 : Fin 84)) := by
  rw [show plane467GenSourceBasis (82 : Fin 84) = [256, 130, 66, 32, 16, 10, 6, 1] from rfl,
      show plane467GenSourceLb (82 : Fin 84) = 9 from rfl]
  exact plane467GenSource0082
theorem plane467GenBound0083 :
    QuotientRankAtLeast (spanCodes (plane467GenSourceBasis (83 : Fin 84))) (plane467GenSourceLb (83 : Fin 84)) := by
  rw [show plane467GenSourceBasis (83 : Fin 84) = [258, 130, 64, 32, 16, 10, 4, 1] from rfl,
      show plane467GenSourceLb (83 : Fin 84) = 9 from rfl]
  exact plane467GenSource0083
end QiushiMatmul
