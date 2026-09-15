import QiushiPlane475GenSources12
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane475GenBound0120 :
    QuotientRankAtLeast (spanCodes (plane475GenSourceBasis (120 : Fin 126))) (plane475GenSourceLb (120 : Fin 126)) := by
  rw [show plane475GenSourceBasis (120 : Fin 126) = [256, 130, 66, 34, 18, 10, 4, 1] from rfl,
      show plane475GenSourceLb (120 : Fin 126) = 9 from rfl]
  exact plane475GenSource0120
theorem plane475GenBound0121 :
    QuotientRankAtLeast (spanCodes (plane475GenSourceBasis (121 : Fin 126))) (plane475GenSourceLb (121 : Fin 126)) := by
  rw [show plane475GenSourceBasis (121 : Fin 126) = [258, 128, 66, 34, 18, 10, 6, 1] from rfl,
      show plane475GenSourceLb (121 : Fin 126) = 9 from rfl]
  exact plane475GenSource0121
theorem plane475GenBound0122 :
    QuotientRankAtLeast (spanCodes (plane475GenSourceBasis (122 : Fin 126))) (plane475GenSourceLb (122 : Fin 126)) := by
  rw [show plane475GenSourceBasis (122 : Fin 126) = [257, 128, 65, 33, 17, 9, 4, 3] from rfl,
      show plane475GenSourceLb (122 : Fin 126) = 9 from rfl]
  exact plane475GenSource0122
theorem plane475GenBound0123 :
    QuotientRankAtLeast (spanCodes (plane475GenSourceBasis (123 : Fin 126))) (plane475GenSourceLb (123 : Fin 126)) := by
  rw [show plane475GenSourceBasis (123 : Fin 126) = [256, 129, 65, 33, 16, 9, 5, 3] from rfl,
      show plane475GenSourceLb (123 : Fin 126) = 9 from rfl]
  exact plane475GenSource0123
theorem plane475GenBound0124 :
    QuotientRankAtLeast (spanCodes (plane475GenSourceBasis (124 : Fin 126))) (plane475GenSourceLb (124 : Fin 126)) := by
  rw [show plane475GenSourceBasis (124 : Fin 126) = [256, 128, 65, 33, 17, 9, 4, 3] from rfl,
      show plane475GenSourceLb (124 : Fin 126) = 9 from rfl]
  exact plane475GenSource0124
theorem plane475GenBound0125 :
    QuotientRankAtLeast (spanCodes (plane475GenSourceBasis (125 : Fin 126))) (plane475GenSourceLb (125 : Fin 126)) := by
  rw [show plane475GenSourceBasis (125 : Fin 126) = [257, 128, 64, 32, 17, 8, 5, 2] from rfl,
      show plane475GenSourceLb (125 : Fin 126) = 9 from rfl]
  exact plane475GenSource0125
end QiushiMatmul
