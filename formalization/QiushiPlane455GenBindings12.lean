import QiushiPlane455GenSources12
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane455GenBound0120 :
    QuotientRankAtLeast (spanCodes (plane455GenSourceBasis (120 : Fin 124))) (plane455GenSourceLb (120 : Fin 124)) := by
  rw [show plane455GenSourceBasis (120 : Fin 124) = [256, 129, 64, 33, 16, 9, 4, 3] from rfl,
      show plane455GenSourceLb (120 : Fin 124) = 9 from rfl]
  exact plane455GenSource0120
theorem plane455GenBound0121 :
    QuotientRankAtLeast (spanCodes (plane455GenSourceBasis (121 : Fin 124))) (plane455GenSourceLb (121 : Fin 124)) := by
  rw [show plane455GenSourceBasis (121 : Fin 124) = [256, 129, 64, 32, 17, 9, 5, 3] from rfl,
      show plane455GenSourceLb (121 : Fin 124) = 9 from rfl]
  exact plane455GenSource0121
theorem plane455GenBound0122 :
    QuotientRankAtLeast (spanCodes (plane455GenSourceBasis (122 : Fin 124))) (plane455GenSourceLb (122 : Fin 124)) := by
  rw [show plane455GenSourceBasis (122 : Fin 124) = [257, 129, 64, 32, 17, 9, 5, 3] from rfl,
      show plane455GenSourceLb (122 : Fin 124) = 9 from rfl]
  exact plane455GenSource0122
theorem plane455GenBound0123 :
    QuotientRankAtLeast (spanCodes (plane455GenSourceBasis (123 : Fin 124))) (plane455GenSourceLb (123 : Fin 124)) := by
  rw [show plane455GenSourceBasis (123 : Fin 124) = [258, 128, 64, 32, 16, 10, 4, 1] from rfl,
      show plane455GenSourceLb (123 : Fin 124) = 9 from rfl]
  exact plane455GenSource0123
end QiushiMatmul
