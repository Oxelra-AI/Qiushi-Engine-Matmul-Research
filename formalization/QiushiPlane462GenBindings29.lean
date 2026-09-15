import QiushiPlane462GenSources29
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane462GenBound0290 :
    QuotientRankAtLeast (spanCodes (plane462GenSourceBasis (290 : Fin 294))) (plane462GenSourceLb (290 : Fin 294)) := by
  rw [show plane462GenSourceBasis (290 : Fin 294) = [258, 130, 64, 34, 18, 10, 4, 1] from rfl,
      show plane462GenSourceLb (290 : Fin 294) = 9 from rfl]
  exact plane462GenSource0290
theorem plane462GenBound0291 :
    QuotientRankAtLeast (spanCodes (plane462GenSourceBasis (291 : Fin 294))) (plane462GenSourceLb (291 : Fin 294)) := by
  rw [show plane462GenSourceBasis (291 : Fin 294) = [258, 130, 64, 32, 16, 10, 4, 1] from rfl,
      show plane462GenSourceLb (291 : Fin 294) = 9 from rfl]
  exact plane462GenSource0291
theorem plane462GenBound0292 :
    QuotientRankAtLeast (spanCodes (plane462GenSourceBasis (292 : Fin 294))) (plane462GenSourceLb (292 : Fin 294)) := by
  rw [show plane462GenSourceBasis (292 : Fin 294) = [260, 128, 68, 36, 20, 8, 2, 1] from rfl,
      show plane462GenSourceLb (292 : Fin 294) = 9 from rfl]
  exact plane462GenSource0292
theorem plane462GenBound0293 :
    QuotientRankAtLeast (spanCodes (plane462GenSourceBasis (293 : Fin 294))) (plane462GenSourceLb (293 : Fin 294)) := by
  rw [show plane462GenSourceBasis (293 : Fin 294) = [256, 132, 68, 32, 20, 8, 2, 1] from rfl,
      show plane462GenSourceLb (293 : Fin 294) = 9 from rfl]
  exact plane462GenSource0293
end QiushiMatmul
