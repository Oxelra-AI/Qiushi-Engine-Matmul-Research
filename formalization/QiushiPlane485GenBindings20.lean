import QiushiPlane485GenSources20
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane485GenBound0200 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (200 : Fin 421))) (plane485GenSourceLb (200 : Fin 421)) := by
  rw [show plane485GenSourceBasis (200 : Fin 421) = [288, 128, 98, 17, 10, 5] from rfl,
      show plane485GenSourceLb (200 : Fin 421) = 15 from rfl]
  exact plane485GenSource0200
theorem plane485GenBound0201 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (201 : Fin 421))) (plane485GenSourceLb (201 : Fin 421)) := by
  rw [show plane485GenSourceBasis (201 : Fin 421) = [289, 160, 66, 16, 10, 4] from rfl,
      show plane485GenSourceLb (201 : Fin 421) = 15 from rfl]
  exact plane485GenSource0201
theorem plane485GenBound0202 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (202 : Fin 421))) (plane485GenSourceLb (202 : Fin 421)) := by
  rw [show plane485GenSourceBasis (202 : Fin 421) = [259, 160, 96, 16, 10, 4] from rfl,
      show plane485GenSourceLb (202 : Fin 421) = 15 from rfl]
  exact plane485GenSource0202
theorem plane485GenBound0203 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (203 : Fin 421))) (plane485GenSourceLb (203 : Fin 421)) := by
  rw [show plane485GenSourceBasis (203 : Fin 421) = [256, 160, 100, 20, 9, 3] from rfl,
      show plane485GenSourceLb (203 : Fin 421) = 15 from rfl]
  exact plane485GenSource0203
theorem plane485GenBound0204 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (204 : Fin 421))) (plane485GenSourceLb (204 : Fin 421)) := by
  rw [show plane485GenSourceBasis (204 : Fin 421) = [288, 133, 96, 20, 8, 2] from rfl,
      show plane485GenSourceLb (204 : Fin 421) = 15 from rfl]
  exact plane485GenSource0204
theorem plane485GenBound0205 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (205 : Fin 421))) (plane485GenSourceLb (205 : Fin 421)) := by
  rw [show plane485GenSourceBasis (205 : Fin 421) = [292, 164, 70, 20, 10, 1] from rfl,
      show plane485GenSourceLb (205 : Fin 421) = 15 from rfl]
  exact plane485GenSource0205
theorem plane485GenBound0206 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (206 : Fin 421))) (plane485GenSourceLb (206 : Fin 421)) := by
  rw [show plane485GenSourceBasis (206 : Fin 421) = [288, 160, 70, 20, 10, 1] from rfl,
      show plane485GenSourceLb (206 : Fin 421) = 15 from rfl]
  exact plane485GenSource0206
theorem plane485GenBound0207 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (207 : Fin 421))) (plane485GenSourceLb (207 : Fin 421)) := by
  rw [show plane485GenSourceBasis (207 : Fin 421) = [262, 128, 64, 20, 10, 1] from rfl,
      show plane485GenSourceLb (207 : Fin 421) = 15 from rfl]
  exact plane485GenSource0207
theorem plane485GenBound0208 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (208 : Fin 421))) (plane485GenSourceLb (208 : Fin 421)) := by
  rw [show plane485GenSourceBasis (208 : Fin 421) = [262, 135, 65, 32, 20, 10] from rfl,
      show plane485GenSourceLb (208 : Fin 421) = 15 from rfl]
  exact plane485GenSource0208
theorem plane485GenBound0209 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (209 : Fin 421))) (plane485GenSourceLb (209 : Fin 421)) := by
  rw [show plane485GenSourceBasis (209 : Fin 421) = [262, 133, 67, 32, 20, 10] from rfl,
      show plane485GenSourceLb (209 : Fin 421) = 15 from rfl]
  exact plane485GenSource0209
end QiushiMatmul
