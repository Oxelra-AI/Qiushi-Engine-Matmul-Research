import QiushiPlane485GenSources32
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane485GenBound0320 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (320 : Fin 421))) (plane485GenSourceLb (320 : Fin 421)) := by
  rw [show plane485GenSourceBasis (320 : Fin 421) = [256, 130, 64, 32, 18, 10, 6] from rfl,
      show plane485GenSourceLb (320 : Fin 421) = 12 from rfl]
  exact plane485GenSource0320
theorem plane485GenBound0321 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (321 : Fin 421))) (plane485GenSourceLb (321 : Fin 421)) := by
  rw [show plane485GenSourceBasis (321 : Fin 421) = [256, 128, 66, 32, 18, 10, 6] from rfl,
      show plane485GenSourceLb (321 : Fin 421) = 12 from rfl]
  exact plane485GenSource0321
theorem plane485GenBound0322 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (322 : Fin 421))) (plane485GenSourceLb (322 : Fin 421)) := by
  rw [show plane485GenSourceBasis (322 : Fin 421) = [258, 130, 64, 35, 19, 10, 7] from rfl,
      show plane485GenSourceLb (322 : Fin 421) = 12 from rfl]
  exact plane485GenSource0322
theorem plane485GenBound0323 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (323 : Fin 421))) (plane485GenSourceLb (323 : Fin 421)) := by
  rw [show plane485GenSourceBasis (323 : Fin 421) = [258, 131, 65, 35, 19, 10, 7] from rfl,
      show plane485GenSourceLb (323 : Fin 421) = 12 from rfl]
  exact plane485GenSource0323
theorem plane485GenBound0324 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (324 : Fin 421))) (plane485GenSourceLb (324 : Fin 421)) := by
  rw [show plane485GenSourceBasis (324 : Fin 421) = [256, 130, 66, 35, 19, 10, 7] from rfl,
      show plane485GenSourceLb (324 : Fin 421) = 12 from rfl]
  exact plane485GenSource0324
theorem plane485GenBound0325 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (325 : Fin 421))) (plane485GenSourceLb (325 : Fin 421)) := by
  rw [show plane485GenSourceBasis (325 : Fin 421) = [256, 131, 67, 33, 16, 10, 4] from rfl,
      show plane485GenSourceLb (325 : Fin 421) = 12 from rfl]
  exact plane485GenSource0325
theorem plane485GenBound0326 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (326 : Fin 421))) (plane485GenSourceLb (326 : Fin 421)) := by
  rw [show plane485GenSourceBasis (326 : Fin 421) = [258, 130, 65, 32, 16, 10, 4] from rfl,
      show plane485GenSourceLb (326 : Fin 421) = 12 from rfl]
  exact plane485GenSource0326
theorem plane485GenBound0327 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (327 : Fin 421))) (plane485GenSourceLb (327 : Fin 421)) := by
  rw [show plane485GenSourceBasis (327 : Fin 421) = [258, 128, 67, 32, 16, 10, 4] from rfl,
      show plane485GenSourceLb (327 : Fin 421) = 12 from rfl]
  exact plane485GenSource0327
theorem plane485GenBound0328 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (328 : Fin 421))) (plane485GenSourceLb (328 : Fin 421)) := by
  rw [show plane485GenSourceBasis (328 : Fin 421) = [257, 130, 64, 34, 16, 10, 4] from rfl,
      show plane485GenSourceLb (328 : Fin 421) = 12 from rfl]
  exact plane485GenSource0328
theorem plane485GenBound0329 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (329 : Fin 421))) (plane485GenSourceLb (329 : Fin 421)) := by
  rw [show plane485GenSourceBasis (329 : Fin 421) = [256, 129, 66, 34, 16, 10, 4] from rfl,
      show plane485GenSourceLb (329 : Fin 421) = 12 from rfl]
  exact plane485GenSource0329
end QiushiMatmul
