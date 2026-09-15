import QiushiPlane485GenSources40
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane485GenBound0400 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (400 : Fin 421))) (plane485GenSourceLb (400 : Fin 421)) := by
  rw [show plane485GenSourceBasis (400 : Fin 421) = [256, 128, 66, 32, 18, 10, 6, 1] from rfl,
      show plane485GenSourceLb (400 : Fin 421) = 9 from rfl]
  exact plane485GenSource0400
theorem plane485GenBound0401 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (401 : Fin 421))) (plane485GenSourceLb (401 : Fin 421)) := by
  rw [show plane485GenSourceBasis (401 : Fin 421) = [258, 128, 66, 34, 18, 10, 6, 1] from rfl,
      show plane485GenSourceLb (401 : Fin 421) = 9 from rfl]
  exact plane485GenSource0401
theorem plane485GenBound0402 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (402 : Fin 421))) (plane485GenSourceLb (402 : Fin 421)) := by
  rw [show plane485GenSourceBasis (402 : Fin 421) = [256, 130, 66, 34, 18, 10, 6, 1] from rfl,
      show plane485GenSourceLb (402 : Fin 421) = 9 from rfl]
  exact plane485GenSource0402
theorem plane485GenBound0403 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (403 : Fin 421))) (plane485GenSourceLb (403 : Fin 421)) := by
  rw [show plane485GenSourceBasis (403 : Fin 421) = [256, 129, 64, 33, 16, 8, 4, 2] from rfl,
      show plane485GenSourceLb (403 : Fin 421) = 9 from rfl]
  exact plane485GenSource0403
theorem plane485GenBound0404 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (404 : Fin 421))) (plane485GenSourceLb (404 : Fin 421)) := by
  rw [show plane485GenSourceBasis (404 : Fin 421) = [257, 129, 65, 33, 16, 8, 4, 2] from rfl,
      show plane485GenSourceLb (404 : Fin 421) = 9 from rfl]
  exact plane485GenSource0404
theorem plane485GenBound0405 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (405 : Fin 421))) (plane485GenSourceLb (405 : Fin 421)) := by
  rw [show plane485GenSourceBasis (405 : Fin 421) = [257, 128, 64, 32, 17, 8, 5, 2] from rfl,
      show plane485GenSourceLb (405 : Fin 421) = 9 from rfl]
  exact plane485GenSource0405
theorem plane485GenBound0406 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (406 : Fin 421))) (plane485GenSourceLb (406 : Fin 421)) := by
  rw [show plane485GenSourceBasis (406 : Fin 421) = [257, 129, 64, 32, 17, 9, 5, 3] from rfl,
      show plane485GenSourceLb (406 : Fin 421) = 9 from rfl]
  exact plane485GenSource0406
theorem plane485GenBound0407 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (407 : Fin 421))) (plane485GenSourceLb (407 : Fin 421)) := by
  rw [show plane485GenSourceBasis (407 : Fin 421) = [257, 128, 65, 32, 17, 9, 5, 3] from rfl,
      show plane485GenSourceLb (407 : Fin 421) = 9 from rfl]
  exact plane485GenSource0407
theorem plane485GenBound0408 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (408 : Fin 421))) (plane485GenSourceLb (408 : Fin 421)) := by
  rw [show plane485GenSourceBasis (408 : Fin 421) = [256, 128, 65, 32, 17, 9, 5, 3] from rfl,
      show plane485GenSourceLb (408 : Fin 421) = 9 from rfl]
  exact plane485GenSource0408
theorem plane485GenBound0409 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (409 : Fin 421))) (plane485GenSourceLb (409 : Fin 421)) := by
  rw [show plane485GenSourceBasis (409 : Fin 421) = [256, 129, 64, 32, 17, 9, 5, 3] from rfl,
      show plane485GenSourceLb (409 : Fin 421) = 9 from rfl]
  exact plane485GenSource0409
end QiushiMatmul
