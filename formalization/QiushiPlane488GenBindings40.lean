import QiushiPlane488GenSources40
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane488GenBound0400 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (400 : Fin 413))) (plane488GenSourceLb (400 : Fin 413)) := by
  rw [show plane488GenSourceBasis (400 : Fin 413) = [256, 129, 65, 33, 16, 9, 5, 3] from rfl,
      show plane488GenSourceLb (400 : Fin 413) = 9 from rfl]
  exact plane488GenSource0400
theorem plane488GenBound0401 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (401 : Fin 413))) (plane488GenSourceLb (401 : Fin 413)) := by
  rw [show plane488GenSourceBasis (401 : Fin 413) = [256, 129, 64, 32, 17, 9, 5, 3] from rfl,
      show plane488GenSourceLb (401 : Fin 413) = 9 from rfl]
  exact plane488GenSource0401
theorem plane488GenBound0402 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (402 : Fin 413))) (plane488GenSourceLb (402 : Fin 413)) := by
  rw [show plane488GenSourceBasis (402 : Fin 413) = [257, 129, 64, 32, 17, 9, 5, 3] from rfl,
      show plane488GenSourceLb (402 : Fin 413) = 9 from rfl]
  exact plane488GenSource0402
theorem plane488GenBound0403 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (403 : Fin 413))) (plane488GenSourceLb (403 : Fin 413)) := by
  rw [show plane488GenSourceBasis (403 : Fin 413) = [257, 128, 64, 32, 16, 9, 5, 3] from rfl,
      show plane488GenSourceLb (403 : Fin 413) = 9 from rfl]
  exact plane488GenSource0403
theorem plane488GenBound0404 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (404 : Fin 413))) (plane488GenSourceLb (404 : Fin 413)) := by
  rw [show plane488GenSourceBasis (404 : Fin 413) = [256, 128, 65, 33, 17, 9, 4, 3] from rfl,
      show plane488GenSourceLb (404 : Fin 413) = 9 from rfl]
  exact plane488GenSource0404
theorem plane488GenBound0405 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (405 : Fin 413))) (plane488GenSourceLb (405 : Fin 413)) := by
  rw [show plane488GenSourceBasis (405 : Fin 413) = [257, 129, 64, 32, 16, 9, 4, 3] from rfl,
      show plane488GenSourceLb (405 : Fin 413) = 9 from rfl]
  exact plane488GenSource0405
theorem plane488GenBound0406 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (406 : Fin 413))) (plane488GenSourceLb (406 : Fin 413)) := by
  rw [show plane488GenSourceBasis (406 : Fin 413) = [257, 129, 65, 33, 17, 8, 5, 2] from rfl,
      show plane488GenSourceLb (406 : Fin 413) = 9 from rfl]
  exact plane488GenSource0406
theorem plane488GenBound0407 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (407 : Fin 413))) (plane488GenSourceLb (407 : Fin 413)) := by
  rw [show plane488GenSourceBasis (407 : Fin 413) = [257, 128, 64, 32, 17, 8, 5, 2] from rfl,
      show plane488GenSourceLb (407 : Fin 413) = 9 from rfl]
  exact plane488GenSource0407
theorem plane488GenBound0408 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (408 : Fin 413))) (plane488GenSourceLb (408 : Fin 413)) := by
  rw [show plane488GenSourceBasis (408 : Fin 413) = [257, 129, 64, 32, 17, 8, 4, 2] from rfl,
      show plane488GenSourceLb (408 : Fin 413) = 9 from rfl]
  exact plane488GenSource0408
theorem plane488GenBound0409 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (409 : Fin 413))) (plane488GenSourceLb (409 : Fin 413)) := by
  rw [show plane488GenSourceBasis (409 : Fin 413) = [256, 130, 64, 32, 18, 10, 6, 1] from rfl,
      show plane488GenSourceLb (409 : Fin 413) = 9 from rfl]
  exact plane488GenSource0409
end QiushiMatmul
