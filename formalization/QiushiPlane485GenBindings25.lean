import QiushiPlane485GenSources25
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane485GenBound0250 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (250 : Fin 421))) (plane485GenSourceLb (250 : Fin 421)) := by
  rw [show plane485GenSourceBasis (250 : Fin 421) = [256, 160, 65, 17, 10, 5] from rfl,
      show plane485GenSourceLb (250 : Fin 421) = 15 from rfl]
  exact plane485GenSource0250
theorem plane485GenBound0251 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (251 : Fin 421))) (plane485GenSourceLb (251 : Fin 421)) := by
  rw [show plane485GenSourceBasis (251 : Fin 421) = [256, 134, 71, 36, 20, 10] from rfl,
      show plane485GenSourceLb (251 : Fin 421) = 15 from rfl]
  exact plane485GenSource0251
theorem plane485GenBound0252 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (252 : Fin 421))) (plane485GenSourceLb (252 : Fin 421)) := by
  rw [show plane485GenSourceBasis (252 : Fin 421) = [260, 135, 65, 39, 20, 10] from rfl,
      show plane485GenSourceLb (252 : Fin 421) = 15 from rfl]
  exact plane485GenSource0252
theorem plane485GenBound0253 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (253 : Fin 421))) (plane485GenSourceLb (253 : Fin 421)) := by
  rw [show plane485GenSourceBasis (253 : Fin 421) = [260, 130, 67, 32, 20, 10] from rfl,
      show plane485GenSourceLb (253 : Fin 421) = 15 from rfl]
  exact plane485GenSource0253
theorem plane485GenBound0254 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (254 : Fin 421))) (plane485GenSourceLb (254 : Fin 421)) := by
  rw [show plane485GenSourceBasis (254 : Fin 421) = [256, 133, 66, 34, 20, 10] from rfl,
      show plane485GenSourceLb (254 : Fin 421) = 15 from rfl]
  exact plane485GenSource0254
theorem plane485GenBound0255 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (255 : Fin 421))) (plane485GenSourceLb (255 : Fin 421)) := by
  rw [show plane485GenSourceBasis (255 : Fin 421) = [257, 160, 64, 16, 10, 4] from rfl,
      show plane485GenSourceLb (255 : Fin 421) = 15 from rfl]
  exact plane485GenSource0255
theorem plane485GenBound0256 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (256 : Fin 421))) (plane485GenSourceLb (256 : Fin 421)) := by
  rw [show plane485GenSourceBasis (256 : Fin 421) = [291, 160, 97, 19, 10, 7] from rfl,
      show plane485GenSourceLb (256 : Fin 421) = 15 from rfl]
  exact plane485GenSource0256
theorem plane485GenBound0257 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (257 : Fin 421))) (plane485GenSourceLb (257 : Fin 421)) := by
  rw [show plane485GenSourceBasis (257 : Fin 421) = [288, 134, 66, 20, 10, 1] from rfl,
      show plane485GenSourceLb (257 : Fin 421) = 15 from rfl]
  exact plane485GenSource0257
theorem plane485GenBound0258 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (258 : Fin 421))) (plane485GenSourceLb (258 : Fin 421)) := by
  rw [show plane485GenSourceBasis (258 : Fin 421) = [450, 32, 18, 10, 6, 1] from rfl,
      show plane485GenSourceLb (258 : Fin 421) = 15 from rfl]
  exact plane485GenSource0258
theorem plane485GenBound0259 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (259 : Fin 421))) (plane485GenSourceLb (259 : Fin 421)) := by
  rw [show plane485GenSourceBasis (259 : Fin 421) = [261, 197, 38, 20, 10] from rfl,
      show plane485GenSourceLb (259 : Fin 421) = 15 from rfl]
  exact plane485GenSource0259
end QiushiMatmul
