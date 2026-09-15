import QiushiPlane471GenSources30
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane471GenBound0300 :
    QuotientRankAtLeast (spanCodes (plane471GenSourceBasis (300 : Fin 304))) (plane471GenSourceLb (300 : Fin 304)) := by
  rw [show plane471GenSourceBasis (300 : Fin 304) = [258, 128, 64, 34, 18, 10, 6, 1] from rfl,
      show plane471GenSourceLb (300 : Fin 304) = 9 from rfl]
  exact plane471GenSource0300
theorem plane471GenBound0301 :
    QuotientRankAtLeast (spanCodes (plane471GenSourceBasis (301 : Fin 304))) (plane471GenSourceLb (301 : Fin 304)) := by
  rw [show plane471GenSourceBasis (301 : Fin 304) = [256, 130, 64, 32, 18, 10, 6, 1] from rfl,
      show plane471GenSourceLb (301 : Fin 304) = 9 from rfl]
  exact plane471GenSource0301
theorem plane471GenBound0302 :
    QuotientRankAtLeast (spanCodes (plane471GenSourceBasis (302 : Fin 304))) (plane471GenSourceLb (302 : Fin 304)) := by
  rw [show plane471GenSourceBasis (302 : Fin 304) = [258, 128, 64, 34, 16, 10, 4, 1] from rfl,
      show plane471GenSourceLb (302 : Fin 304) = 9 from rfl]
  exact plane471GenSource0302
theorem plane471GenBound0303 :
    QuotientRankAtLeast (spanCodes (plane471GenSourceBasis (303 : Fin 304))) (plane471GenSourceLb (303 : Fin 304)) := by
  rw [show plane471GenSourceBasis (303 : Fin 304) = [289, 84, 10] from rfl,
      show plane471GenSourceLb (303 : Fin 304) = 17 from rfl]
  exact plane471GenSource0303
end QiushiMatmul
