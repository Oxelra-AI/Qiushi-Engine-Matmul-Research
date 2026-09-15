import QiushiPlane152GenSources01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane152GenBound0010 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (10 : Fin 16))) (plane152GenSourceLb (10 : Fin 16)) := by
  rw [show plane152GenSourceBasis (10 : Fin 16) = [256, 128, 66, 34, 16, 10, 6, 1] from rfl,
      show plane152GenSourceLb (10 : Fin 16) = 9 from rfl]
  exact plane152GenSource0010
theorem plane152GenBound0011 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (11 : Fin 16))) (plane152GenSourceLb (11 : Fin 16)) := by
  rw [show plane152GenSourceBasis (11 : Fin 16) = [256, 130, 64, 32, 16, 10, 6, 1] from rfl,
      show plane152GenSourceLb (11 : Fin 16) = 9 from rfl]
  exact plane152GenSource0011
theorem plane152GenBound0012 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (12 : Fin 16))) (plane152GenSourceLb (12 : Fin 16)) := by
  rw [show plane152GenSourceBasis (12 : Fin 16) = [258, 128, 64, 32, 16, 10, 4, 1] from rfl,
      show plane152GenSourceLb (12 : Fin 16) = 9 from rfl]
  exact plane152GenSource0012
theorem plane152GenBound0013 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (13 : Fin 16))) (plane152GenSourceLb (13 : Fin 16)) := by
  rw [show plane152GenSourceBasis (13 : Fin 16) = [258, 130, 66, 34, 16, 10, 4, 1] from rfl,
      show plane152GenSourceLb (13 : Fin 16) = 6 from rfl]
  exact plane152GenSource0013
theorem plane152GenBound0014 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (14 : Fin 16))) (plane152GenSourceLb (14 : Fin 16)) := by
  rw [show plane152GenSourceBasis (14 : Fin 16) = [258, 130, 64, 32, 16, 10, 6, 1] from rfl,
      show plane152GenSourceLb (14 : Fin 16) = 6 from rfl]
  exact plane152GenSource0014
theorem plane152GenBound0015 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (15 : Fin 16))) (plane152GenSourceLb (15 : Fin 16)) := by
  rw [show plane152GenSourceBasis (15 : Fin 16) = [258, 128, 66, 34, 16, 10, 6, 1] from rfl,
      show plane152GenSourceLb (15 : Fin 16) = 6 from rfl]
  exact plane152GenSource0015
end QiushiMatmul
