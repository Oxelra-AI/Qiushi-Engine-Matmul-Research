import QiushiPlane255GenSources01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane255GenBound0010 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (10 : Fin 25))) (plane255GenSourceLb (10 : Fin 25)) := by
  rw [show plane255GenSourceBasis (10 : Fin 25) = [164, 96, 8, 2, 1] from rfl,
      show plane255GenSourceLb (10 : Fin 25) = 15 from rfl]
  exact plane255GenSource0010
theorem plane255GenBound0011 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (11 : Fin 25))) (plane255GenSourceLb (11 : Fin 25)) := by
  rw [show plane255GenSourceBasis (11 : Fin 25) = [176, 96, 8, 2, 1] from rfl,
      show plane255GenSourceLb (11 : Fin 25) = 15 from rfl]
  exact plane255GenSource0011
theorem plane255GenBound0012 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (12 : Fin 25))) (plane255GenSourceLb (12 : Fin 25)) := by
  rw [show plane255GenSourceBasis (12 : Fin 25) = [180, 96, 8, 2, 1] from rfl,
      show plane255GenSourceLb (12 : Fin 25) = 15 from rfl]
  exact plane255GenSource0012
theorem plane255GenBound0013 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (13 : Fin 25))) (plane255GenSourceLb (13 : Fin 25)) := by
  rw [show plane255GenSourceBasis (13 : Fin 25) = [272, 96, 8, 2, 1] from rfl,
      show plane255GenSourceLb (13 : Fin 25) = 15 from rfl]
  exact plane255GenSource0013
theorem plane255GenBound0014 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (14 : Fin 25))) (plane255GenSourceLb (14 : Fin 25)) := by
  rw [show plane255GenSourceBasis (14 : Fin 25) = [276, 96, 8, 2, 1] from rfl,
      show plane255GenSourceLb (14 : Fin 25) = 15 from rfl]
  exact plane255GenSource0014
theorem plane255GenBound0015 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (15 : Fin 25))) (plane255GenSourceLb (15 : Fin 25)) := by
  rw [show plane255GenSourceBasis (15 : Fin 25) = [304, 96, 8, 2, 1] from rfl,
      show plane255GenSourceLb (15 : Fin 25) = 15 from rfl]
  exact plane255GenSource0015
theorem plane255GenBound0016 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (16 : Fin 25))) (plane255GenSourceLb (16 : Fin 25)) := by
  rw [show plane255GenSourceBasis (16 : Fin 25) = [308, 96, 8, 2, 1] from rfl,
      show plane255GenSourceLb (16 : Fin 25) = 15 from rfl]
  exact plane255GenSource0016
theorem plane255GenBound0017 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (17 : Fin 25))) (plane255GenSourceLb (17 : Fin 25)) := by
  rw [show plane255GenSourceBasis (17 : Fin 25) = [256, 96, 8, 4, 2, 1] from rfl,
      show plane255GenSourceLb (17 : Fin 25) = 12 from rfl]
  exact plane255GenSource0017
theorem plane255GenBound0018 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (18 : Fin 25))) (plane255GenSourceLb (18 : Fin 25)) := by
  rw [show plane255GenSourceBasis (18 : Fin 25) = [288, 96, 8, 4, 2, 1] from rfl,
      show plane255GenSourceLb (18 : Fin 25) = 12 from rfl]
  exact plane255GenSource0018
theorem plane255GenBound0019 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (19 : Fin 25))) (plane255GenSourceLb (19 : Fin 25)) := by
  rw [show plane255GenSourceBasis (19 : Fin 25) = [384, 68, 36, 20, 8, 2, 1] from rfl,
      show plane255GenSourceLb (19 : Fin 25) = 12 from rfl]
  exact plane255GenSource0019
end QiushiMatmul
