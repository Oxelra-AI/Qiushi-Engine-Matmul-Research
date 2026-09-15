import QiushiPlane413GenSources01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane413GenBound0010 :
    QuotientRankAtLeast (spanCodes (plane413GenSourceBasis (10 : Fin 49))) (plane413GenSourceLb (10 : Fin 49)) := by
  rw [show plane413GenSourceBasis (10 : Fin 49) = [32, 24, 2, 1] from rfl,
      show plane413GenSourceLb (10 : Fin 49) = 15 from rfl]
  exact plane413GenSource0010
theorem plane413GenBound0011 :
    QuotientRankAtLeast (spanCodes (plane413GenSourceBasis (11 : Fin 49))) (plane413GenSourceLb (11 : Fin 49)) := by
  rw [show plane413GenSourceBasis (11 : Fin 49) = [32, 28, 2, 1] from rfl,
      show plane413GenSourceLb (11 : Fin 49) = 15 from rfl]
  exact plane413GenSource0011
theorem plane413GenBound0012 :
    QuotientRankAtLeast (spanCodes (plane413GenSourceBasis (12 : Fin 49))) (plane413GenSourceLb (12 : Fin 49)) := by
  rw [show plane413GenSourceBasis (12 : Fin 49) = [80, 32, 2, 1] from rfl,
      show plane413GenSourceLb (12 : Fin 49) = 15 from rfl]
  exact plane413GenSource0012
theorem plane413GenBound0013 :
    QuotientRankAtLeast (spanCodes (plane413GenSourceBasis (13 : Fin 49))) (plane413GenSourceLb (13 : Fin 49)) := by
  rw [show plane413GenSourceBasis (13 : Fin 49) = [68, 32, 16, 2, 1] from rfl,
      show plane413GenSourceLb (13 : Fin 49) = 15 from rfl]
  exact plane413GenSource0013
theorem plane413GenBound0014 :
    QuotientRankAtLeast (spanCodes (plane413GenSourceBasis (14 : Fin 49))) (plane413GenSourceLb (14 : Fin 49)) := by
  rw [show plane413GenSourceBasis (14 : Fin 49) = [88, 32, 2, 1] from rfl,
      show plane413GenSourceLb (14 : Fin 49) = 15 from rfl]
  exact plane413GenSource0014
theorem plane413GenBound0015 :
    QuotientRankAtLeast (spanCodes (plane413GenSourceBasis (15 : Fin 49))) (plane413GenSourceLb (15 : Fin 49)) := by
  rw [show plane413GenSourceBasis (15 : Fin 49) = [68, 32, 24, 2, 1] from rfl,
      show plane413GenSourceLb (15 : Fin 49) = 15 from rfl]
  exact plane413GenSource0015
theorem plane413GenBound0016 :
    QuotientRankAtLeast (spanCodes (plane413GenSourceBasis (16 : Fin 49))) (plane413GenSourceLb (16 : Fin 49)) := by
  rw [show plane413GenSourceBasis (16 : Fin 49) = [136, 32, 2, 1] from rfl,
      show plane413GenSourceLb (16 : Fin 49) = 15 from rfl]
  exact plane413GenSource0016
theorem plane413GenBound0017 :
    QuotientRankAtLeast (spanCodes (plane413GenSourceBasis (17 : Fin 49))) (plane413GenSourceLb (17 : Fin 49)) := by
  rw [show plane413GenSourceBasis (17 : Fin 49) = [132, 32, 8, 2, 1] from rfl,
      show plane413GenSourceLb (17 : Fin 49) = 15 from rfl]
  exact plane413GenSource0017
theorem plane413GenBound0018 :
    QuotientRankAtLeast (spanCodes (plane413GenSourceBasis (18 : Fin 49))) (plane413GenSourceLb (18 : Fin 49)) := by
  rw [show plane413GenSourceBasis (18 : Fin 49) = [152, 32, 2, 1] from rfl,
      show plane413GenSourceLb (18 : Fin 49) = 15 from rfl]
  exact plane413GenSource0018
theorem plane413GenBound0019 :
    QuotientRankAtLeast (spanCodes (plane413GenSourceBasis (19 : Fin 49))) (plane413GenSourceLb (19 : Fin 49)) := by
  rw [show plane413GenSourceBasis (19 : Fin 49) = [132, 32, 24, 2, 1] from rfl,
      show plane413GenSourceLb (19 : Fin 49) = 15 from rfl]
  exact plane413GenSource0019
end QiushiMatmul
