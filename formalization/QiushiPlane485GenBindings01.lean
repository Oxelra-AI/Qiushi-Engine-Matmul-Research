import QiushiPlane485GenSources01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane485GenBound0010 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (10 : Fin 421))) (plane485GenSourceLb (10 : Fin 421)) := by
  rw [show plane485GenSourceBasis (10 : Fin 421) = [100, 20, 10] from rfl,
      show plane485GenSourceLb (10 : Fin 421) = 18 from rfl]
  exact plane485GenSource0010
theorem plane485GenBound0011 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (11 : Fin 421))) (plane485GenSourceLb (11 : Fin 421)) := by
  rw [show plane485GenSourceBasis (11 : Fin 421) = [101, 20, 10] from rfl,
      show plane485GenSourceLb (11 : Fin 421) = 18 from rfl]
  exact plane485GenSource0011
theorem plane485GenBound0012 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (12 : Fin 421))) (plane485GenSourceLb (12 : Fin 421)) := by
  rw [show plane485GenSourceBasis (12 : Fin 421) = [102, 20, 10] from rfl,
      show plane485GenSourceLb (12 : Fin 421) = 18 from rfl]
  exact plane485GenSource0012
theorem plane485GenBound0013 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (13 : Fin 421))) (plane485GenSourceLb (13 : Fin 421)) := by
  rw [show plane485GenSourceBasis (13 : Fin 421) = [103, 20, 10] from rfl,
      show plane485GenSourceLb (13 : Fin 421) = 18 from rfl]
  exact plane485GenSource0013
theorem plane485GenBound0014 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (14 : Fin 421))) (plane485GenSourceLb (14 : Fin 421)) := by
  rw [show plane485GenSourceBasis (14 : Fin 421) = [129, 20, 10] from rfl,
      show plane485GenSourceLb (14 : Fin 421) = 18 from rfl]
  exact plane485GenSource0014
theorem plane485GenBound0015 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (15 : Fin 421))) (plane485GenSourceLb (15 : Fin 421)) := by
  rw [show plane485GenSourceBasis (15 : Fin 421) = [131, 20, 10] from rfl,
      show plane485GenSourceLb (15 : Fin 421) = 18 from rfl]
  exact plane485GenSource0015
theorem plane485GenBound0016 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (16 : Fin 421))) (plane485GenSourceLb (16 : Fin 421)) := by
  rw [show plane485GenSourceBasis (16 : Fin 421) = [133, 20, 10] from rfl,
      show plane485GenSourceLb (16 : Fin 421) = 18 from rfl]
  exact plane485GenSource0016
theorem plane485GenBound0017 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (17 : Fin 421))) (plane485GenSourceLb (17 : Fin 421)) := by
  rw [show plane485GenSourceBasis (17 : Fin 421) = [135, 20, 10] from rfl,
      show plane485GenSourceLb (17 : Fin 421) = 18 from rfl]
  exact plane485GenSource0017
theorem plane485GenBound0018 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (18 : Fin 421))) (plane485GenSourceLb (18 : Fin 421)) := by
  rw [show plane485GenSourceBasis (18 : Fin 421) = [160, 20, 10] from rfl,
      show plane485GenSourceLb (18 : Fin 421) = 18 from rfl]
  exact plane485GenSource0018
theorem plane485GenBound0019 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (19 : Fin 421))) (plane485GenSourceLb (19 : Fin 421)) := by
  rw [show plane485GenSourceBasis (19 : Fin 421) = [161, 20, 10] from rfl,
      show plane485GenSourceLb (19 : Fin 421) = 18 from rfl]
  exact plane485GenSource0019
end QiushiMatmul
