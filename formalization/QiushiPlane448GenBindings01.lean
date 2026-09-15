import QiushiPlane448GenSources01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane448GenBound0010 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (10 : Fin 56))) (plane448GenSourceLb (10 : Fin 56)) := by
  rw [show plane448GenSourceBasis (10 : Fin 56) = [268, 150, 54, 1] from rfl,
      show plane448GenSourceLb (10 : Fin 56) = 16 from rfl]
  exact plane448GenSource0010
theorem plane448GenBound0011 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (11 : Fin 56))) (plane448GenSourceLb (11 : Fin 56)) := by
  rw [show plane448GenSourceBasis (11 : Fin 56) = [258, 152, 56, 1] from rfl,
      show plane448GenSourceLb (11 : Fin 56) = 16 from rfl]
  exact plane448GenSource0011
theorem plane448GenBound0012 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (12 : Fin 56))) (plane448GenSourceLb (12 : Fin 56)) := by
  rw [show plane448GenSourceBasis (12 : Fin 56) = [258, 150, 54, 14, 1] from rfl,
      show plane448GenSourceLb (12 : Fin 56) = 16 from rfl]
  exact plane448GenSource0012
theorem plane448GenBound0013 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (13 : Fin 56))) (plane448GenSourceLb (13 : Fin 56)) := by
  rw [show plane448GenSourceBasis (13 : Fin 56) = [256, 154, 58, 1] from rfl,
      show plane448GenSourceLb (13 : Fin 56) = 16 from rfl]
  exact plane448GenSource0013
theorem plane448GenBound0014 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (14 : Fin 56))) (plane448GenSourceLb (14 : Fin 56)) := by
  rw [show plane448GenSourceBasis (14 : Fin 56) = [262, 156, 60, 1] from rfl,
      show plane448GenSourceLb (14 : Fin 56) = 16 from rfl]
  exact plane448GenSource0014
theorem plane448GenBound0015 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (15 : Fin 56))) (plane448GenSourceLb (15 : Fin 56)) := by
  rw [show plane448GenSourceBasis (15 : Fin 56) = [314, 160, 70, 1] from rfl,
      show plane448GenSourceLb (15 : Fin 56) = 16 from rfl]
  exact plane448GenSource0015
theorem plane448GenBound0016 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (16 : Fin 56))) (plane448GenSourceLb (16 : Fin 56)) := by
  rw [show plane448GenSourceBasis (16 : Fin 56) = [308, 160, 68, 14, 1] from rfl,
      show plane448GenSourceLb (16 : Fin 56) = 16 from rfl]
  exact plane448GenSource0016
theorem plane448GenBound0017 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (17 : Fin 56))) (plane448GenSourceLb (17 : Fin 56)) := by
  rw [show plane448GenSourceBasis (17 : Fin 56) = [314, 160, 76, 1] from rfl,
      show plane448GenSourceLb (17 : Fin 56) = 16 from rfl]
  exact plane448GenSource0017
theorem plane448GenBound0018 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (18 : Fin 56))) (plane448GenSourceLb (18 : Fin 56)) := by
  rw [show plane448GenSourceBasis (18 : Fin 56) = [308, 160, 66, 14, 1] from rfl,
      show plane448GenSourceLb (18 : Fin 56) = 16 from rfl]
  exact plane448GenSource0018
theorem plane448GenBound0019 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (19 : Fin 56))) (plane448GenSourceLb (19 : Fin 56)) := by
  rw [show plane448GenSourceBasis (19 : Fin 56) = [310, 160, 66, 12, 1] from rfl,
      show plane448GenSourceLb (19 : Fin 56) = 16 from rfl]
  exact plane448GenSource0019
end QiushiMatmul
