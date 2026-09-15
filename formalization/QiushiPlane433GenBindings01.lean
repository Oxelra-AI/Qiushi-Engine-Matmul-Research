import QiushiPlane433GenSources01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane433GenBound0010 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (10 : Fin 63))) (plane433GenSourceLb (10 : Fin 63)) := by
  rw [show plane433GenSourceBasis (10 : Fin 63) = [258, 74, 42, 16, 1] from rfl,
      show plane433GenSourceLb (10 : Fin 63) = 16 from rfl]
  exact plane433GenSource0010
theorem plane433GenBound0011 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (11 : Fin 63))) (plane433GenSourceLb (11 : Fin 63)) := by
  rw [show plane433GenSourceBasis (11 : Fin 63) = [258, 100, 16, 1] from rfl,
      show plane433GenSourceLb (11 : Fin 63) = 16 from rfl]
  exact plane433GenSource0011
theorem plane433GenBound0012 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (12 : Fin 63))) (plane433GenSourceLb (12 : Fin 63)) := by
  rw [show plane433GenSourceBasis (12 : Fin 63) = [258, 102, 16, 1] from rfl,
      show plane433GenSourceLb (12 : Fin 63) = 16 from rfl]
  exact plane433GenSource0012
theorem plane433GenBound0013 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (13 : Fin 63))) (plane433GenSourceLb (13 : Fin 63)) := by
  rw [show plane433GenSourceBasis (13 : Fin 63) = [258, 128, 16, 1] from rfl,
      show plane433GenSourceLb (13 : Fin 63) = 16 from rfl]
  exact plane433GenSource0013
theorem plane433GenBound0014 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (14 : Fin 63))) (plane433GenSourceLb (14 : Fin 63)) := by
  rw [show plane433GenSourceBasis (14 : Fin 63) = [258, 136, 16, 1] from rfl,
      show plane433GenSourceLb (14 : Fin 63) = 16 from rfl]
  exact plane433GenSource0014
theorem plane433GenBound0015 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (15 : Fin 63))) (plane433GenSourceLb (15 : Fin 63)) := by
  rw [show plane433GenSourceBasis (15 : Fin 63) = [258, 134, 16, 14, 1] from rfl,
      show plane433GenSourceLb (15 : Fin 63) = 16 from rfl]
  exact plane433GenSource0015
theorem plane433GenBound0016 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (16 : Fin 63))) (plane433GenSourceLb (16 : Fin 63)) := by
  rw [show plane433GenSourceBasis (16 : Fin 63) = [258, 138, 16, 1] from rfl,
      show plane433GenSourceLb (16 : Fin 63) = 16 from rfl]
  exact plane433GenSource0016
theorem plane433GenBound0017 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (17 : Fin 63))) (plane433GenSourceLb (17 : Fin 63)) := by
  rw [show plane433GenSourceBasis (17 : Fin 63) = [258, 160, 16, 1] from rfl,
      show plane433GenSourceLb (17 : Fin 63) = 16 from rfl]
  exact plane433GenSource0017
theorem plane433GenBound0018 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (18 : Fin 63))) (plane433GenSourceLb (18 : Fin 63)) := by
  rw [show plane433GenSourceBasis (18 : Fin 63) = [258, 166, 16, 1] from rfl,
      show plane433GenSourceLb (18 : Fin 63) = 16 from rfl]
  exact plane433GenSource0018
theorem plane433GenBound0019 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (19 : Fin 63))) (plane433GenSourceLb (19 : Fin 63)) := by
  rw [show plane433GenSourceBasis (19 : Fin 63) = [258, 168, 16, 1] from rfl,
      show plane433GenSourceLb (19 : Fin 63) = 16 from rfl]
  exact plane433GenSource0019
end QiushiMatmul
