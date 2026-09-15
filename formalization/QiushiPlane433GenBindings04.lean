import QiushiPlane433GenSources04
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane433GenBound0040 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (40 : Fin 63))) (plane433GenSourceLb (40 : Fin 63)) := by
  rw [show plane433GenSourceBasis (40 : Fin 63) = [258, 128, 64, 16, 10, 1] from rfl,
      show plane433GenSourceLb (40 : Fin 63) = 15 from rfl]
  exact plane433GenSource0040
theorem plane433GenBound0041 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (41 : Fin 63))) (plane433GenSourceLb (41 : Fin 63)) := by
  rw [show plane433GenSourceBasis (41 : Fin 63) = [258, 128, 72, 42, 16, 1] from rfl,
      show plane433GenSourceLb (41 : Fin 63) = 15 from rfl]
  exact plane433GenSource0041
theorem plane433GenBound0042 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (42 : Fin 63))) (plane433GenSourceLb (42 : Fin 63)) := by
  rw [show plane433GenSourceBasis (42 : Fin 63) = [258, 136, 76, 34, 16, 1] from rfl,
      show plane433GenSourceLb (42 : Fin 63) = 15 from rfl]
  exact plane433GenSource0042
theorem plane433GenBound0043 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (43 : Fin 63))) (plane433GenSourceLb (43 : Fin 63)) := by
  rw [show plane433GenSourceBasis (43 : Fin 63) = [258, 194, 42, 16, 1] from rfl,
      show plane433GenSourceLb (43 : Fin 63) = 15 from rfl]
  exact plane433GenSource0043
theorem plane433GenBound0044 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (44 : Fin 63))) (plane433GenSourceLb (44 : Fin 63)) := by
  rw [show plane433GenSourceBasis (44 : Fin 63) = [256, 68, 16, 2, 1] from rfl,
      show plane433GenSourceLb (44 : Fin 63) = 14 from rfl]
  exact plane433GenSource0044
theorem plane433GenBound0045 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (45 : Fin 63))) (plane433GenSourceLb (45 : Fin 63)) := by
  rw [show plane433GenSourceBasis (45 : Fin 63) = [256, 160, 16, 2, 1] from rfl,
      show plane433GenSourceLb (45 : Fin 63) = 14 from rfl]
  exact plane433GenSource0045
theorem plane433GenBound0046 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (46 : Fin 63))) (plane433GenSourceLb (46 : Fin 63)) := by
  rw [show plane433GenSourceBasis (46 : Fin 63) = [258, 162, 16, 6, 1] from rfl,
      show plane433GenSourceLb (46 : Fin 63) = 14 from rfl]
  exact plane433GenSource0046
theorem plane433GenBound0047 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (47 : Fin 63))) (plane433GenSourceLb (47 : Fin 63)) := by
  rw [show plane433GenSourceBasis (47 : Fin 63) = [258, 130, 70, 16, 1] from rfl,
      show plane433GenSourceLb (47 : Fin 63) = 14 from rfl]
  exact plane433GenSource0047
theorem plane433GenBound0048 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (48 : Fin 63))) (plane433GenSourceLb (48 : Fin 63)) := by
  rw [show plane433GenSourceBasis (48 : Fin 63) = [258, 130, 106, 16, 1] from rfl,
      show plane433GenSourceLb (48 : Fin 63) = 14 from rfl]
  exact plane433GenSource0048
theorem plane433GenBound0049 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (49 : Fin 63))) (plane433GenSourceLb (49 : Fin 63)) := by
  rw [show plane433GenSourceBasis (49 : Fin 63) = [258, 130, 78, 34, 16, 1] from rfl,
      show plane433GenSourceLb (49 : Fin 63) = 14 from rfl]
  exact plane433GenSource0049
end QiushiMatmul
