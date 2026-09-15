import QiushiPlane448GenSources04
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane448GenBound0040 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (40 : Fin 56))) (plane448GenSourceLb (40 : Fin 56)) := by
  rw [show plane448GenSourceBasis (40 : Fin 56) = [294, 160, 18, 14, 1] from rfl,
      show plane448GenSourceLb (40 : Fin 56) = 15 from rfl]
  exact plane448GenSource0040
theorem plane448GenBound0041 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (41 : Fin 56))) (plane448GenSourceLb (41 : Fin 56)) := by
  rw [show plane448GenSourceBasis (41 : Fin 56) = [292, 160, 72, 30, 1] from rfl,
      show plane448GenSourceLb (41 : Fin 56) = 15 from rfl]
  exact plane448GenSource0041
theorem plane448GenBound0042 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (42 : Fin 56))) (plane448GenSourceLb (42 : Fin 56)) := by
  rw [show plane448GenSourceBasis (42 : Fin 56) = [314, 160, 82, 4, 1] from rfl,
      show plane448GenSourceLb (42 : Fin 56) = 15 from rfl]
  exact plane448GenSource0042
theorem plane448GenBound0043 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (43 : Fin 56))) (plane448GenSourceLb (43 : Fin 56)) := by
  rw [show plane448GenSourceBasis (43 : Fin 56) = [292, 160, 68, 30, 1] from rfl,
      show plane448GenSourceLb (43 : Fin 56) = 15 from rfl]
  exact plane448GenSource0043
theorem plane448GenBound0044 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (44 : Fin 56))) (plane448GenSourceLb (44 : Fin 56)) := by
  rw [show plane448GenSourceBasis (44 : Fin 56) = [288, 160, 70, 26, 1] from rfl,
      show plane448GenSourceLb (44 : Fin 56) = 15 from rfl]
  exact plane448GenSource0044
theorem plane448GenBound0045 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (45 : Fin 56))) (plane448GenSourceLb (45 : Fin 56)) := by
  rw [show plane448GenSourceBasis (45 : Fin 56) = [314, 160, 90, 6, 1] from rfl,
      show plane448GenSourceLb (45 : Fin 56) = 15 from rfl]
  exact plane448GenSource0045
theorem plane448GenBound0046 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (46 : Fin 56))) (plane448GenSourceLb (46 : Fin 56)) := by
  rw [show plane448GenSourceBasis (46 : Fin 56) = [290, 160, 18, 10, 6, 1] from rfl,
      show plane448GenSourceLb (46 : Fin 56) = 14 from rfl]
  exact plane448GenSource0046
theorem plane448GenBound0047 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (47 : Fin 56))) (plane448GenSourceLb (47 : Fin 56)) := by
  rw [show plane448GenSourceBasis (47 : Fin 56) = [294, 160, 70, 18, 14, 1] from rfl,
      show plane448GenSourceLb (47 : Fin 56) = 14 from rfl]
  exact plane448GenSource0047
theorem plane448GenBound0048 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (48 : Fin 56))) (plane448GenSourceLb (48 : Fin 56)) := by
  rw [show plane448GenSourceBasis (48 : Fin 56) = [270, 140, 74, 44, 24, 1] from rfl,
      show plane448GenSourceLb (48 : Fin 56) = 14 from rfl]
  exact plane448GenSource0048
theorem plane448GenBound0049 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (49 : Fin 56))) (plane448GenSourceLb (49 : Fin 56)) := by
  rw [show plane448GenSourceBasis (49 : Fin 56) = [274, 128, 66, 32, 8, 4, 1] from rfl,
      show plane448GenSourceLb (49 : Fin 56) = 12 from rfl]
  exact plane448GenSource0049
end QiushiMatmul
