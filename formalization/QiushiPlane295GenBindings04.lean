import QiushiPlane295GenSources04
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane295GenBound0040 :
    QuotientRankAtLeast (spanCodes (plane295GenSourceBasis (40 : Fin 46))) (plane295GenSourceLb (40 : Fin 46)) := by
  rw [show plane295GenSourceBasis (40 : Fin 46) = [256, 130, 68, 32, 16, 10, 1] from rfl,
      show plane295GenSourceLb (40 : Fin 46) = 12 from rfl]
  exact plane295GenSource0040
theorem plane295GenBound0041 :
    QuotientRankAtLeast (spanCodes (plane295GenSourceBasis (41 : Fin 46))) (plane295GenSourceLb (41 : Fin 46)) := by
  rw [show plane295GenSourceBasis (41 : Fin 46) = [272, 144, 64, 32, 10, 6, 1] from rfl,
      show plane295GenSourceLb (41 : Fin 46) = 12 from rfl]
  exact plane295GenSource0041
theorem plane295GenBound0042 :
    QuotientRankAtLeast (spanCodes (plane295GenSourceBasis (42 : Fin 46))) (plane295GenSourceLb (42 : Fin 46)) := by
  rw [show plane295GenSourceBasis (42 : Fin 46) = [256, 130, 64, 32, 16, 10, 6, 1] from rfl,
      show plane295GenSourceLb (42 : Fin 46) = 9 from rfl]
  exact plane295GenSource0042
theorem plane295GenBound0043 :
    QuotientRankAtLeast (spanCodes (plane295GenSourceBasis (43 : Fin 46))) (plane295GenSourceLb (43 : Fin 46)) := by
  rw [show plane295GenSourceBasis (43 : Fin 46) = [258, 128, 64, 32, 18, 10, 6, 1] from rfl,
      show plane295GenSourceLb (43 : Fin 46) = 9 from rfl]
  exact plane295GenSource0043
theorem plane295GenBound0044 :
    QuotientRankAtLeast (spanCodes (plane295GenSourceBasis (44 : Fin 46))) (plane295GenSourceLb (44 : Fin 46)) := by
  rw [show plane295GenSourceBasis (44 : Fin 46) = [258, 130, 66, 32, 18, 10, 6, 1] from rfl,
      show plane295GenSourceLb (44 : Fin 46) = 9 from rfl]
  exact plane295GenSource0044
theorem plane295GenBound0045 :
    QuotientRankAtLeast (spanCodes (plane295GenSourceBasis (45 : Fin 46))) (plane295GenSourceLb (45 : Fin 46)) := by
  rw [show plane295GenSourceBasis (45 : Fin 46) = [256, 130, 66, 32, 16, 10, 6, 1] from rfl,
      show plane295GenSourceLb (45 : Fin 46) = 9 from rfl]
  exact plane295GenSource0045
end QiushiMatmul
