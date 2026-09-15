import QiushiPlane480GenSources16
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane480GenBound0160 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (160 : Fin 221))) (plane480GenSourceLb (160 : Fin 221)) := by
  rw [show plane480GenSourceBasis (160 : Fin 221) = [290, 128, 98, 16, 6, 1] from rfl,
      show plane480GenSourceLb (160 : Fin 221) = 12 from rfl]
  exact plane480GenSource0160
theorem plane480GenBound0161 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (161 : Fin 221))) (plane480GenSourceLb (161 : Fin 221)) := by
  rw [show plane480GenSourceBasis (161 : Fin 221) = [290, 130, 98, 16, 4, 1] from rfl,
      show plane480GenSourceLb (161 : Fin 221) = 12 from rfl]
  exact plane480GenSource0161
theorem plane480GenBound0162 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (162 : Fin 221))) (plane480GenSourceLb (162 : Fin 221)) := by
  rw [show plane480GenSourceBasis (162 : Fin 221) = [288, 128, 98, 16, 4, 1] from rfl,
      show plane480GenSourceLb (162 : Fin 221) = 12 from rfl]
  exact plane480GenSource0162
theorem plane480GenBound0163 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (163 : Fin 221))) (plane480GenSourceLb (163 : Fin 221)) := by
  rw [show plane480GenSourceBasis (163 : Fin 221) = [256, 128, 68, 16, 2, 1] from rfl,
      show plane480GenSourceLb (163 : Fin 221) = 12 from rfl]
  exact plane480GenSource0163
theorem plane480GenBound0164 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (164 : Fin 221))) (plane480GenSourceLb (164 : Fin 221)) := by
  rw [show plane480GenSourceBasis (164 : Fin 221) = [360, 168, 16, 4, 2, 1] from rfl,
      show plane480GenSourceLb (164 : Fin 221) = 12 from rfl]
  exact plane480GenSource0164
theorem plane480GenBound0165 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (165 : Fin 221))) (plane480GenSourceLb (165 : Fin 221)) := by
  rw [show plane480GenSourceBasis (165 : Fin 221) = [288, 160, 64, 16, 8, 1] from rfl,
      show plane480GenSourceLb (165 : Fin 221) = 12 from rfl]
  exact plane480GenSource0165
theorem plane480GenBound0166 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (166 : Fin 221))) (plane480GenSourceLb (166 : Fin 221)) := by
  rw [show plane480GenSourceBasis (166 : Fin 221) = [292, 132, 96, 16, 8, 2, 1] from rfl,
      show plane480GenSourceLb (166 : Fin 221) = 12 from rfl]
  exact plane480GenSource0166
theorem plane480GenBound0167 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (167 : Fin 221))) (plane480GenSourceLb (167 : Fin 221)) := by
  rw [show plane480GenSourceBasis (167 : Fin 221) = [288, 160, 66, 16, 10, 4, 1] from rfl,
      show plane480GenSourceLb (167 : Fin 221) = 12 from rfl]
  exact plane480GenSource0167
theorem plane480GenBound0168 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (168 : Fin 221))) (plane480GenSourceLb (168 : Fin 221)) := by
  rw [show plane480GenSourceBasis (168 : Fin 221) = [288, 160, 64, 16, 10, 6, 1] from rfl,
      show plane480GenSourceLb (168 : Fin 221) = 12 from rfl]
  exact plane480GenSource0168
theorem plane480GenBound0169 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (169 : Fin 221))) (plane480GenSourceLb (169 : Fin 221)) := by
  rw [show plane480GenSourceBasis (169 : Fin 221) = [290, 162, 64, 16, 10, 6, 1] from rfl,
      show plane480GenSourceLb (169 : Fin 221) = 12 from rfl]
  exact plane480GenSource0169
end QiushiMatmul
