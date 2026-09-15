import QiushiPlane480GenSources15
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane480GenBound0150 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (150 : Fin 221))) (plane480GenSourceLb (150 : Fin 221)) := by
  rw [show plane480GenSourceBasis (150 : Fin 221) = [384, 32, 16, 6, 1] from rfl,
      show plane480GenSourceLb (150 : Fin 221) = 12 from rfl]
  exact plane480GenSource0150
theorem plane480GenBound0151 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (151 : Fin 221))) (plane480GenSourceLb (151 : Fin 221)) := by
  rw [show plane480GenSourceBasis (151 : Fin 221) = [256, 160, 16, 4, 2, 1] from rfl,
      show plane480GenSourceLb (151 : Fin 221) = 12 from rfl]
  exact plane480GenSource0151
theorem plane480GenBound0152 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (152 : Fin 221))) (plane480GenSourceLb (152 : Fin 221)) := by
  rw [show plane480GenSourceBasis (152 : Fin 221) = [256, 128, 64, 16, 1] from rfl,
      show plane480GenSourceLb (152 : Fin 221) = 12 from rfl]
  exact plane480GenSource0152
theorem plane480GenBound0153 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (153 : Fin 221))) (plane480GenSourceLb (153 : Fin 221)) := by
  rw [show plane480GenSourceBasis (153 : Fin 221) = [260, 128, 68, 16, 2, 1] from rfl,
      show plane480GenSourceLb (153 : Fin 221) = 12 from rfl]
  exact plane480GenSource0153
theorem plane480GenBound0154 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (154 : Fin 221))) (plane480GenSourceLb (154 : Fin 221)) := by
  rw [show plane480GenSourceBasis (154 : Fin 221) = [290, 128, 98, 16, 4, 1] from rfl,
      show plane480GenSourceLb (154 : Fin 221) = 12 from rfl]
  exact plane480GenSource0154
theorem plane480GenBound0155 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (155 : Fin 221))) (plane480GenSourceLb (155 : Fin 221)) := by
  rw [show plane480GenSourceBasis (155 : Fin 221) = [288, 130, 98, 16, 4, 1] from rfl,
      show plane480GenSourceLb (155 : Fin 221) = 12 from rfl]
  exact plane480GenSource0155
theorem plane480GenBound0156 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (156 : Fin 221))) (plane480GenSourceLb (156 : Fin 221)) := by
  rw [show plane480GenSourceBasis (156 : Fin 221) = [288, 128, 98, 16, 6, 1] from rfl,
      show plane480GenSourceLb (156 : Fin 221) = 12 from rfl]
  exact plane480GenSource0156
theorem plane480GenBound0157 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (157 : Fin 221))) (plane480GenSourceLb (157 : Fin 221)) := by
  rw [show plane480GenSourceBasis (157 : Fin 221) = [290, 130, 98, 16, 6, 1] from rfl,
      show plane480GenSourceLb (157 : Fin 221) = 12 from rfl]
  exact plane480GenSource0157
theorem plane480GenBound0158 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (158 : Fin 221))) (plane480GenSourceLb (158 : Fin 221)) := by
  rw [show plane480GenSourceBasis (158 : Fin 221) = [260, 130, 64, 16, 1] from rfl,
      show plane480GenSourceLb (158 : Fin 221) = 12 from rfl]
  exact plane480GenSource0158
theorem plane480GenBound0159 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (159 : Fin 221))) (plane480GenSourceLb (159 : Fin 221)) := by
  rw [show plane480GenSourceBasis (159 : Fin 221) = [288, 130, 98, 16, 6, 1] from rfl,
      show plane480GenSourceLb (159 : Fin 221) = 12 from rfl]
  exact plane480GenSource0159
end QiushiMatmul
