import QiushiPlane480GenSources14
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane480GenBound0140 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (140 : Fin 221))) (plane480GenSourceLb (140 : Fin 221)) := by
  rw [show plane480GenSourceBasis (140 : Fin 221) = [128, 64, 16, 1] from rfl,
      show plane480GenSourceLb (140 : Fin 221) = 15 from rfl]
  exact plane480GenSource0140
theorem plane480GenBound0141 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (141 : Fin 221))) (plane480GenSourceLb (141 : Fin 221)) := by
  rw [show plane480GenSourceBasis (141 : Fin 221) = [130, 64, 16, 1] from rfl,
      show plane480GenSourceLb (141 : Fin 221) = 15 from rfl]
  exact plane480GenSource0141
theorem plane480GenBound0142 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (142 : Fin 221))) (plane480GenSourceLb (142 : Fin 221)) := by
  rw [show plane480GenSourceBasis (142 : Fin 221) = [128, 72, 16, 1] from rfl,
      show plane480GenSourceLb (142 : Fin 221) = 15 from rfl]
  exact plane480GenSource0142
theorem plane480GenBound0143 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (143 : Fin 221))) (plane480GenSourceLb (143 : Fin 221)) := by
  rw [show plane480GenSourceBasis (143 : Fin 221) = [130, 72, 16, 1] from rfl,
      show plane480GenSourceLb (143 : Fin 221) = 15 from rfl]
  exact plane480GenSource0143
theorem plane480GenBound0144 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (144 : Fin 221))) (plane480GenSourceLb (144 : Fin 221)) := by
  rw [show plane480GenSourceBasis (144 : Fin 221) = [260, 130, 70, 16, 1] from rfl,
      show plane480GenSourceLb (144 : Fin 221) = 14 from rfl]
  exact plane480GenSource0144
theorem plane480GenBound0145 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (145 : Fin 221))) (plane480GenSourceLb (145 : Fin 221)) := by
  rw [show plane480GenSourceBasis (145 : Fin 221) = [256, 32, 16, 4, 1] from rfl,
      show plane480GenSourceLb (145 : Fin 221) = 12 from rfl]
  exact plane480GenSource0145
theorem plane480GenBound0146 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (146 : Fin 221))) (plane480GenSourceLb (146 : Fin 221)) := by
  rw [show plane480GenSourceBasis (146 : Fin 221) = [260, 68, 32, 16, 8, 1] from rfl,
      show plane480GenSourceLb (146 : Fin 221) = 12 from rfl]
  exact plane480GenSource0146
theorem plane480GenBound0147 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (147 : Fin 221))) (plane480GenSourceLb (147 : Fin 221)) := by
  rw [show plane480GenSourceBasis (147 : Fin 221) = [256, 68, 32, 16, 8, 1] from rfl,
      show plane480GenSourceLb (147 : Fin 221) = 12 from rfl]
  exact plane480GenSource0147
theorem plane480GenBound0148 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (148 : Fin 221))) (plane480GenSourceLb (148 : Fin 221)) := by
  rw [show plane480GenSourceBasis (148 : Fin 221) = [320, 40, 16, 4, 1] from rfl,
      show plane480GenSourceLb (148 : Fin 221) = 12 from rfl]
  exact plane480GenSource0148
theorem plane480GenBound0149 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (149 : Fin 221))) (plane480GenSourceLb (149 : Fin 221)) := by
  rw [show plane480GenSourceBasis (149 : Fin 221) = [288, 160, 16, 4, 2, 1] from rfl,
      show plane480GenSourceLb (149 : Fin 221) = 12 from rfl]
  exact plane480GenSource0149
end QiushiMatmul
