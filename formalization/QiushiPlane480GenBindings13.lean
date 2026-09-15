import QiushiPlane480GenSources13
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane480GenBound0130 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (130 : Fin 221))) (plane480GenSourceLb (130 : Fin 221)) := by
  rw [show plane480GenSourceBasis (130 : Fin 221) = [32, 16, 2, 1] from rfl,
      show plane480GenSourceLb (130 : Fin 221) = 15 from rfl]
  exact plane480GenSource0130
theorem plane480GenBound0131 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (131 : Fin 221))) (plane480GenSourceLb (131 : Fin 221)) := by
  rw [show plane480GenSourceBasis (131 : Fin 221) = [32, 16, 4, 1] from rfl,
      show plane480GenSourceLb (131 : Fin 221) = 15 from rfl]
  exact plane480GenSource0131
theorem plane480GenBound0132 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (132 : Fin 221))) (plane480GenSourceLb (132 : Fin 221)) := by
  rw [show plane480GenSourceBasis (132 : Fin 221) = [32, 16, 6, 1] from rfl,
      show plane480GenSourceLb (132 : Fin 221) = 15 from rfl]
  exact plane480GenSource0132
theorem plane480GenBound0133 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (133 : Fin 221))) (plane480GenSourceLb (133 : Fin 221)) := by
  rw [show plane480GenSourceBasis (133 : Fin 221) = [40, 16, 2, 1] from rfl,
      show plane480GenSourceLb (133 : Fin 221) = 15 from rfl]
  exact plane480GenSource0133
theorem plane480GenBound0134 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (134 : Fin 221))) (plane480GenSourceLb (134 : Fin 221)) := by
  rw [show plane480GenSourceBasis (134 : Fin 221) = [40, 16, 4, 1] from rfl,
      show plane480GenSourceLb (134 : Fin 221) = 15 from rfl]
  exact plane480GenSource0134
theorem plane480GenBound0135 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (135 : Fin 221))) (plane480GenSourceLb (135 : Fin 221)) := by
  rw [show plane480GenSourceBasis (135 : Fin 221) = [40, 16, 6, 1] from rfl,
      show plane480GenSourceLb (135 : Fin 221) = 15 from rfl]
  exact plane480GenSource0135
theorem plane480GenBound0136 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (136 : Fin 221))) (plane480GenSourceLb (136 : Fin 221)) := by
  rw [show plane480GenSourceBasis (136 : Fin 221) = [64, 16, 2, 1] from rfl,
      show plane480GenSourceLb (136 : Fin 221) = 15 from rfl]
  exact plane480GenSource0136
theorem plane480GenBound0137 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (137 : Fin 221))) (plane480GenSourceLb (137 : Fin 221)) := by
  rw [show plane480GenSourceBasis (137 : Fin 221) = [72, 16, 2, 1] from rfl,
      show plane480GenSourceLb (137 : Fin 221) = 15 from rfl]
  exact plane480GenSource0137
theorem plane480GenBound0138 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (138 : Fin 221))) (plane480GenSourceLb (138 : Fin 221)) := by
  rw [show plane480GenSourceBasis (138 : Fin 221) = [128, 16, 8, 1] from rfl,
      show plane480GenSourceLb (138 : Fin 221) = 15 from rfl]
  exact plane480GenSource0138
theorem plane480GenBound0139 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (139 : Fin 221))) (plane480GenSourceLb (139 : Fin 221)) := by
  rw [show plane480GenSourceBasis (139 : Fin 221) = [130, 16, 8, 1] from rfl,
      show plane480GenSourceLb (139 : Fin 221) = 15 from rfl]
  exact plane480GenSource0139
end QiushiMatmul
