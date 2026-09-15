import QiushiPlane480GenSources20
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane480GenBound0200 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (200 : Fin 221))) (plane480GenSourceLb (200 : Fin 221)) := by
  rw [show plane480GenSourceBasis (200 : Fin 221) = [256, 142, 72, 40, 16, 1] from rfl,
      show plane480GenSourceLb (200 : Fin 221) = 12 from rfl]
  exact plane480GenSource0200
theorem plane480GenBound0201 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (201 : Fin 221))) (plane480GenSourceLb (201 : Fin 221)) := by
  rw [show plane480GenSourceBasis (201 : Fin 221) = [264, 142, 64, 40, 16, 1] from rfl,
      show plane480GenSourceLb (201 : Fin 221) = 12 from rfl]
  exact plane480GenSource0201
theorem plane480GenBound0202 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (202 : Fin 221))) (plane480GenSourceLb (202 : Fin 221)) := by
  rw [show plane480GenSourceBasis (202 : Fin 221) = [264, 142, 72, 32, 16, 1] from rfl,
      show plane480GenSourceLb (202 : Fin 221) = 12 from rfl]
  exact plane480GenSource0202
theorem plane480GenBound0203 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (203 : Fin 221))) (plane480GenSourceLb (203 : Fin 221)) := by
  rw [show plane480GenSourceBasis (203 : Fin 221) = [256, 142, 64, 32, 16, 1] from rfl,
      show plane480GenSourceLb (203 : Fin 221) = 12 from rfl]
  exact plane480GenSource0203
theorem plane480GenBound0204 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (204 : Fin 221))) (plane480GenSourceLb (204 : Fin 221)) := by
  rw [show plane480GenSourceBasis (204 : Fin 221) = [258, 130, 70, 34, 16, 10, 1] from rfl,
      show plane480GenSourceLb (204 : Fin 221) = 12 from rfl]
  exact plane480GenSource0204
theorem plane480GenBound0205 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (205 : Fin 221))) (plane480GenSourceLb (205 : Fin 221)) := by
  rw [show plane480GenSourceBasis (205 : Fin 221) = [256, 130, 68, 34, 16, 10, 1] from rfl,
      show plane480GenSourceLb (205 : Fin 221) = 12 from rfl]
  exact plane480GenSource0205
theorem plane480GenBound0206 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (206 : Fin 221))) (plane480GenSourceLb (206 : Fin 221)) := by
  rw [show plane480GenSourceBasis (206 : Fin 221) = [256, 128, 68, 32, 16, 10, 1] from rfl,
      show plane480GenSourceLb (206 : Fin 221) = 12 from rfl]
  exact plane480GenSource0206
theorem plane480GenBound0207 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (207 : Fin 221))) (plane480GenSourceLb (207 : Fin 221)) := by
  rw [show plane480GenSourceBasis (207 : Fin 221) = [260, 162, 64, 16, 8, 1] from rfl,
      show plane480GenSourceLb (207 : Fin 221) = 12 from rfl]
  exact plane480GenSource0207
theorem plane480GenBound0208 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (208 : Fin 221))) (plane480GenSourceLb (208 : Fin 221)) := by
  rw [show plane480GenSourceBasis (208 : Fin 221) = [384, 70, 32, 16, 8, 1] from rfl,
      show plane480GenSourceLb (208 : Fin 221) = 12 from rfl]
  exact plane480GenSource0208
theorem plane480GenBound0209 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (209 : Fin 221))) (plane480GenSourceLb (209 : Fin 221)) := by
  rw [show plane480GenSourceBasis (209 : Fin 221) = [258, 128, 106, 16, 6, 1] from rfl,
      show plane480GenSourceLb (209 : Fin 221) = 12 from rfl]
  exact plane480GenSource0209
end QiushiMatmul
