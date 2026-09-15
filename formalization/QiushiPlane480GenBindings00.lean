import QiushiPlane480GenSources00
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane480GenBound0000 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (0 : Fin 221))) (plane480GenSourceLb (0 : Fin 221)) := by
  rw [show plane480GenSourceBasis (0 : Fin 221) = [16, 10, 1] from rfl,
      show plane480GenSourceLb (0 : Fin 221) = 17 from rfl]
  exact plane480GenSource0000
theorem plane480GenBound0001 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (1 : Fin 221))) (plane480GenSourceLb (1 : Fin 221)) := by
  rw [show plane480GenSourceBasis (1 : Fin 221) = [16, 12, 1] from rfl,
      show plane480GenSourceLb (1 : Fin 221) = 17 from rfl]
  exact plane480GenSource0001
theorem plane480GenBound0002 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (2 : Fin 221))) (plane480GenSourceLb (2 : Fin 221)) := by
  rw [show plane480GenSourceBasis (2 : Fin 221) = [16, 14, 1] from rfl,
      show plane480GenSourceLb (2 : Fin 221) = 17 from rfl]
  exact plane480GenSource0002
theorem plane480GenBound0003 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (3 : Fin 221))) (plane480GenSourceLb (3 : Fin 221)) := by
  rw [show plane480GenSourceBasis (3 : Fin 221) = [34, 16, 1] from rfl,
      show plane480GenSourceLb (3 : Fin 221) = 17 from rfl]
  exact plane480GenSource0003
theorem plane480GenBound0004 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (4 : Fin 221))) (plane480GenSourceLb (4 : Fin 221)) := by
  rw [show plane480GenSourceBasis (4 : Fin 221) = [36, 16, 1] from rfl,
      show plane480GenSourceLb (4 : Fin 221) = 17 from rfl]
  exact plane480GenSource0004
theorem plane480GenBound0005 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (5 : Fin 221))) (plane480GenSourceLb (5 : Fin 221)) := by
  rw [show plane480GenSourceBasis (5 : Fin 221) = [38, 16, 1] from rfl,
      show plane480GenSourceLb (5 : Fin 221) = 17 from rfl]
  exact plane480GenSource0005
theorem plane480GenBound0006 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (6 : Fin 221))) (plane480GenSourceLb (6 : Fin 221)) := by
  rw [show plane480GenSourceBasis (6 : Fin 221) = [42, 16, 1] from rfl,
      show plane480GenSourceLb (6 : Fin 221) = 17 from rfl]
  exact plane480GenSource0006
theorem plane480GenBound0007 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (7 : Fin 221))) (plane480GenSourceLb (7 : Fin 221)) := by
  rw [show plane480GenSourceBasis (7 : Fin 221) = [44, 16, 1] from rfl,
      show plane480GenSourceLb (7 : Fin 221) = 17 from rfl]
  exact plane480GenSource0007
theorem plane480GenBound0008 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (8 : Fin 221))) (plane480GenSourceLb (8 : Fin 221)) := by
  rw [show plane480GenSourceBasis (8 : Fin 221) = [46, 16, 1] from rfl,
      show plane480GenSourceLb (8 : Fin 221) = 17 from rfl]
  exact plane480GenSource0008
theorem plane480GenBound0009 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (9 : Fin 221))) (plane480GenSourceLb (9 : Fin 221)) := by
  rw [show plane480GenSourceBasis (9 : Fin 221) = [66, 16, 1] from rfl,
      show plane480GenSourceLb (9 : Fin 221) = 17 from rfl]
  exact plane480GenSource0009
end QiushiMatmul
