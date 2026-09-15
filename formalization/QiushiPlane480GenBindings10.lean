import QiushiPlane480GenSources10
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane480GenBound0100 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (100 : Fin 221))) (plane480GenSourceLb (100 : Fin 221)) := by
  rw [show plane480GenSourceBasis (100 : Fin 221) = [492, 16, 1] from rfl,
      show plane480GenSourceLb (100 : Fin 221) = 17 from rfl]
  exact plane480GenSource0100
theorem plane480GenBound0101 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (101 : Fin 221))) (plane480GenSourceLb (101 : Fin 221)) := by
  rw [show plane480GenSourceBasis (101 : Fin 221) = [68, 16, 2, 1] from rfl,
      show plane480GenSourceLb (101 : Fin 221) = 16 from rfl]
  exact plane480GenSource0101
theorem plane480GenBound0102 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (102 : Fin 221))) (plane480GenSourceLb (102 : Fin 221)) := by
  rw [show plane480GenSourceBasis (102 : Fin 221) = [68, 16, 8, 1] from rfl,
      show plane480GenSourceLb (102 : Fin 221) = 16 from rfl]
  exact plane480GenSource0102
theorem plane480GenBound0103 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (103 : Fin 221))) (plane480GenSourceLb (103 : Fin 221)) := by
  rw [show plane480GenSourceBasis (103 : Fin 221) = [64, 34, 16, 1] from rfl,
      show plane480GenSourceLb (103 : Fin 221) = 16 from rfl]
  exact plane480GenSource0103
theorem plane480GenBound0104 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (104 : Fin 221))) (plane480GenSourceLb (104 : Fin 221)) := by
  rw [show plane480GenSourceBasis (104 : Fin 221) = [66, 32, 16, 1] from rfl,
      show plane480GenSourceLb (104 : Fin 221) = 16 from rfl]
  exact plane480GenSource0104
theorem plane480GenBound0105 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (105 : Fin 221))) (plane480GenSourceLb (105 : Fin 221)) := by
  rw [show plane480GenSourceBasis (105 : Fin 221) = [72, 42, 16, 1] from rfl,
      show plane480GenSourceLb (105 : Fin 221) = 16 from rfl]
  exact plane480GenSource0105
theorem plane480GenBound0106 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (106 : Fin 221))) (plane480GenSourceLb (106 : Fin 221)) := by
  rw [show plane480GenSourceBasis (106 : Fin 221) = [74, 40, 16, 1] from rfl,
      show plane480GenSourceLb (106 : Fin 221) = 16 from rfl]
  exact plane480GenSource0106
theorem plane480GenBound0107 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (107 : Fin 221))) (plane480GenSourceLb (107 : Fin 221)) := by
  rw [show plane480GenSourceBasis (107 : Fin 221) = [98, 16, 6, 1] from rfl,
      show plane480GenSourceLb (107 : Fin 221) = 16 from rfl]
  exact plane480GenSource0107
theorem plane480GenBound0108 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (108 : Fin 221))) (plane480GenSourceLb (108 : Fin 221)) := by
  rw [show plane480GenSourceBasis (108 : Fin 221) = [98, 16, 4, 1] from rfl,
      show plane480GenSourceLb (108 : Fin 221) = 16 from rfl]
  exact plane480GenSource0108
theorem plane480GenBound0109 :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis (109 : Fin 221))) (plane480GenSourceLb (109 : Fin 221)) := by
  rw [show plane480GenSourceBasis (109 : Fin 221) = [128, 16, 12, 1] from rfl,
      show plane480GenSourceLb (109 : Fin 221) = 16 from rfl]
  exact plane480GenSource0109
end QiushiMatmul
