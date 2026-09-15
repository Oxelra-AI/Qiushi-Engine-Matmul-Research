import QiushiPlane447GenSources05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane447GenBound0050 :
    QuotientRankAtLeast (spanCodes (plane447GenSourceBasis (50 : Fin 55))) (plane447GenSourceLb (50 : Fin 55)) := by
  rw [show plane447GenSourceBasis (50 : Fin 55) = [288, 160, 18, 1] from rfl,
      show plane447GenSourceLb (50 : Fin 55) = 15 from rfl]
  exact plane447GenSource0050
theorem plane447GenBound0051 :
    QuotientRankAtLeast (spanCodes (plane447GenSourceBasis (51 : Fin 55))) (plane447GenSourceLb (51 : Fin 55)) := by
  rw [show plane447GenSourceBasis (51 : Fin 55) = [272, 130, 34, 8, 1] from rfl,
      show plane447GenSourceLb (51 : Fin 55) = 14 from rfl]
  exact plane447GenSource0051
theorem plane447GenBound0052 :
    QuotientRankAtLeast (spanCodes (plane447GenSourceBasis (52 : Fin 55))) (plane447GenSourceLb (52 : Fin 55)) := by
  rw [show plane447GenSourceBasis (52 : Fin 55) = [274, 128, 64, 32, 1] from rfl,
      show plane447GenSourceLb (52 : Fin 55) = 14 from rfl]
  exact plane447GenSource0052
theorem plane447GenBound0053 :
    QuotientRankAtLeast (spanCodes (plane447GenSourceBasis (53 : Fin 55))) (plane447GenSourceLb (53 : Fin 55)) := by
  rw [show plane447GenSourceBasis (53 : Fin 55) = [278, 132, 72, 36, 1] from rfl,
      show plane447GenSourceLb (53 : Fin 55) = 14 from rfl]
  exact plane447GenSource0053
theorem plane447GenBound0054 :
    QuotientRankAtLeast (spanCodes (plane447GenSourceBasis (54 : Fin 55))) (plane447GenSourceLb (54 : Fin 55)) := by
  rw [show plane447GenSourceBasis (54 : Fin 55) = [256, 144, 48, 4, 2, 1] from rfl,
      show plane447GenSourceLb (54 : Fin 55) = 12 from rfl]
  exact plane447GenSource0054
end QiushiMatmul
