import QiushiPlane429GenSources05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane429GenBound0050 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (50 : Fin 55))) (plane429GenSourceLb (50 : Fin 55)) := by
  rw [show plane429GenSourceBasis (50 : Fin 55) = [260, 132, 70, 36, 16, 10, 1] from rfl,
      show plane429GenSourceLb (50 : Fin 55) = 12 from rfl]
  exact plane429GenSource0050
theorem plane429GenBound0051 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (51 : Fin 55))) (plane429GenSourceLb (51 : Fin 55)) := by
  rw [show plane429GenSourceBasis (51 : Fin 55) = [256, 136, 64, 34, 16, 4, 1] from rfl,
      show plane429GenSourceLb (51 : Fin 55) = 12 from rfl]
  exact plane429GenSource0051
theorem plane429GenBound0052 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (52 : Fin 55))) (plane429GenSourceLb (52 : Fin 55)) := by
  rw [show plane429GenSourceBasis (52 : Fin 55) = [260, 132, 68, 36, 16, 12, 2, 1] from rfl,
      show plane429GenSourceLb (52 : Fin 55) = 9 from rfl]
  exact plane429GenSource0052
theorem plane429GenBound0053 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (53 : Fin 55))) (plane429GenSourceLb (53 : Fin 55)) := by
  rw [show plane429GenSourceBasis (53 : Fin 55) = [256, 132, 68, 36, 16, 12, 2, 1] from rfl,
      show plane429GenSourceLb (53 : Fin 55) = 9 from rfl]
  exact plane429GenSource0053
theorem plane429GenBound0054 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (54 : Fin 55))) (plane429GenSourceLb (54 : Fin 55)) := by
  rw [show plane429GenSourceBasis (54 : Fin 55) = [260, 132, 64, 32, 16, 12, 2, 1] from rfl,
      show plane429GenSourceLb (54 : Fin 55) = 9 from rfl]
  exact plane429GenSource0054
end QiushiMatmul
