import QiushiPlane448GenSources05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane448GenBound0050 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (50 : Fin 56))) (plane448GenSourceLb (50 : Fin 56)) := by
  rw [show plane448GenSourceBasis (50 : Fin 56) = [276, 128, 64, 32, 12, 2, 1] from rfl,
      show plane448GenSourceLb (50 : Fin 56) = 12 from rfl]
  exact plane448GenSource0050
theorem plane448GenBound0051 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (51 : Fin 56))) (plane448GenSourceLb (51 : Fin 56)) := by
  rw [show plane448GenSourceBasis (51 : Fin 56) = [260, 128, 76, 32, 28, 2, 1] from rfl,
      show plane448GenSourceLb (51 : Fin 56) = 12 from rfl]
  exact plane448GenSource0051
theorem plane448GenBound0052 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (52 : Fin 56))) (plane448GenSourceLb (52 : Fin 56)) := by
  rw [show plane448GenSourceBasis (52 : Fin 56) = [266, 136, 74, 40, 24, 1] from rfl,
      show plane448GenSourceLb (52 : Fin 56) = 12 from rfl]
  exact plane448GenSource0052
theorem plane448GenBound0053 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (53 : Fin 56))) (plane448GenSourceLb (53 : Fin 56)) := by
  rw [show plane448GenSourceBasis (53 : Fin 56) = [260, 144, 68, 48, 12, 2, 1] from rfl,
      show plane448GenSourceLb (53 : Fin 56) = 12 from rfl]
  exact plane448GenSource0053
theorem plane448GenBound0054 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (54 : Fin 56))) (plane448GenSourceLb (54 : Fin 56)) := by
  rw [show plane448GenSourceBasis (54 : Fin 56) = [258, 144, 66, 48, 8, 6, 1] from rfl,
      show plane448GenSourceLb (54 : Fin 56) = 12 from rfl]
  exact plane448GenSource0054
theorem plane448GenBound0055 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (55 : Fin 56))) (plane448GenSourceLb (55 : Fin 56)) := by
  rw [show plane448GenSourceBasis (55 : Fin 56) = [256, 144, 64, 48, 10, 4, 1] from rfl,
      show plane448GenSourceLb (55 : Fin 56) = 12 from rfl]
  exact plane448GenSource0055
end QiushiMatmul
