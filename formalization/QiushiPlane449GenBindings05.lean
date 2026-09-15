import QiushiPlane449GenSources05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane449GenBound0050 :
    QuotientRankAtLeast (spanCodes (plane449GenSourceBasis (50 : Fin 56))) (plane449GenSourceLb (50 : Fin 56)) := by
  rw [show plane449GenSourceBasis (50 : Fin 56) = [272, 140, 78, 44, 1] from rfl,
      show plane449GenSourceLb (50 : Fin 56) = 15 from rfl]
  exact plane449GenSource0050
theorem plane449GenBound0051 :
    QuotientRankAtLeast (spanCodes (plane449GenSourceBasis (51 : Fin 56))) (plane449GenSourceLb (51 : Fin 56)) := by
  rw [show plane449GenSourceBasis (51 : Fin 56) = [258, 144, 48, 8, 6, 1] from rfl,
      show plane449GenSourceLb (51 : Fin 56) = 12 from rfl]
  exact plane449GenSource0051
theorem plane449GenBound0052 :
    QuotientRankAtLeast (spanCodes (plane449GenSourceBasis (52 : Fin 56))) (plane449GenSourceLb (52 : Fin 56)) := by
  rw [show plane449GenSourceBasis (52 : Fin 56) = [258, 130, 72, 34, 24, 4, 1] from rfl,
      show plane449GenSourceLb (52 : Fin 56) = 12 from rfl]
  exact plane449GenSource0052
theorem plane449GenBound0053 :
    QuotientRankAtLeast (spanCodes (plane449GenSourceBasis (53 : Fin 56))) (plane449GenSourceLb (53 : Fin 56)) := by
  rw [show plane449GenSourceBasis (53 : Fin 56) = [262, 128, 66, 32, 22, 12, 1] from rfl,
      show plane449GenSourceLb (53 : Fin 56) = 12 from rfl]
  exact plane449GenSource0053
theorem plane449GenBound0054 :
    QuotientRankAtLeast (spanCodes (plane449GenSourceBasis (54 : Fin 56))) (plane449GenSourceLb (54 : Fin 56)) := by
  rw [show plane449GenSourceBasis (54 : Fin 56) = [288, 160, 64, 24, 4, 2, 1] from rfl,
      show plane449GenSourceLb (54 : Fin 56) = 9 from rfl]
  exact plane449GenSource0054
theorem plane449GenBound0055 :
    QuotientRankAtLeast (spanCodes (plane449GenSourceBasis (55 : Fin 56))) (plane449GenSourceLb (55 : Fin 56)) := by
  rw [show plane449GenSourceBasis (55 : Fin 56) = [260, 144, 64, 48, 8, 2, 1] from rfl,
      show plane449GenSourceLb (55 : Fin 56) = 9 from rfl]
  exact plane449GenSource0055
end QiushiMatmul
