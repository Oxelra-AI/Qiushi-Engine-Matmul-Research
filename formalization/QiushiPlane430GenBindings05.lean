import QiushiPlane430GenSources05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane430GenBound0050 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (50 : Fin 57))) (plane430GenSourceLb (50 : Fin 57)) := by
  rw [show plane430GenSourceBasis (50 : Fin 57) = [256, 132, 64, 36, 16, 12, 1] from rfl,
      show plane430GenSourceLb (50 : Fin 57) = 12 from rfl]
  exact plane430GenSource0050
theorem plane430GenBound0051 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (51 : Fin 57))) (plane430GenSourceLb (51 : Fin 57)) := by
  rw [show plane430GenSourceBasis (51 : Fin 57) = [260, 130, 68, 32, 16, 10, 1] from rfl,
      show plane430GenSourceLb (51 : Fin 57) = 12 from rfl]
  exact plane430GenSource0051
theorem plane430GenBound0052 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (52 : Fin 57))) (plane430GenSourceLb (52 : Fin 57)) := by
  rw [show plane430GenSourceBasis (52 : Fin 57) = [256, 132, 64, 36, 16, 14, 1] from rfl,
      show plane430GenSourceLb (52 : Fin 57) = 12 from rfl]
  exact plane430GenSource0052
theorem plane430GenBound0053 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (53 : Fin 57))) (plane430GenSourceLb (53 : Fin 57)) := by
  rw [show plane430GenSourceBasis (53 : Fin 57) = [258, 132, 64, 36, 16, 12, 1] from rfl,
      show plane430GenSourceLb (53 : Fin 57) = 12 from rfl]
  exact plane430GenSource0053
theorem plane430GenBound0054 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (54 : Fin 57))) (plane430GenSourceLb (54 : Fin 57)) := by
  rw [show plane430GenSourceBasis (54 : Fin 57) = [260, 134, 68, 32, 16, 12, 1] from rfl,
      show plane430GenSourceLb (54 : Fin 57) = 12 from rfl]
  exact plane430GenSource0054
theorem plane430GenBound0055 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (55 : Fin 57))) (plane430GenSourceLb (55 : Fin 57)) := by
  rw [show plane430GenSourceBasis (55 : Fin 57) = [262, 128, 70, 34, 16, 10, 1] from rfl,
      show plane430GenSourceLb (55 : Fin 57) = 12 from rfl]
  exact plane430GenSource0055
theorem plane430GenBound0056 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (56 : Fin 57))) (plane430GenSourceLb (56 : Fin 57)) := by
  rw [show plane430GenSourceBasis (56 : Fin 57) = [256, 128, 66, 34, 16, 10, 4, 1] from rfl,
      show plane430GenSourceLb (56 : Fin 57) = 9 from rfl]
  exact plane430GenSource0056
end QiushiMatmul
