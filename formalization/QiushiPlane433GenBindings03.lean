import QiushiPlane433GenSources03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane433GenBound0030 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (30 : Fin 63))) (plane433GenSourceLb (30 : Fin 63)) := by
  rw [show plane433GenSourceBasis (30 : Fin 63) = [258, 230, 16, 1] from rfl,
      show plane433GenSourceLb (30 : Fin 63) = 16 from rfl]
  exact plane433GenSource0030
theorem plane433GenBound0031 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (31 : Fin 63))) (plane433GenSourceLb (31 : Fin 63)) := by
  rw [show plane433GenSourceBasis (31 : Fin 63) = [258, 238, 16, 1] from rfl,
      show plane433GenSourceLb (31 : Fin 63) = 16 from rfl]
  exact plane433GenSource0031
theorem plane433GenBound0032 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (32 : Fin 63))) (plane433GenSourceLb (32 : Fin 63)) := by
  rw [show plane433GenSourceBasis (32 : Fin 63) = [258, 32, 16, 14, 1] from rfl,
      show plane433GenSourceLb (32 : Fin 63) = 15 from rfl]
  exact plane433GenSource0032
theorem plane433GenBound0033 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (33 : Fin 63))) (plane433GenSourceLb (33 : Fin 63)) := by
  rw [show plane433GenSourceBasis (33 : Fin 63) = [258, 74, 40, 16, 4, 1] from rfl,
      show plane433GenSourceLb (33 : Fin 63) = 15 from rfl]
  exact plane433GenSource0033
theorem plane433GenBound0034 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (34 : Fin 63))) (plane433GenSourceLb (34 : Fin 63)) := by
  rw [show plane433GenSourceBasis (34 : Fin 63) = [258, 68, 36, 16, 8, 1] from rfl,
      show plane433GenSourceLb (34 : Fin 63) = 15 from rfl]
  exact plane433GenSource0034
theorem plane433GenBound0035 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (35 : Fin 63))) (plane433GenSourceLb (35 : Fin 63)) := by
  rw [show plane433GenSourceBasis (35 : Fin 63) = [258, 74, 38, 16, 1] from rfl,
      show plane433GenSourceLb (35 : Fin 63) = 15 from rfl]
  exact plane433GenSource0035
theorem plane433GenBound0036 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (36 : Fin 63))) (plane433GenSourceLb (36 : Fin 63)) := by
  rw [show plane433GenSourceBasis (36 : Fin 63) = [258, 140, 38, 16, 1] from rfl,
      show plane433GenSourceLb (36 : Fin 63) = 15 from rfl]
  exact plane433GenSource0036
theorem plane433GenBound0037 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (37 : Fin 63))) (plane433GenSourceLb (37 : Fin 63)) := by
  rw [show plane433GenSourceBasis (37 : Fin 63) = [258, 140, 32, 16, 1] from rfl,
      show plane433GenSourceLb (37 : Fin 63) = 15 from rfl]
  exact plane433GenSource0037
theorem plane433GenBound0038 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (38 : Fin 63))) (plane433GenSourceLb (38 : Fin 63)) := by
  rw [show plane433GenSourceBasis (38 : Fin 63) = [258, 192, 16, 8, 1] from rfl,
      show plane433GenSourceLb (38 : Fin 63) = 15 from rfl]
  exact plane433GenSource0038
theorem plane433GenBound0039 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (39 : Fin 63))) (plane433GenSourceLb (39 : Fin 63)) := by
  rw [show plane433GenSourceBasis (39 : Fin 63) = [258, 160, 96, 16, 8, 1] from rfl,
      show plane433GenSourceLb (39 : Fin 63) = 15 from rfl]
  exact plane433GenSource0039
end QiushiMatmul
