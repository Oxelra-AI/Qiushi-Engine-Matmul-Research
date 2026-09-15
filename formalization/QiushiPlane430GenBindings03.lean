import QiushiPlane430GenSources03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane430GenBound0030 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (30 : Fin 57))) (plane430GenSourceLb (30 : Fin 57)) := by
  rw [show plane430GenSourceBasis (30 : Fin 57) = [172, 100, 16, 2, 1] from rfl,
      show plane430GenSourceLb (30 : Fin 57) = 15 from rfl]
  exact plane430GenSource0030
theorem plane430GenBound0031 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (31 : Fin 57))) (plane430GenSourceLb (31 : Fin 57)) := by
  rw [show plane430GenSourceBasis (31 : Fin 57) = [290, 96, 16, 8, 4, 1] from rfl,
      show plane430GenSourceLb (31 : Fin 57) = 15 from rfl]
  exact plane430GenSource0031
theorem plane430GenBound0032 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (32 : Fin 57))) (plane430GenSourceLb (32 : Fin 57)) := by
  rw [show plane430GenSourceBasis (32 : Fin 57) = [268, 134, 100, 16, 1] from rfl,
      show plane430GenSourceLb (32 : Fin 57) = 15 from rfl]
  exact plane430GenSource0032
theorem plane430GenBound0033 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (33 : Fin 57))) (plane430GenSourceLb (33 : Fin 57)) := by
  rw [show plane430GenSourceBasis (33 : Fin 57) = [288, 140, 100, 16, 1] from rfl,
      show plane430GenSourceLb (33 : Fin 57) = 15 from rfl]
  exact plane430GenSource0033
theorem plane430GenBound0034 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (34 : Fin 57))) (plane430GenSourceLb (34 : Fin 57)) := by
  rw [show plane430GenSourceBasis (34 : Fin 57) = [386, 74, 40, 16, 6, 1] from rfl,
      show plane430GenSourceLb (34 : Fin 57) = 15 from rfl]
  exact plane430GenSource0034
theorem plane430GenBound0035 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (35 : Fin 57))) (plane430GenSourceLb (35 : Fin 57)) := by
  rw [show plane430GenSourceBasis (35 : Fin 57) = [134, 70, 34, 16, 14, 1] from rfl,
      show plane430GenSourceLb (35 : Fin 57) = 14 from rfl]
  exact plane430GenSource0035
theorem plane430GenBound0036 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (36 : Fin 57))) (plane430GenSourceLb (36 : Fin 57)) := by
  rw [show plane430GenSourceBasis (36 : Fin 57) = [290, 162, 96, 16, 4, 1] from rfl,
      show plane430GenSourceLb (36 : Fin 57) = 14 from rfl]
  exact plane430GenSource0036
theorem plane430GenBound0037 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (37 : Fin 57))) (plane430GenSourceLb (37 : Fin 57)) := by
  rw [show plane430GenSourceBasis (37 : Fin 57) = [256, 130, 66, 34, 16, 4, 1] from rfl,
      show plane430GenSourceLb (37 : Fin 57) = 12 from rfl]
  exact plane430GenSource0037
theorem plane430GenBound0038 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (38 : Fin 57))) (plane430GenSourceLb (38 : Fin 57)) := by
  rw [show plane430GenSourceBasis (38 : Fin 57) = [264, 130, 74, 42, 16, 4, 1] from rfl,
      show plane430GenSourceLb (38 : Fin 57) = 12 from rfl]
  exact plane430GenSource0038
theorem plane430GenBound0039 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (39 : Fin 57))) (plane430GenSourceLb (39 : Fin 57)) := by
  rw [show plane430GenSourceBasis (39 : Fin 57) = [264, 136, 64, 34, 16, 6, 1] from rfl,
      show plane430GenSourceLb (39 : Fin 57) = 12 from rfl]
  exact plane430GenSource0039
end QiushiMatmul
