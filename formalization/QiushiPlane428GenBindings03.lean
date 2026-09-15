import QiushiPlane428GenSources03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane428GenBound0030 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (30 : Fin 51))) (plane428GenSourceLb (30 : Fin 51)) := by
  rw [show plane428GenSourceBasis (30 : Fin 51) = [256, 132, 96, 16, 10, 1] from rfl,
      show plane428GenSourceLb (30 : Fin 51) = 15 from rfl]
  exact plane428GenSource0030
theorem plane428GenBound0031 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (31 : Fin 51))) (plane428GenSourceLb (31 : Fin 51)) := by
  rw [show plane428GenSourceBasis (31 : Fin 51) = [416, 96, 16, 1] from rfl,
      show plane428GenSourceLb (31 : Fin 51) = 15 from rfl]
  exact plane428GenSource0031
theorem plane428GenBound0032 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (32 : Fin 51))) (plane428GenSourceLb (32 : Fin 51)) := by
  rw [show plane428GenSourceBasis (32 : Fin 51) = [296, 142, 96, 16, 1] from rfl,
      show plane428GenSourceLb (32 : Fin 51) = 15 from rfl]
  exact plane428GenSource0032
theorem plane428GenBound0033 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (33 : Fin 51))) (plane428GenSourceLb (33 : Fin 51)) := by
  rw [show plane428GenSourceBasis (33 : Fin 51) = [292, 140, 96, 16, 1] from rfl,
      show plane428GenSourceLb (33 : Fin 51) = 15 from rfl]
  exact plane428GenSource0033
theorem plane428GenBound0034 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (34 : Fin 51))) (plane428GenSourceLb (34 : Fin 51)) := by
  rw [show plane428GenSourceBasis (34 : Fin 51) = [298, 128, 96, 16, 1] from rfl,
      show plane428GenSourceLb (34 : Fin 51) = 15 from rfl]
  exact plane428GenSource0034
theorem plane428GenBound0035 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (35 : Fin 51))) (plane428GenSourceLb (35 : Fin 51)) := by
  rw [show plane428GenSourceBasis (35 : Fin 51) = [302, 130, 96, 16, 1] from rfl,
      show plane428GenSourceLb (35 : Fin 51) = 15 from rfl]
  exact plane428GenSource0035
theorem plane428GenBound0036 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (36 : Fin 51))) (plane428GenSourceLb (36 : Fin 51)) := by
  rw [show plane428GenSourceBasis (36 : Fin 51) = [426, 96, 16, 6, 1] from rfl,
      show plane428GenSourceLb (36 : Fin 51) = 15 from rfl]
  exact plane428GenSource0036
theorem plane428GenBound0037 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (37 : Fin 51))) (plane428GenSourceLb (37 : Fin 51)) := by
  rw [show plane428GenSourceBasis (37 : Fin 51) = [418, 96, 16, 8, 6, 1] from rfl,
      show plane428GenSourceLb (37 : Fin 51) = 15 from rfl]
  exact plane428GenSource0037
theorem plane428GenBound0038 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (38 : Fin 51))) (plane428GenSourceLb (38 : Fin 51)) := by
  rw [show plane428GenSourceBasis (38 : Fin 51) = [256, 72, 40, 16, 1] from rfl,
      show plane428GenSourceLb (38 : Fin 51) = 14 from rfl]
  exact plane428GenSource0038
theorem plane428GenBound0039 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (39 : Fin 51))) (plane428GenSourceLb (39 : Fin 51)) := by
  rw [show plane428GenSourceBasis (39 : Fin 51) = [264, 64, 32, 16, 1] from rfl,
      show plane428GenSourceLb (39 : Fin 51) = 14 from rfl]
  exact plane428GenSource0039
end QiushiMatmul
