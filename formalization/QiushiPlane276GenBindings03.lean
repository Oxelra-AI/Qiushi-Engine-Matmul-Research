import QiushiPlane276GenSources03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane276GenBound0030 :
    QuotientRankAtLeast (spanCodes (plane276GenSourceBasis (30 : Fin 37))) (plane276GenSourceLb (30 : Fin 37)) := by
  rw [show plane276GenSourceBasis (30 : Fin 37) = [272, 144, 80, 48, 8, 2, 1] from rfl,
      show plane276GenSourceLb (30 : Fin 37) = 9 from rfl]
  exact plane276GenSource0030
theorem plane276GenBound0031 :
    QuotientRankAtLeast (spanCodes (plane276GenSourceBasis (31 : Fin 37))) (plane276GenSourceLb (31 : Fin 37)) := by
  rw [show plane276GenSourceBasis (31 : Fin 37) = [272, 144, 80, 48, 8, 4, 2, 1] from rfl,
      show plane276GenSourceLb (31 : Fin 37) = 6 from rfl]
  exact plane276GenSource0031
theorem plane276GenBound0032 :
    QuotientRankAtLeast (spanCodes (plane276GenSourceBasis (32 : Fin 37))) (plane276GenSourceLb (32 : Fin 37)) := by
  rw [show plane276GenSourceBasis (32 : Fin 37) = [256, 136, 64, 32, 16, 4, 2, 1] from rfl,
      show plane276GenSourceLb (32 : Fin 37) = 6 from rfl]
  exact plane276GenSource0032
theorem plane276GenBound0033 :
    QuotientRankAtLeast (spanCodes (plane276GenSourceBasis (33 : Fin 37))) (plane276GenSourceLb (33 : Fin 37)) := by
  rw [show plane276GenSourceBasis (33 : Fin 37) = [264, 128, 72, 40, 24, 4, 2, 1] from rfl,
      show plane276GenSourceLb (33 : Fin 37) = 6 from rfl]
  exact plane276GenSource0033
theorem plane276GenBound0034 :
    QuotientRankAtLeast (spanCodes (plane276GenSourceBasis (34 : Fin 37))) (plane276GenSourceLb (34 : Fin 37)) := by
  rw [show plane276GenSourceBasis (34 : Fin 37) = [260, 128, 96, 20, 2, 1] from rfl,
      show plane276GenSourceLb (34 : Fin 37) = 15 from rfl]
  exact plane276GenSource0034
theorem plane276GenBound0035 :
    QuotientRankAtLeast (spanCodes (plane276GenSourceBasis (35 : Fin 37))) (plane276GenSourceLb (35 : Fin 37)) := by
  rw [show plane276GenSourceBasis (35 : Fin 37) = [272, 68, 36, 8, 2, 1] from rfl,
      show plane276GenSourceLb (35 : Fin 37) = 15 from rfl]
  exact plane276GenSource0035
theorem plane276GenBound0036 :
    QuotientRankAtLeast (spanCodes (plane276GenSourceBasis (36 : Fin 37))) (plane276GenSourceLb (36 : Fin 37)) := by
  rw [show plane276GenSourceBasis (36 : Fin 37) = [268, 164, 96, 28, 2, 1] from rfl,
      show plane276GenSourceLb (36 : Fin 37) = 15 from rfl]
  exact plane276GenSource0036
end QiushiMatmul
