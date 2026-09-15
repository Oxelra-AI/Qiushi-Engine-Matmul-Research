import QiushiPlane458GenSources20
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane458GenBound0200 :
    QuotientRankAtLeast (spanCodes (plane458GenSourceBasis (200 : Fin 203))) (plane458GenSourceLb (200 : Fin 203)) := by
  rw [show plane458GenSourceBasis (200 : Fin 203) = [256, 129, 65, 33, 16, 8, 4, 2] from rfl,
      show plane458GenSourceLb (200 : Fin 203) = 9 from rfl]
  exact plane458GenSource0200
theorem plane458GenBound0201 :
    QuotientRankAtLeast (spanCodes (plane458GenSourceBasis (201 : Fin 203))) (plane458GenSourceLb (201 : Fin 203)) := by
  rw [show plane458GenSourceBasis (201 : Fin 203) = [258, 130, 66, 32, 18, 10, 6, 1] from rfl,
      show plane458GenSourceLb (201 : Fin 203) = 9 from rfl]
  exact plane458GenSource0201
theorem plane458GenBound0202 :
    QuotientRankAtLeast (spanCodes (plane458GenSourceBasis (202 : Fin 203))) (plane458GenSourceLb (202 : Fin 203)) := by
  rw [show plane458GenSourceBasis (202 : Fin 203) = [256, 132, 68, 36, 20, 8, 2, 1] from rfl,
      show plane458GenSourceLb (202 : Fin 203) = 9 from rfl]
  exact plane458GenSource0202
end QiushiMatmul
