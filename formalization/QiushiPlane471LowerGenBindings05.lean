import QiushiPlane471LowerGenSources05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane471LowerGenBound0050 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenSourceBasis (50 : Fin 53))) (plane471LowerGenSourceLb (50 : Fin 53)) := by
  rw [show plane471LowerGenSourceBasis (50 : Fin 53) = [289, 64, 20, 9, 3] from rfl,
      show plane471LowerGenSourceLb (50 : Fin 53) = 14 from rfl]
  exact plane471LowerGenSource0050
theorem plane471LowerGenBound0051 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenSourceBasis (51 : Fin 53))) (plane471LowerGenSourceLb (51 : Fin 53)) := by
  rw [show plane471LowerGenSourceBasis (51 : Fin 53) = [288, 68, 16, 8, 2, 1] from rfl,
      show plane471LowerGenSourceLb (51 : Fin 53) = 12 from rfl]
  exact plane471LowerGenSource0051
theorem plane471LowerGenBound0052 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenSourceBasis (52 : Fin 53))) (plane471LowerGenSourceLb (52 : Fin 53)) := by
  rw [show plane471LowerGenSourceBasis (52 : Fin 53) = [289, 65, 16, 8, 5, 2] from rfl,
      show plane471LowerGenSourceLb (52 : Fin 53) = 9 from rfl]
  exact plane471LowerGenSource0052
end QiushiMatmul
