import QiushiPlane324GenSources03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane324GenBound0030 :
    QuotientRankAtLeast (spanCodes (plane324GenSourceBasis (30 : Fin 31))) (plane324GenSourceLb (30 : Fin 31)) := by
  rw [show plane324GenSourceBasis (30 : Fin 31) = [258, 130, 66, 32, 16, 10, 4, 1] from rfl,
      show plane324GenSourceLb (30 : Fin 31) = 9 from rfl]
  exact plane324GenSource0030
end QiushiMatmul
