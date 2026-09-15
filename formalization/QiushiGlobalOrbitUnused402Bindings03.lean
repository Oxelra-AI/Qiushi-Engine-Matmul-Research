import QiushiGlobalOrbitUnused402Sources03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane402UnusedGenBound0030 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenSourceBasis (30 : Fin 31))) (plane402UnusedGenSourceLb (30 : Fin 31)) := by
  rw [show plane402UnusedGenSourceBasis (30 : Fin 31) = [257, 129, 64, 32, 16, 9, 4, 3] from rfl,
      show plane402UnusedGenSourceLb (30 : Fin 31) = 9 from rfl]
  exact plane402UnusedGenSource0030
end QiushiMatmul
