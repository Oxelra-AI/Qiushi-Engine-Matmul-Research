import QiushiGlobalOrbitUnused339Sources03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane339UnusedGenBound0030 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenSourceBasis (30 : Fin 31))) (plane339UnusedGenSourceLb (30 : Fin 31)) := by
  rw [show plane339UnusedGenSourceBasis (30 : Fin 31) = [256, 134, 70, 36, 16, 12, 1] from rfl,
      show plane339UnusedGenSourceLb (30 : Fin 31) = 12 from rfl]
  exact plane339UnusedGenSource0030
end QiushiMatmul
