import QiushiGlobalOrbitUnused396Sources03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane396UnusedGenBound0030 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenSourceBasis (30 : Fin 32))) (plane396UnusedGenSourceLb (30 : Fin 32)) := by
  rw [show plane396UnusedGenSourceBasis (30 : Fin 32) = [257, 131, 66, 34, 18, 10, 6] from rfl,
      show plane396UnusedGenSourceLb (30 : Fin 32) = 12 from rfl]
  exact plane396UnusedGenSource0030
theorem plane396UnusedGenBound0031 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenSourceBasis (31 : Fin 32))) (plane396UnusedGenSourceLb (31 : Fin 32)) := by
  rw [show plane396UnusedGenSourceBasis (31 : Fin 32) = [257, 128, 65, 33, 17, 8, 5, 2] from rfl,
      show plane396UnusedGenSourceLb (31 : Fin 32) = 6 from rfl]
  exact plane396UnusedGenSource0031
end QiushiMatmul
