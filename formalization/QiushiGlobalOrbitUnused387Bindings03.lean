import QiushiGlobalOrbitUnused387Sources03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane387UnusedGenBound0030 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenSourceBasis (30 : Fin 32))) (plane387UnusedGenSourceLb (30 : Fin 32)) := by
  rw [show plane387UnusedGenSourceBasis (30 : Fin 32) = [259, 128, 67, 34, 19, 10, 7] from rfl,
      show plane387UnusedGenSourceLb (30 : Fin 32) = 12 from rfl]
  exact plane387UnusedGenSource0030
theorem plane387UnusedGenBound0031 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenSourceBasis (31 : Fin 32))) (plane387UnusedGenSourceLb (31 : Fin 32)) := by
  rw [show plane387UnusedGenSourceBasis (31 : Fin 32) = [256, 132, 68, 36, 20, 8, 2, 1] from rfl,
      show plane387UnusedGenSourceLb (31 : Fin 32) = 9 from rfl]
  exact plane387UnusedGenSource0031
end QiushiMatmul
