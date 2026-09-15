import QiushiGlobalOrbitUnused394Sources03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane394UnusedGenBound0030 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenSourceBasis (30 : Fin 32))) (plane394UnusedGenSourceLb (30 : Fin 32)) := by
  rw [show plane394UnusedGenSourceBasis (30 : Fin 32) = [256, 64, 33, 16, 8, 4, 2] from rfl,
      show plane394UnusedGenSourceLb (30 : Fin 32) = 9 from rfl]
  exact plane394UnusedGenSource0030
theorem plane394UnusedGenBound0031 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenSourceBasis (31 : Fin 32))) (plane394UnusedGenSourceLb (31 : Fin 32)) := by
  rw [show plane394UnusedGenSourceBasis (31 : Fin 32) = [256, 130, 64, 33, 16, 10, 4] from rfl,
      show plane394UnusedGenSourceLb (31 : Fin 32) = 12 from rfl]
  exact plane394UnusedGenSource0031
end QiushiMatmul
