import QiushiGlobalOrbitUnused386Sources02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane386UnusedGenBound0020 :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenSourceBasis (20 : Fin 21))) (plane386UnusedGenSourceLb (20 : Fin 21)) := by
  rw [show plane386UnusedGenSourceBasis (20 : Fin 21) = [256, 130, 66, 34, 18, 10, 6, 1] from rfl,
      show plane386UnusedGenSourceLb (20 : Fin 21) = 9 from rfl]
  exact plane386UnusedGenSource0020
end QiushiMatmul
