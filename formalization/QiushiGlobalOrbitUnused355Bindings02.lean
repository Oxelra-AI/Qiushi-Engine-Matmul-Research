import QiushiGlobalOrbitUnused355Sources02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane355UnusedGenBound0020 :
    QuotientRankAtLeast (spanCodes (plane355UnusedGenSourceBasis (20 : Fin 21))) (plane355UnusedGenSourceLb (20 : Fin 21)) := by
  rw [show plane355UnusedGenSourceBasis (20 : Fin 21) = [260, 132, 64, 32, 20, 12, 2, 1] from rfl,
      show plane355UnusedGenSourceLb (20 : Fin 21) = 9 from rfl]
  exact plane355UnusedGenSource0020
end QiushiMatmul
