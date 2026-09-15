import QiushiFrozenRank24

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace QiushiMatmul.FrozenRank

def sources028 : Fin 7 → List Nat := ![
  [272,160,80,8,4,2,1],
  [264,160,64,16,4,2,1],
  [256,160,72,24,4,2,1],
  [280,128,80,32,4,2,1],
  [280,136,80,40,4,2,1],
  [280,144,80,48,4,2,1],
  [280,152,80,56,4,2,1]]

theorem sources028_rank (i : Fin 7) :
    QuotientRankAtLeast (spanCodes (sources028 i)) 9 := by
  fin_cases i
  · exact sources024_rank 4
  · exact quotientRankAtLeast_of_code_transport
      [256,160,80,8,4,2,1]
      [(264,80),(160,160),(64,8),(16,256),(4,2),(2,4),(1,1)]
      (codeMat 161) (codeMat 161) (codeMat 161) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_9
  · exact quotientRankAtLeast_of_code_transport
      [256,160,80,8,4,2,1]
      [(256,8),(160,88),(72,504),(24,256),(4,1),(2,3),(1,7)]
      (codeMat 161) (codeMat 95) (codeMat 244) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_9
  · exact quotientRankAtLeast_of_code_transport
      [256,160,80,8,4,2,1]
      [(280,160),(128,8),(80,88),(32,256),(4,4),(2,1),(1,3)]
      (codeMat 161) (codeMat 267) (codeMat 282) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_9
  · exact quotientRankAtLeast_of_code_transport
      [256,160,80,8,4,2,1]
      [(280,248),(136,336),(80,168),(40,8),(4,3),(2,5),(1,2)]
      (codeMat 273) (codeMat 174) (codeMat 359) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_9
  · exact quotientRankAtLeast_of_code_transport
      [256,160,80,8,4,2,1]
      [(280,416),(144,504),(80,248),(48,8),(4,6),(2,7),(1,3)]
      (codeMat 273) (codeMat 443) (codeMat 254) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_9
  · exact quotientRankAtLeast_of_code_transport
      [256,160,80,8,4,2,1]
      [(280,496),(152,240),(80,344),(56,8),(4,7),(2,3),(1,5)]
      (codeMat 273) (codeMat 375) (codeMat 491) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_9

theorem sources028_contain : ∀ i g, g ∈ [280,160,80,4,2,1] →
    spanContainsCode (sources028 i) g = true := by
  decide +kernel

theorem sources028_cover : ∀ c : Fin 512,
    ∃ i : Fin 7, spanContainsCode (sources028 i) c.val = true := by
  decide +kernel

theorem span028_lb11 : QuotientRankAtLeast (spanCodes [280,160,80,4,2,1]) 11 :=
  quotientRankAtLeast_eleven_of_seven_code_cover _ sources028
    sources028_rank sources028_contain sources028_cover

theorem rep028 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 28))
      (frozenWangTable.lower 28) := by
  exact span028_lb11

end QiushiMatmul.FrozenRank
