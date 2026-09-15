import QiushiFrozenRank24
import QiushiOrbit8Closed

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace QiushiMatmul.FrozenRank

def sources027 : Fin 7 → List Nat := ![
  [288,160,16,8,4,2,1],
  [272,128,32,8,4,2,1],
  [256,144,48,8,4,2,1],
  [304,160,64,8,4,2,1],
  [304,160,80,8,4,2,1],
  [304,160,96,8,4,2,1],
  [304,160,112,8,4,2,1]]

theorem sources027_rank (i : Fin 7) :
    QuotientRankAtLeast (spanCodes (sources027 i)) 9 := by
  fin_cases i
  · exact quotientRankAtLeast_of_code_transport
      [256,96,16,8,4,2,1]
      [(288,360),(160,104),(16,8),(8,16),(4,5),(2,1),(1,2)]
      (codeMat 273) (codeMat 270) (codeMat 298) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_7
  · exact quotientRankAtLeast_of_code_transport
      [256,96,16,8,4,2,1]
      [(272,96),(128,256),(32,8),(8,16),(4,1),(2,4),(1,2)]
      (codeMat 273) (codeMat 140) (codeMat 98) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_7
  · exact quotientRankAtLeast_of_code_transport
      [256,96,16,8,4,2,1]
      [(256,256),(144,360),(48,8),(8,16),(4,4),(2,5),(1,2)]
      (codeMat 273) (codeMat 394) (codeMat 330) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_7
  · exact orbit8_lb9
  · exact sources024_rank 6
  · exact quotientRankAtLeast_of_code_transport
      [256,160,80,8,4,2,1]
      [(304,240),(160,344),(96,88),(8,8),(4,3),(2,5),(1,1)]
      (codeMat 273) (codeMat 167) (codeMat 167) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_9
  · exact quotientRankAtLeast_of_code_transport
      [256,160,80,8,4,2,1]
      [(304,424),(160,344),(112,416),(8,256),(4,5),(2,3),(1,4)]
      (codeMat 161) (codeMat 342) (codeMat 215) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_9

theorem sources027_contain : ∀ i g, g ∈ [304,160,8,4,2,1] →
    spanContainsCode (sources027 i) g = true := by
  decide +kernel

theorem sources027_cover : ∀ c : Fin 512,
    ∃ i : Fin 7, spanContainsCode (sources027 i) c.val = true := by
  decide +kernel

theorem span027_lb11 : QuotientRankAtLeast (spanCodes [304,160,8,4,2,1]) 11 :=
  quotientRankAtLeast_eleven_of_seven_code_cover _ sources027
    sources027_rank sources027_contain sources027_cover

theorem rep027 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 27))
      (frozenWangTable.lower 27) := by
  exact span027_lb11

end QiushiMatmul.FrozenRank
