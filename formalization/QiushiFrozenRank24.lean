import QiushiFrozenRankCover
import QiushiCertifiedTransport
import QiushiOrbit5FP
import QiushiFlattenSeeds
import QiushiFrozenWangData

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace QiushiMatmul.FrozenRank

def sources024 : Fin 7 → List Nat := ![
  [160,64,16,8,4,2,1],
  [128,80,32,8,4,2,1],
  [144,80,48,8,4,2,1],
  [256,160,80,8,4,2,1],
  [272,160,80,8,4,2,1],
  [288,160,80,8,4,2,1],
  [304,160,80,8,4,2,1]]

theorem sources024_rank (i : Fin 7) :
    QuotientRankAtLeast (spanCodes (sources024 i)) 9 := by
  fin_cases i
  · exact quotientRankAtLeast_of_code_transport
      [1,2,4,8,16,64,160]
      [(160,160),(64,64),(16,16),(8,8),(4,4),(2,2),(1,1)]
      (codeMat 273) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit5_lb9
  · exact quotientRankAtLeast_of_code_transport
      [256,96,16,8,4,2,1]
      [(128,256),(80,96),(32,16),(8,8),(4,2),(2,4),(1,1)]
      (codeMat 273) (codeMat 161) (codeMat 161) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_7
  · exact quotientRankAtLeast_of_code_transport
      [256,96,16,8,4,2,1]
      [(144,360),(80,104),(48,24),(8,8),(4,6),(2,5),(1,1)]
      (codeMat 273) (codeMat 419) (codeMat 183) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_7
  · exact flatSeed_9
  · exact quotientRankAtLeast_of_code_transport
      [256,160,80,8,4,2,1]
      [(272,336),(160,168),(80,80),(8,8),(4,5),(2,2),(1,1)]
      (codeMat 273) (codeMat 277) (codeMat 277) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_9
  · exact quotientRankAtLeast_of_code_transport
      [256,160,80,8,4,2,1]
      [(288,256),(160,248),(80,80),(8,8),(4,4),(2,3),(1,1)]
      (codeMat 401) (codeMat 275) (codeMat 275) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_9
  · exact quotientRankAtLeast_of_code_transport
      [256,160,80,8,4,2,1]
      [(304,344),(160,240),(80,416),(8,256),(4,3),(2,6),(1,4)]
      (codeMat 161) (codeMat 244) (codeMat 95) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_9

theorem sources024_contain : ∀ i g, g ∈ [160,80,8,4,2,1] →
    spanContainsCode (sources024 i) g = true := by
  decide +kernel

theorem sources024_cover : ∀ c : Fin 512,
    ∃ i : Fin 7, spanContainsCode (sources024 i) c.val = true := by
  decide +kernel

theorem span024_lb11 : QuotientRankAtLeast (spanCodes [160,80,8,4,2,1]) 11 :=
  quotientRankAtLeast_eleven_of_seven_code_cover _ sources024
    sources024_rank sources024_contain sources024_cover

theorem rep024 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 24))
      (frozenWangTable.lower 24) := by
  exact span024_lb11

end QiushiMatmul.FrozenRank
