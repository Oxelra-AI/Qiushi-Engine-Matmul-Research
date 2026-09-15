import QiushiFrozenRank358
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit180Dispatch
import QiushiBranch262Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open BigOperators

namespace QiushiMatmul.FrozenRank

def sources359 : Fin 11 → List Nat := ![
  [418,96,20,10,1],
  [290,138,96,20,1],
  [264,160,96,20,1],
  [266,162,96,20,1],
  [386,74,42,16,4,1],
  [386,74,42,18,6,1],
  [386,66,34,20,8,1],
  [256,136,64,32,20,1],
  [262,132,74,42,20,1],
  [260,134,74,42,20,1],
  [256,128,68,36,20,12,2,1]]

def lower359 : Fin 11 → Nat := ![16,16,15,16,14,15,15,15,15,15,9]

theorem sources359_rank (i : Fin 11) :
    QuotientRankAtLeast (spanCodes (sources359 i)) (lower359 i) := by
  fin_cases i
  · exact quotientRankAtLeast_of_code_transport
      [256,96,20,10,1]
      [(418,276),(96,126),(20,20),(10,11),(1,1)]
      (codeMat 473) (codeMat 305) (codeMat 305) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step109_orbit164_lb16_wc
  · exact quotientRankAtLeast_of_code_transport
      [294,136,96,20,1]
      [(290,294),(138,136),(96,97),(20,20),(1,1)]
      (codeMat 337) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step109_orbit238_lb16_wc
  · exact quotientRankAtLeast_of_code_transport
      [144,84,32,10,1]
      [(264,10),(160,155),(96,11),(20,228),(1,32)]
      (codeMat 102) (codeMat 172) (codeMat 99) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step109_orbit180_lb15_wc
  · exact quotientRankAtLeast_of_code_transport
      [278,132,96,10,1]
      [(266,229),(162,132),(96,381),(20,278),(1,504)]
      (codeMat 501) (codeMat 249) (codeMat 425) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step109_orbit214_lb16_wc
  · exact quotientRankAtLeast_of_code_transport
      [272,132,32,12,2,1]
      [(386,437),(74,135),(42,12),(16,45),(4,3),(1,2)]
      (codeMat 473) (codeMat 174) (codeMat 359) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step113_262_row11_qr
  · exact sources358_rank 3
  · exact sources358_rank 4
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(256,1),(136,21),(64,2),(32,8),(20,104),(1,128)]
      (codeMat 84) (codeMat 142) (codeMat 354) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [256,164,96,16,10,1]
      [(262,437),(132,222),(74,10),(42,452),(20,197),(1,1)]
      (codeMat 249) (codeMat 307) (codeMat 311) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      plane152GenBound0001
  · exact sources358_rank 8
  · exact quotientRankAtLeast_of_code_transport
      [256,128,68,32,20,8,2,1]
      [(256,504),(128,216),(68,151),(36,63),(20,31),(12,23),(2,3),(1,2)]
      (codeMat 401) (codeMat 318) (codeMat 299) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_3

theorem sources359_contain : ∀ i g, g ∈ [424,96,20,1] →
    spanContainsCode (sources359 i) g = true := by
  decide +kernel

theorem sources359_cover : ∀ c : Fin 512,
    ∃ i : Fin 11, spanContainsCode (sources359 i) c.val = true := by
  decide +kernel

theorem capacity359 (r : Nat) (hr : r < 17) (hlower : ∀ i, lower359 i ≤ r) :
    (∑ i : Fin 11, (r - lower359 i)) < r := by
  have h16 : 16 ≤ r := hlower 0
  have heq : r = 16 := by omega
  subst r
  decide +kernel

theorem span359_lb17 : QuotientRankAtLeast (spanCodes [424,96,20,1]) 17 :=
  quotientRankAtLeast_of_mixed_code_cover _ sources359 lower359
    sources359_rank sources359_contain sources359_cover capacity359

theorem rep359 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 359))
      (frozenWangTable.lower 359) := by
  exact span359_lb17

end QiushiMatmul.FrozenRank
