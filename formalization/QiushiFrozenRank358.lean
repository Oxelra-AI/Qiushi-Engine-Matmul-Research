import QiushiFrozenRank357
import QiushiPlane427GenBindings06
import QiushiStep99Orbit77Dispatch
import QiushiWcOrbit166Dispatch
import QiushiPlane315GenBindings00
import QiushiFlattenSeeds

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open BigOperators

namespace QiushiMatmul.FrozenRank

def sources358 : Fin 10 → List Nat := ![
  [288,162,96,20,1],
  [298,168,96,20,1],
  [256,128,96,20,2,1],
  [386,74,42,18,6,1],
  [386,66,34,20,8,1],
  [262,132,96,20,12,1],
  [270,140,70,38,20,1],
  [268,142,72,40,20,1],
  [260,134,74,42,20,1],
  [258,128,64,32,16,10,4,1]]

def lower358 : Fin 10 → Nat := ![15,16,15,15,15,15,15,15,15,9]

theorem sources358_rank (i : Fin 10) :
    QuotientRankAtLeast (spanCodes (sources358 i)) (lower358 i) := by
  fin_cases i
  · exact quotientRankAtLeast_of_code_transport
      [334,192,36,16,1]
      [(288,36),(162,245),(96,37),(20,378),(1,16)]
      (codeMat 396) (codeMat 188) (codeMat 103) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      plane427GenBound0061
  · exact sources357_rank 6
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(256,9),(128,1),(96,118),(20,20),(2,2),(1,128)]
      (codeMat 204) (codeMat 102) (codeMat 156) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(386,96),(74,127),(42,131),(18,128),(6,8),(1,9)]
      (codeMat 281) (codeMat 425) (codeMat 249) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(386,252),(66,126),(34,31),(20,28),(8,8),(1,9)]
      (codeMat 467) (codeMat 403) (codeMat 403) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [260,128,96,20,10,1]
      [(262,126),(132,399),(96,20),(20,139),(12,11),(1,1)]
      (codeMat 401) (codeMat 167) (codeMat 167) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step99_orbit77_lb15_unconditional
  · exact quotientRankAtLeast_of_code_transport
      [290,160,96,20,10,1]
      [(270,117),(140,106),(70,10),(38,508),(20,291),(1,1)]
      (codeMat 425) (codeMat 421) (codeMat 179) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step109wc166s6Dispatch
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(268,11),(142,253),(72,130),(40,8),(20,232),(1,128)]
      (codeMat 87) (codeMat 174) (codeMat 359) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [260,160,68,16,10,1]
      [(260,27),(134,238),(74,321),(42,186),(20,430),(1,260)]
      (codeMat 478) (codeMat 230) (codeMat 159) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      plane315GenBound0009
  · exact quotientRankAtLeast_of_code_transport
      [256,128,68,32,20,8,2,1]
      [(258,80),(128,216),(64,288),(32,1),(16,3),(10,28),(4,8),(1,32)]
      (codeMat 330) (codeMat 86) (codeMat 212) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_3

theorem sources358_contain : ∀ i g, g ∈ [386,96,20,1] →
    spanContainsCode (sources358 i) g = true := by
  decide +kernel

theorem sources358_cover : ∀ c : Fin 512,
    ∃ i : Fin 10, spanContainsCode (sources358 i) c.val = true := by
  decide +kernel

theorem capacity358 (r : Nat) (hr : r < 17) (hlower : ∀ i, lower358 i ≤ r) :
    (∑ i : Fin 10, (r - lower358 i)) < r := by
  have h16 : 16 ≤ r := hlower 1
  have heq : r = 16 := by omega
  subst r
  decide +kernel

theorem span358_lb17 : QuotientRankAtLeast (spanCodes [386,96,20,1]) 17 :=
  quotientRankAtLeast_of_mixed_code_cover _ sources358 lower358
    sources358_rank sources358_contain sources358_cover capacity358

theorem rep358 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 358))
      (frozenWangTable.lower 358) := by
  exact span358_lb17

end QiushiMatmul.FrozenRank
