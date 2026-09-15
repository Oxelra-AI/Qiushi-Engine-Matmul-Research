import QiushiFrozenRankCoverMixed
import QiushiCertifiedTransport
import QiushiGlobalOrbitUnused88Final
import QiushiOrbit101FP
import QiushiOrbit31FP
import QiushiOrbit35FP
import QiushiFlattenSeeds
import QiushiFrozenWangData

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open BigOperators

namespace QiushiMatmul.FrozenRank

def sources260 : Fin 7 → List Nat := ![
  [80,8,4,2,1],
  [144,80,12,2,1],
  [128,68,20,12,2,1],
  [292,132,80,12,2,1],
  [308,132,80,12,2,1],
  [256,132,64,32,16,12,2,1],
  [260,132,64,36,16,12,2,1]]

def lower260 : Fin 7 → Nat := ![13,15,15,15,15,9,9]

theorem sources260_rank (i : Fin 7) :
    QuotientRankAtLeast (spanCodes (sources260 i)) (lower260 i) := by
  fin_cases i
  · exact plane88UnusedGen_lb13
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,32,84]
      [(144,32),(80,34),(12,118),(2,8),(1,9)]
      (codeMat 417) (codeMat 281) (codeMat 281) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit101_lb15
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,32,68]
      [(128,54),(68,112),(20,82),(12,80),(2,9),(1,8)]
      (codeMat 401) (codeMat 282) (codeMat 267) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit31_lb15
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(292,128),(132,127),(80,28),(12,96),(2,9),(1,8)]
      (codeMat 185) (codeMat 282) (codeMat 267) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(308,252),(132,126),(80,20),(12,104),(2,9),(1,8)]
      (codeMat 177) (codeMat 314) (codeMat 271) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [256,128,68,32,20,8,2,1]
      [(256,256),(132,68),(64,128),(32,32),(16,8),(12,20),(2,1),(1,2)]
      (codeMat 273) (codeMat 266) (codeMat 266) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_3
  · exact quotientRankAtLeast_of_code_transport
      [256,128,68,32,20,8,2,1]
      [(260,256),(132,69),(64,130),(36,32),(16,9),(12,22),(2,1),(1,2)]
      (codeMat 345) (codeMat 266) (codeMat 266) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_3

theorem sources260_contain : ∀ i g, g ∈ [80,12,2,1] →
    spanContainsCode (sources260 i) g = true := by
  decide +kernel

theorem sources260_cover : ∀ c : Fin 512,
    ∃ i : Fin 7, spanContainsCode (sources260 i) c.val = true := by
  decide +kernel

theorem capacity260 (r : Nat) (hr : r < 16) (hlower : ∀ i, lower260 i ≤ r) :
    (∑ i : Fin 7, (r - lower260 i)) < r := by
  have h15 : 15 ≤ r := hlower 1
  have heq : r = 15 := by omega
  subst r
  decide +kernel

theorem span260_lb16 : QuotientRankAtLeast (spanCodes [80,12,2,1]) 16 :=
  quotientRankAtLeast_of_mixed_code_cover _ sources260 lower260
    sources260_rank sources260_contain sources260_cover capacity260

theorem rep260 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 260))
      (frozenWangTable.lower 260) := by
  exact span260_lb16

end QiushiMatmul.FrozenRank
