import QiushiFrozenRankCoverMixed
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiWcOrbit204Dispatch
import QiushiPlane315GenBindings00
import QiushiStep81Qdim2Generated
import QiushiFlattenSeeds
import QiushiFrozenWangData

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open BigOperators

namespace QiushiMatmul.FrozenRank

def sources314 : Fin 7 → List Nat := ![
  [258,160,66,10,4,1],
  [258,160,64,10,6,1],
  [258,160,68,16,10,1],
  [258,160,68,18,10,1],
  [258,132,68,36,22,10,1],
  [258,134,68,38,22,10,1],
  [256,128,68,32,20,8,2,1]]

def lower314 : Fin 7 → Nat := ![15,15,15,15,14,14,9]

theorem sources314_rank (i : Fin 7) :
    QuotientRankAtLeast (spanCodes (sources314 i)) (lower314 i) := by
  fin_cases i
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(258,31),(160,252),(66,22),(10,148),(4,3),(1,2)]
      (codeMat 489) (codeMat 172) (codeMat 99) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(258,136),(160,232),(64,3),(10,150),(6,128),(1,2)]
      (codeMat 205) (codeMat 177) (codeMat 417) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact step109wc204s0Dispatch
  · exact quotientRankAtLeast_of_code_transport
      [260,160,68,16,10,1]
      [(258,506),(160,170),(68,78),(18,320),(10,68),(1,1)]
      (codeMat 241) (codeMat 423) (codeMat 181) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      plane315GenBound0009
  · exact quotientRankAtLeast_of_code_transport
      [262,128,68,32,20,10,1]
      [(258,21),(132,42),(68,322),(36,1),(22,10),(10,208),(1,128)]
      (codeMat 459) (codeMat 84) (codeMat 84) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step81o17s4Span_lb
  · exact quotientRankAtLeast_of_code_transport
      [262,128,68,32,20,10,1]
      [(258,53),(134,43),(68,374),(38,10),(22,11),(10,81),(1,219)]
      (codeMat 410) (codeMat 125) (codeMat 348) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step81o17s4Span_lb
  · exact flatSeed_3

theorem sources314_contain : ∀ i g, g ∈ [258,160,10,1] →
    spanContainsCode (sources314 i) g = true := by
  decide +kernel

theorem sources314_cover : ∀ c : Fin 512,
    ∃ i : Fin 7, spanContainsCode (sources314 i) c.val = true := by
  decide +kernel

theorem capacity314 (r : Nat) (hr : r < 17) (hlower : ∀ i, lower314 i ≤ r) :
    (∑ i : Fin 7, (r - lower314 i)) < r := by
  have h15 : 15 ≤ r := hlower 0
  have hr_cases : r = 15 ∨ r = 16 := by omega
  rcases hr_cases with rfl | rfl <;> decide +kernel

theorem span314_lb17 : QuotientRankAtLeast (spanCodes [258,160,10,1]) 17 :=
  quotientRankAtLeast_of_mixed_code_cover _ sources314 lower314
    sources314_rank sources314_contain sources314_cover capacity314

theorem rep314 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 314))
      (frozenWangTable.lower 314) := by
  exact span314_lb17

end QiushiMatmul.FrozenRank
