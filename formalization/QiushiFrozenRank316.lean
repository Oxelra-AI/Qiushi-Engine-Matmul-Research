import QiushiFrozenRank314
import QiushiStep99Orbit67Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open BigOperators

namespace QiushiMatmul.FrozenRank

def sources316 : Fin 7 → List Nat := ![
  [258,160,66,10,4,1],
  [256,160,64,10,6,1],
  [262,160,68,16,10,1],
  [262,160,68,18,10,1],
  [262,128,68,32,20,10,1],
  [262,130,68,34,20,10,1],
  [260,132,68,36,20,8,2,1]]

def lower316 : Fin 7 → Nat := ![15,15,15,15,14,14,9]

theorem sources316_rank (i : Fin 7) :
    QuotientRankAtLeast (spanCodes (sources316 i)) (lower316 i) := by
  fin_cases i
  · exact sources314_rank 0
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(256,8),(160,104),(64,1),(10,148),(6,128),(1,2)]
      (codeMat 140) (codeMat 177) (codeMat 417) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [260,160,68,16,10,1]
      [(262,496),(160,160),(68,78),(16,16),(10,10),(1,1)]
      (codeMat 401) (codeMat 305) (codeMat 305) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      plane315GenBound0009
  · exact quotientRankAtLeast_of_code_transport
      [262,164,68,16,10,1]
      [(262,328),(160,224),(68,68),(18,16),(10,11),(1,1)]
      (codeMat 281) (codeMat 273) (codeMat 273) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step99_orbit67_lb15_unconditional
  · exact step81o17s4Span_lb
  · exact quotientRankAtLeast_of_code_transport
      [262,128,68,32,20,10,1]
      [(262,52),(130,32),(68,402),(34,11),(20,10),(10,208),(1,128)]
      (codeMat 331) (codeMat 116) (codeMat 92) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step81o17s4Span_lb
  · exact quotientRankAtLeast_of_code_transport
      [256,128,68,32,20,8,2,1]
      [(260,288),(132,150),(68,77),(36,32),(20,22),(8,9),(2,2),(1,1)]
      (codeMat 409) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      flatSeed_3

theorem sources316_contain : ∀ i g, g ∈ [262,160,10,1] →
    spanContainsCode (sources316 i) g = true := by
  decide +kernel

theorem sources316_cover : ∀ c : Fin 512,
    ∃ i : Fin 7, spanContainsCode (sources316 i) c.val = true := by
  decide +kernel

theorem capacity316 (r : Nat) (hr : r < 17) (hlower : ∀ i, lower316 i ≤ r) :
    (∑ i : Fin 7, (r - lower316 i)) < r :=
  capacity314 r hr hlower

theorem span316_lb17 : QuotientRankAtLeast (spanCodes [262,160,10,1]) 17 :=
  quotientRankAtLeast_of_mixed_code_cover _ sources316 lower316
    sources316_rank sources316_contain sources316_cover capacity316

theorem rep316 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 316))
      (frozenWangTable.lower 316) := by
  exact span316_lb17

end QiushiMatmul.FrozenRank
