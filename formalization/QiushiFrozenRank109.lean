import QiushiFrozenRankCoverMixed
import QiushiCertifiedTransport
import QiushiOrbit25FP
import QiushiOrbit40FP
import QiushiOrbit41FP
import QiushiOrbit10FP
import QiushiFrozenWangData

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open BigOperators

namespace QiushiMatmul.FrozenRank

def sources109 : Fin 12 → List Nat := ![
  [256,80,8,4,2,1],
  [256,64,20,8,2,1],
  [256,84,32,8,2,1],
  [256,84,36,8,2,1],
  [256,84,48,8,2,1],
  [256,84,52,8,2,1],
  [256,128,84,8,2,1],
  [256,132,84,8,2,1],
  [256,144,84,8,2,1],
  [256,148,84,8,2,1],
  [256,160,68,16,8,2,1],
  [256,164,68,16,8,2,1]]

def lower109 : Fin 12 → Nat := fun _ => 12

theorem sources109_rank (i : Fin 12) :
    QuotientRankAtLeast (spanCodes (sources109 i)) (lower109 i) := by
  fin_cases i
  · exact quotientRankAtLeast_of_code_transport
      [1,2,4,8,80,256]
      [(256,256),(80,80),(8,8),(4,4),(2,2),(1,1)]
      (codeMat 273) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit25_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,4,8,80,256]
      [(256,256),(64,4),(20,80),(8,2),(2,8),(1,1)]
      (codeMat 273) (codeMat 273) (codeMat 273) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit25_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,32,84,128]
      [(256,32),(84,84),(32,8),(8,1),(2,128),(1,2)]
      (codeMat 266) (codeMat 161) (codeMat 161) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit40_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,32,84,128]
      [(256,32),(84,212),(36,8),(8,3),(2,128),(1,2)]
      (codeMat 267) (codeMat 161) (codeMat 161) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit40_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,32,84,384]
      [(256,384),(84,86),(48,32),(8,8),(2,2),(1,1)]
      (codeMat 273) (codeMat 305) (codeMat 305) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit41_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,32,84,384]
      [(256,384),(84,84),(52,34),(8,9),(2,2),(1,1)]
      (codeMat 281) (codeMat 305) (codeMat 305) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit41_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,32,84,128]
      [(256,128),(128,2),(84,84),(8,32),(2,1),(1,8)]
      (codeMat 161) (codeMat 266) (codeMat 266) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit40_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,32,84,384]
      [(256,384),(132,118),(84,84),(8,2),(2,9),(1,1)]
      (codeMat 401) (codeMat 275) (codeMat 275) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit41_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,32,84,384]
      [(256,384),(144,32),(84,86),(8,2),(2,8),(1,1)]
      (codeMat 401) (codeMat 273) (codeMat 273) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit41_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,32,84,128]
      [(256,128),(148,118),(84,116),(8,32),(2,9),(1,8)]
      (codeMat 161) (codeMat 282) (codeMat 267) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit40_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,16,68,160,256]
      [(256,256),(160,160),(68,68),(16,16),(8,8),(2,2),(1,1)]
      (codeMat 273) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit10_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,16,68,160,256]
      [(256,256),(164,160),(68,68),(16,18),(8,9),(2,2),(1,1)]
      (codeMat 281) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit10_lb12

theorem sources109_contain : ∀ i g, g ∈ [256,84,8,2,1] →
    spanContainsCode (sources109 i) g = true := by
  decide +kernel

theorem sources109_cover : ∀ c : Fin 512,
    ∃ i : Fin 12, spanContainsCode (sources109 i) c.val = true := by
  decide +kernel

theorem capacity109 (r : Nat) (hr : r < 14) (hlower : ∀ i, lower109 i ≤ r) :
    (∑ i : Fin 12, (r - lower109 i)) < r := by
  have h12 : 12 ≤ r := hlower 0
  have hr_cases : r = 12 ∨ r = 13 := by omega
  rcases hr_cases with rfl | rfl <;> decide +kernel

theorem span109_lb14 : QuotientRankAtLeast (spanCodes [256,84,8,2,1]) 14 :=
  quotientRankAtLeast_of_mixed_code_cover _ sources109 lower109
    sources109_rank sources109_contain sources109_cover capacity109

theorem rep109 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 109))
      (frozenWangTable.lower 109) := by
  exact span109_lb14

end QiushiMatmul.FrozenRank
