import QiushiFrozenRankCoverMixed
import QiushiCertifiedTransport
import QiushiStep99Orbit34Dispatch
import QiushiOrbit35FP
import QiushiWcOrbit156Dispatch
import QiushiOrbit10FP
import QiushiStep81Qdim2Generated
import QiushiFrozenWangData

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open BigOperators

namespace QiushiMatmul.FrozenRank

def sources318 : Fin 8 → List Nat := ![
  [290,160,66,10,4,1],
  [290,160,112,10,6,1],
  [260,134,64,38,10,1],
  [274,144,80,48,10,1],
  [288,160,68,16,8,2,1],
  [258,128,70,32,20,10,1],
  [256,130,70,34,20,10,1],
  [262,132,70,36,22,10,1]]

def lower318 : Fin 8 → Nat := ![14,15,15,15,12,14,14,14]

theorem sources318_rank (i : Fin 8) :
    QuotientRankAtLeast (spanCodes (sources318 i)) (lower318 i) := by
  fin_cases i
  · exact quotientRankAtLeast_of_code_transport
      [256,68,20,8,2,1]
      [(290,88),(160,336),(66,77),(10,79),(4,8),(1,1)]
      (codeMat 369) (codeMat 177) (codeMat 417) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step99_orbit34_lb14_unconditional
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(290,136),(160,224),(112,28),(10,119),(6,8),(1,9)]
      (codeMat 313) (codeMat 409) (codeMat 473) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(260,3),(134,28),(64,9),(38,224),(10,104),(1,8)]
      (codeMat 205) (codeMat 165) (codeMat 163) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [258,68,32,20,10,1]
      [(274,112),(144,1),(80,33),(48,63),(10,100),(1,365)]
      (codeMat 230) (codeMat 355) (codeMat 190) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step109wc156s1Dispatch
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,16,68,160,256]
      [(288,256),(160,69),(68,168),(16,1),(8,8),(2,2),(1,16)]
      (codeMat 394) (codeMat 266) (codeMat 266) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit10_lb12
  · exact quotientRankAtLeast_of_code_transport
      [262,128,68,32,20,10,1]
      [(258,20),(128,32),(70,274),(32,1),(20,10),(10,80),(1,128)]
      (codeMat 266) (codeMat 84) (codeMat 84) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step81o17s4Span_lb
  · exact quotientRankAtLeast_of_code_transport
      [262,128,68,32,20,10,1]
      [(256,63),(130,32),(70,508),(34,10),(20,11),(10,138),(1,219)]
      (codeMat 339) (codeMat 125) (codeMat 348) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step81o17s4Span_lb
  · exact quotientRankAtLeast_of_code_transport
      [262,128,68,32,20,10,1]
      [(262,30),(132,43),(70,374),(36,1),(22,11),(10,138),(1,219)]
      (codeMat 467) (codeMat 93) (codeMat 372) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step81o17s4Span_lb

theorem sources318_contain : ∀ i g, g ∈ [290,160,10,1] →
    spanContainsCode (sources318 i) g = true := by
  decide +kernel

theorem sources318_cover : ∀ c : Fin 512,
    ∃ i : Fin 8, spanContainsCode (sources318 i) c.val = true := by
  decide +kernel

theorem capacity318 (r : Nat) (hr : r < 17) (hlower : ∀ i, lower318 i ≤ r) :
    (∑ i : Fin 8, (r - lower318 i)) < r := by
  have h15 : 15 ≤ r := hlower 1
  have hr_cases : r = 15 ∨ r = 16 := by omega
  rcases hr_cases with rfl | rfl <;> decide +kernel

theorem span318_lb17 : QuotientRankAtLeast (spanCodes [290,160,10,1]) 17 :=
  quotientRankAtLeast_of_mixed_code_cover _ sources318 lower318
    sources318_rank sources318_contain sources318_cover capacity318

theorem rep318 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 318))
      (frozenWangTable.lower 318) := by
  exact span318_lb17

end QiushiMatmul.FrozenRank
