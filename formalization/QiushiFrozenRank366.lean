import QiushiFrozenRankCoverMixed
import QiushiCertifiedTransport
import QiushiWcOrbit127Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit128Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit214Dispatch
import QiushiBranch262Dispatch
import QiushiWcOrbit156Dispatch
import QiushiPlane315GenBindings00
import QiushiOrbit35FP
import QiushiOrbit11FP
import QiushiStep81Qdim2Generated
import QiushiFrozenWangData

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open BigOperators

namespace QiushiMatmul.FrozenRank

def sources366 : Fin 13 → List Nat := ![
  [268,160,20,2,1],
  [268,160,70,20,1],
  [268,160,72,20,1],
  [268,160,74,20,1],
  [268,160,102,20,1],
  [268,160,110,20,1],
  [258,160,16,10,4,1],
  [256,160,18,10,6,1],
  [262,132,36,20,10,1],
  [268,130,66,34,20,1],
  [268,138,64,42,20,1],
  [260,128,68,32,20,8,1],
  [262,134,68,38,20,10,1]]

def lower366 : Fin 13 → Nat := ![15,16,15,16,16,16,14,14,15,15,15,12,14]

theorem sources366_rank (i : Fin 13) :
    QuotientRankAtLeast (spanCodes (sources366 i)) (lower366 i) := by
  fin_cases i
  · exact quotientRankAtLeast_of_code_transport
      [272,96,12,2,1]
      [(268,284),(160,96),(20,12),(2,1),(1,3)]
      (codeMat 273) (codeMat 267) (codeMat 282) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      QiushiMatmul.step109_orbit127_lb15_wc
  · exact quotientRankAtLeast_of_code_transport
      [340,132,32,10,1]
      [(268,132),(160,350),(70,10),(20,497),(1,1)]
      (codeMat 489) (codeMat 405) (codeMat 407) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      QiushiMatmul.step109_orbit201_lb16_wc
  · exact quotientRankAtLeast_of_code_transport
      [384,96,12,2,1]
      [(268,386),(160,108),(72,1),(20,483),(1,3)]
      (codeMat 190) (codeMat 405) (codeMat 407) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      QiushiMatmul.step109_orbit128_lb15_wc
  · exact quotientRankAtLeast_of_code_transport
      [276,132,96,10,1]
      [(268,497),(160,276),(74,10),(20,132),(1,1)]
      (codeMat 241) (codeMat 305) (codeMat 305) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      QiushiMatmul.step109_orbit213_lb16_wc
  · exact quotientRankAtLeast_of_code_transport
      [294,136,96,20,1]
      [(268,21),(160,252),(102,116),(20,462),(1,1)]
      (codeMat 425) (codeMat 167) (codeMat 167) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      QiushiMatmul.step109_orbit238_lb16_wc
  · exact quotientRankAtLeast_of_code_transport
      [278,132,96,10,1]
      [(268,96),(160,402),(110,143),(20,228),(1,504)]
      (codeMat 167) (codeMat 474) (codeMat 395) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      QiushiMatmul.step109_orbit214_lb16_wc
  · exact quotientRankAtLeast_of_code_transport
      [272,132,32,12,2,1]
      [(258,132),(160,272),(16,32),(10,12),(4,2),(1,1)]
      (codeMat 273) (codeMat 161) (codeMat 161) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      QiushiMatmul.step113_262_row11_qr
  · exact quotientRankAtLeast_of_code_transport
      [272,132,32,12,2,1]
      [(256,438),(160,274),(18,32),(10,13),(6,2),(1,1)]
      (codeMat 409) (codeMat 417) (codeMat 177) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      QiushiMatmul.step113_262_row11_qr
  · exact quotientRankAtLeast_of_code_transport
      [258,68,32,20,10,1]
      [(262,43),(132,30),(36,1),(20,33),(10,265),(1,365)]
      (codeMat 187) (codeMat 95) (codeMat 244) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      QiushiMatmul.step109wc156s1Dispatch
  · exact quotientRankAtLeast_of_code_transport
      [260,160,68,16,10,1]
      [(268,238),(130,260),(66,261),(34,176),(20,160),(1,320)]
      (codeMat 92) (codeMat 481) (codeMat 185) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      QiushiMatmul.plane315GenBound0009
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(268,151),(138,148),(64,130),(42,104),(20,224),(1,128)]
      (codeMat 93) (codeMat 428) (codeMat 107) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      QiushiMatmul.orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,32,68,128]
      [(260,54),(128,219),(68,53),(32,9),(20,100),(8,8),(1,40)]
      (codeMat 242) (codeMat 190) (codeMat 355) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      QiushiMatmul.orbit11_lb12
  · exact quotientRankAtLeast_of_code_transport
      [262,128,68,32,20,10,1]
      [(262,149),(134,509),(68,322),(38,148),(20,294),(10,402),(1,128)]
      (codeMat 142) (codeMat 214) (codeMat 214) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      QiushiMatmul.step81o17s4Span_lb

theorem sources366_contain : ∀ i g, g ∈ [268,160,20,1] →
    spanContainsCode (sources366 i) g = true := by
  decide +kernel

theorem sources366_cover : ∀ c : Fin 512,
    ∃ i : Fin 13, spanContainsCode (sources366 i) c.val = true := by
  decide +kernel

theorem capacity366 (r : Nat) (hr : r < 17) (hlower : ∀ i, lower366 i ≤ r) :
    (∑ i : Fin 13, (r - lower366 i)) < r := by
  have h16 : 16 ≤ r := hlower 1
  have heq : r = 16 := by omega
  subst r
  decide +kernel

theorem span366_lb17 : QuotientRankAtLeast (spanCodes [268,160,20,1]) 17 :=
  quotientRankAtLeast_of_mixed_code_cover _ sources366 lower366
    sources366_rank sources366_contain sources366_cover capacity366

theorem rep366 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 366))
      (frozenWangTable.lower 366) := by
  exact span366_lb17

end QiushiMatmul.FrozenRank
