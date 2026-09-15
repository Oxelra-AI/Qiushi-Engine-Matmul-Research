import QiushiFrozenRankCoverMixed
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiMonoOrbit71From17
import QiushiOrbit14FP
import QiushiFrozenWangData

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open BigOperators

namespace QiushiMatmul.FrozenRank

def sources162 : Fin 7 → List Nat := ![
  [128,96,20,8,2,1],
  [128,68,36,20,10,1],
  [128,70,38,20,10,1],
  [256,128,96,16,10,4,1],
  [290,128,96,18,10,6,1],
  [262,128,64,32,20,10,1],
  [258,128,66,34,20,10,1]]

def lower162 : Fin 7 → Nat := ![15,14,14,12,12,12,12]

theorem sources162_rank (i : Fin 7) :
    QuotientRankAtLeast (spanCodes (sources162 i)) (lower162 i) := by
  fin_cases i
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(128,128),(96,96),(20,20),(8,8),(2,2),(1,1)]
      (codeMat 273) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [128,68,32,20,10,1]
      [(128,63),(68,78),(36,219),(20,91),(10,11),(1,1)]
      (codeMat 465) (codeMat 311) (codeMat 307) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit71_lb14_mono
  · exact quotientRankAtLeast_of_code_transport
      [128,68,32,20,10,1]
      [(128,63),(70,79),(38,139),(20,90),(10,10),(1,1)]
      (codeMat 409) (codeMat 279) (codeMat 279) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit71_lb14_mono
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128,256]
      [(256,2),(128,128),(96,20),(16,256),(10,96),(4,1),(1,8)]
      (codeMat 161) (codeMat 140) (codeMat 98) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit14_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128,256]
      [(290,131),(128,9),(96,252),(18,8),(10,352),(6,128),(1,256)]
      (codeMat 95) (codeMat 102) (codeMat 156) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit14_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128,256]
      [(262,139),(128,9),(64,1),(32,360),(20,245),(10,30),(1,3)]
      (codeMat 428) (codeMat 307) (codeMat 311) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit14_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128,256]
      [(258,224),(128,256),(66,96),(34,227),(20,284),(10,97),(1,8)]
      (codeMat 270) (codeMat 165) (codeMat 163) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit14_lb12

theorem sources162_contain : ∀ i g, g ∈ [128,96,20,10,1] →
    spanContainsCode (sources162 i) g = true := by
  decide +kernel

theorem sources162_cover : ∀ c : Fin 512,
    ∃ i : Fin 7, spanContainsCode (sources162 i) c.val = true := by
  decide +kernel

theorem capacity162 (r : Nat) (hr : r < 16) (hlower : ∀ i, lower162 i ≤ r) :
    (∑ i : Fin 7, (r - lower162 i)) < r := by
  have h15 : 15 ≤ r := hlower 0
  have heq : r = 15 := by omega
  subst r
  decide +kernel

theorem span162_lb16 : QuotientRankAtLeast (spanCodes [128,96,20,10,1]) 16 :=
  quotientRankAtLeast_of_mixed_code_cover _ sources162 lower162
    sources162_rank sources162_contain sources162_cover capacity162

theorem rep162 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 162))
      (frozenWangTable.lower 162) := by
  exact span162_lb16

end QiushiMatmul.FrozenRank
