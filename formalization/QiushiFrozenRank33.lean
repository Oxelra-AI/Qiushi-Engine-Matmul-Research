import QiushiFrozenRankCoverMixed
import QiushiFrozenRank24
import QiushiOrbit11FP
import QiushiOrbit13FP

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open BigOperators

namespace QiushiMatmul.FrozenRank

def sources033 : Fin 7 → List Nat := ![
  [160,64,16,8,4,2,1],
  [128,68,32,20,8,2,1],
  [132,68,36,20,8,2,1],
  [256,160,68,20,8,2,1],
  [260,160,68,20,8,2,1],
  [288,160,68,20,8,2,1],
  [292,160,68,20,8,2,1]]

def lower033 : Fin 7 → Nat := ![9,12,12,12,12,12,12]

theorem sources033_rank (i : Fin 7) :
    QuotientRankAtLeast (spanCodes (sources033 i)) (lower033 i) := by
  fin_cases i
  · exact sources024_rank 0
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,32,68,128]
      [(128,128),(68,68),(32,32),(20,20),(8,8),(2,2),(1,1)]
      (codeMat 273) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit11_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,32,68,128]
      [(132,100),(68,68),(36,128),(20,91),(8,3),(2,9),(1,1)]
      (codeMat 281) (codeMat 275) (codeMat 275) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit11_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,68,160,256]
      [(256,256),(160,160),(68,68),(20,20),(8,8),(2,2),(1,1)]
      (codeMat 273) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit13_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,68,160,256]
      [(260,256),(160,162),(68,69),(20,20),(8,8),(2,2),(1,1)]
      (codeMat 337) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit13_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,68,160,256]
      [(288,256),(160,182),(68,77),(20,22),(8,9),(2,2),(1,1)]
      (codeMat 409) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit13_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,68,160,256]
      [(292,256),(160,180),(68,76),(20,22),(8,9),(2,2),(1,1)]
      (codeMat 473) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit13_lb12

theorem sources033_contain : ∀ i g, g ∈ [160,68,20,8,2,1] →
    spanContainsCode (sources033 i) g = true := by
  decide +kernel

theorem sources033_cover : ∀ c : Fin 512,
    ∃ i : Fin 7, spanContainsCode (sources033 i) c.val = true := by
  decide +kernel

theorem capacity033 (r : Nat) (hr : r < 14) (hlower : ∀ i, lower033 i ≤ r) :
    (∑ i : Fin 7, (r - lower033 i)) < r := by
  have h12 : 12 ≤ r := hlower 1
  simp [lower033, Fin.sum_univ_succ]
  omega

theorem span033_lb14 : QuotientRankAtLeast (spanCodes [160,68,20,8,2,1]) 14 :=
  quotientRankAtLeast_of_mixed_code_cover _ sources033 lower033
    sources033_rank sources033_contain sources033_cover capacity033

theorem rep033 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 33))
      (frozenWangTable.lower 33) := by
  exact span033_lb14

end QiushiMatmul.FrozenRank
