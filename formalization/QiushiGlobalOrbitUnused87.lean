import QiushiFrozenRankCover
import QiushiCertifiedTransport
import QiushiOrbit5FP
import QiushiFrozenWangData

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace QiushiMatmul.GlobalOrbit.Unused

def sources087 : Fin 9 → List Nat := ![
  [160,64,16,8,4,2,1],
  [272,64,32,8,4,2,1],
  [400,64,48,8,4,2,1],
  [272,128,64,8,4,2,1],
  [304,144,64,8,4,2,1],
  [256,160,64,8,4,2,1],
  [272,160,64,8,4,2,1],
  [288,176,64,8,4,2,1],
  [304,176,64,8,4,2,1]]

theorem sources087_rank (i : Fin 9) :
    QuotientRankAtLeast (spanCodes (sources087 i)) 9 := by
  fin_cases i
  · exact quotientRankAtLeast_of_code_transport
      [1,2,4,8,16,64,160]
      [(160,160),(64,64),(16,16),(8,8),(4,4),(2,2),(1,1)]
      (codeMat 273) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit5_lb9
  · exact quotientRankAtLeast_of_code_transport
      [1,2,4,8,16,64,160]
      [(272,160),(64,4),(32,16),(8,2),(4,8),(2,64),(1,1)]
      (codeMat 273) (codeMat 161) (codeMat 161) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit5_lb9
  · exact quotientRankAtLeast_of_code_transport
      [1,2,4,8,16,64,160]
      [(400,160),(64,4),(48,16),(8,2),(4,72),(2,64),(1,1)]
      (codeMat 273) (codeMat 417) (codeMat 177) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit5_lb9
  · exact quotientRankAtLeast_of_code_transport
      [1,2,4,8,16,64,160]
      [(272,160),(128,16),(64,8),(8,64),(4,4),(2,2),(1,1)]
      (codeMat 161) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit5_lb9
  · exact quotientRankAtLeast_of_code_transport
      [1,2,4,8,16,64,160]
      [(304,160),(144,16),(64,72),(8,64),(4,4),(2,2),(1,1)]
      (codeMat 177) (codeMat 273) (codeMat 273) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit5_lb9
  · exact quotientRankAtLeast_of_code_transport
      [1,2,4,8,16,64,160]
      [(256,16),(160,160),(64,2),(8,4),(4,8),(2,64),(1,1)]
      (codeMat 161) (codeMat 161) (codeMat 161) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit5_lb9
  · exact quotientRankAtLeast_of_code_transport
      [1,2,4,8,16,64,160]
      [(272,176),(160,160),(64,6),(8,4),(4,72),(2,64),(1,1)]
      (codeMat 177) (codeMat 417) (codeMat 177) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit5_lb9
  · exact quotientRankAtLeast_of_code_transport
      [1,2,4,8,16,64,160]
      [(288,16),(176,160),(64,6),(8,4),(4,8),(2,64),(1,1)]
      (codeMat 177) (codeMat 161) (codeMat 161) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit5_lb9
  · exact quotientRankAtLeast_of_code_transport
      [1,2,4,8,16,64,160]
      [(304,176),(176,160),(64,2),(8,4),(4,72),(2,64),(1,1)]
      (codeMat 161) (codeMat 417) (codeMat 177) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit5_lb9

theorem sources087_contain : ∀ i g, g ∈ [64,8,4,2,1] →
    spanContainsCode (sources087 i) g = true := by
  decide +kernel

theorem sources087_cover : ∀ c : Fin 512,
    ∃ i : Fin 9, spanContainsCode (sources087 i) c.val = true := by
  decide +kernel

theorem node87_bound : QuotientRankAtLeast (spanCodes [64,8,4,2,1]) 11 := by
  have hLe : ∀ i : Fin 9, spanCodes [64,8,4,2,1] ≤ spanCodes (sources087 i) := by
    intro i
    apply Submodule.span_le.mpr
    rintro M ⟨g, hg, rfl⟩
    exact spanContainsCode_implies_mem_spanCodes _ _ (sources087_contain i g hg)
  have hCover : ∀ M : Mat3, ∃ i : Fin 9, M ∈ spanCodes (sources087 i) := by
    intro M
    obtain ⟨i, hi⟩ := sources087_cover (matrixCode M)
    refine ⟨i, ?_⟩
    have hMem := spanContainsCode_implies_mem_spanCodes _ _ hi
    simpa only [matrixCode, codeMat_matrixCode] using hMem
  intro r hr
  refine ⟨fun D => ?_⟩
  by_cases hmr : 9 ≤ r
  · have h := decomp_length_le_cover_capacity
      (fun i => spanCodes (sources087 i)) hLe sources087_rank hCover D hmr
    omega
  · exact quotient_bound_exceeds_length (hLe 0) D (sources087_rank 0) (by omega)

theorem rep087 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 87))
      (frozenWangTable.lower 87) := by
  rw [show frozenWangTable.basis 87 = [64,8,4,2,1] by decide +kernel,
      show frozenWangTable.lower 87 = 11 by decide +kernel]
  exact node87_bound

end QiushiMatmul.GlobalOrbit.Unused
