import QiushiOccupation
import QiushiExtractionBridge
import QiushiCodeSpanBridgeCore
import QiushiLineOrbit

open BigOperators

namespace QiushiMatmul

/-- A finite cover bounds the number of terms by the sum of kill capacities. -/
theorem decomp_length_le_cover_capacity {W : Submodule F2 Mat3}
    {n m r : Nat} (U : Fin n → Submodule F2 Mat3)
    (hWU : ∀ i, W ≤ U i)
    (hRank : ∀ i, QuotientRankAtLeast (U i) m)
    (hCover : ∀ M : Mat3, ∃ i, M ∈ U i)
    (D : QuotientTensorDecomp W r) (hmr : m ≤ r) :
    r ≤ n * (r - m) := by
  classical
  have hUnion : (Finset.univ : Finset (Fin r)) =
      Finset.univ.biUnion (fun i : Fin n => killSet D (U i)) := by
    apply Finset.Subset.antisymm
    · intro t _
      obtain ⟨i, hi⟩ := hCover (D.A t)
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa [killSet] using hi⟩
    · exact Finset.subset_univ _
  calc
    r = (Finset.univ : Finset (Fin r)).card := by simp
    _ = (Finset.univ.biUnion (fun i : Fin n => killSet D (U i))).card :=
      congrArg Finset.card hUnion
    _ ≤ ∑ i : Fin n, (killSet D (U i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin n, (r - m) :=
      Finset.sum_le_sum (fun i _ => occupation_inequality (hWU i) D (hRank i) hmr)
    _ = n * (r - m) := by simp

/-- Seven rank-nine quotients covering every A-factor exclude length ten. -/
theorem quotientRankAtLeast_eleven_of_seven_cover {W : Submodule F2 Mat3}
    (U : Fin 7 → Submodule F2 Mat3)
    (hWU : ∀ i, W ≤ U i)
    (hRank : ∀ i, QuotientRankAtLeast (U i) 9)
    (hCover : ∀ M : Mat3, ∃ i, M ∈ U i) :
    QuotientRankAtLeast W 11 := by
  intro r hr
  refine ⟨fun D => ?_⟩
  by_cases hmr : 9 ≤ r
  · have h := decomp_length_le_cover_capacity U hWU hRank hCover D hmr
    omega
  · exact quotient_bound_exceeds_length (hWU 0) D (hRank 0) (by omega)

/-- Code checks certify an actual matrix cover, not merely a cover of labels. -/
theorem quotientRankAtLeast_eleven_of_seven_code_cover (basis : List Nat)
    (sources : Fin 7 → List Nat)
    (hRank : ∀ i, QuotientRankAtLeast (spanCodes (sources i)) 9)
    (hLe : ∀ i g, g ∈ basis → spanContainsCode (sources i) g = true)
    (hCover : ∀ c : Fin 512, ∃ i, spanContainsCode (sources i) c.val = true) :
    QuotientRankAtLeast (spanCodes basis) 11 := by
  apply quotientRankAtLeast_eleven_of_seven_cover (fun i => spanCodes (sources i))
  · intro i
    apply Submodule.span_le.mpr
    rintro M ⟨g, hg, rfl⟩
    exact spanContainsCode_implies_mem_spanCodes _ _ (hLe i g hg)
  · exact hRank
  · intro M
    obtain ⟨i, hi⟩ := hCover (matrixCode M)
    refine ⟨i, ?_⟩
    have hMem := spanContainsCode_implies_mem_spanCodes _ _ hi
    simpa only [matrixCode, codeMat_matrixCode] using hMem

end QiushiMatmul
