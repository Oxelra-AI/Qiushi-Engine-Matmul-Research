import QiushiFrozenRankCover

open BigOperators

namespace QiushiMatmul

/-- A cover may use a different proved quotient bound for each source. -/
theorem decomp_length_le_sum_cover_capacities {W : Submodule F2 Mat3}
    {n r : Nat} (U : Fin n → Submodule F2 Mat3) (lower : Fin n → Nat)
    (hWU : ∀ i, W ≤ U i)
    (hRank : ∀ i, QuotientRankAtLeast (U i) (lower i))
    (hCover : ∀ M : Mat3, ∃ i, M ∈ U i)
    (D : QuotientTensorDecomp W r) (hmr : ∀ i, lower i ≤ r) :
    r ≤ ∑ i : Fin n, (r - lower i) := by
  classical
  calc
    r = (Finset.univ : Finset (Fin r)).card := by simp
    _ ≤ (Finset.univ.biUnion (fun i : Fin n => killSet D (U i))).card := by
      apply Finset.card_le_card
      intro t _
      obtain ⟨i, hi⟩ := hCover (D.A t)
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa [killSet] using hi⟩
    _ ≤ ∑ i : Fin n, (killSet D (U i)).card := Finset.card_biUnion_le
    _ ≤ ∑ i : Fin n, (r - lower i) :=
      Finset.sum_le_sum (fun i _ => occupation_inequality (hWU i) D (hRank i) (hmr i))

/-- Exact code-level covers turn a finite capacity contradiction into a rank bound. -/
theorem quotientRankAtLeast_of_mixed_code_cover {n bound : Nat} (basis : List Nat)
    (sources : Fin n → List Nat) (lower : Fin n → Nat)
    (hRank : ∀ i, QuotientRankAtLeast (spanCodes (sources i)) (lower i))
    (hLe : ∀ i g, g ∈ basis → spanContainsCode (sources i) g = true)
    (hCover : ∀ c : Fin 512, ∃ i, spanContainsCode (sources i) c.val = true)
    (hCapacity : ∀ r, r < bound → (∀ i, lower i ≤ r) →
      (∑ i : Fin n, (r - lower i)) < r) :
    QuotientRankAtLeast (spanCodes basis) bound := by
  classical
  have hWU : ∀ i, spanCodes basis ≤ spanCodes (sources i) := by
    intro i
    apply Submodule.span_le.mpr
    rintro M ⟨g, hg, rfl⟩
    exact spanContainsCode_implies_mem_spanCodes _ _ (hLe i g hg)
  have hActualCover : ∀ M : Mat3, ∃ i, M ∈ spanCodes (sources i) := by
    intro M
    obtain ⟨i, hi⟩ := hCover (matrixCode M)
    refine ⟨i, ?_⟩
    have hMem := spanContainsCode_implies_mem_spanCodes _ _ hi
    simpa only [matrixCode, codeMat_matrixCode] using hMem
  intro r hr
  refine ⟨fun D => ?_⟩
  by_cases hmr : ∀ i, lower i ≤ r
  · have hBound := decomp_length_le_sum_cover_capacities
      (fun i => spanCodes (sources i)) lower hWU hRank hActualCover D hmr
    exact (Nat.not_lt_of_ge hBound) (hCapacity r hr hmr)
  · obtain ⟨i, hi⟩ := not_forall.mp hmr
    exact quotient_bound_exceeds_length (hWU i) D (hRank i) (by omega)

end QiushiMatmul
