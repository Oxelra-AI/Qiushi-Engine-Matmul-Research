import QiushiDefs
import QiushiOrbitTransport
import QiushiMatmulFinitePremises
import QiushiOccupationAPI
import QiushiCodeSpanBridge

/-!
# Line bounds from plane bounds via GL transport and monotonicity

All three line lower bounds follow from plane bounds, eliminating
417,197-row line occupation proofs entirely.
-/

open Matrix BigOperators

set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

noncomputable section

namespace QiushiMatmul

-- ============================================================================
-- Plane definitions
-- ============================================================================

def plane479 : Submodule F2 Mat3 := spanCodes [1, 10]

-- ============================================================================
-- Containment: lineRank1 ≤ plane479
-- ============================================================================

theorem lineRank1_le_plane479 : lineRank1 ≤ plane479 := by
  show spanCodes [1] ≤ spanCodes [1, 10]
  apply Submodule.span_mono
  rintro M ⟨n, hn, rfl⟩
  refine ⟨n, ?_, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn ⊢
  exact Or.inl hn

-- ============================================================================
-- Monotonicity
-- ============================================================================

theorem quotientRankAtLeast_mono' {W U : Submodule F2 Mat3} {r : ℕ}
    (hWU : W ≤ U) (hU : QuotientRankAtLeast U r) : QuotientRankAtLeast W r :=
  quotientRankAtLeast_of_contradiction W r
    (fun _m hm D => quotient_bound_exceeds_length hWU D hU hm)

-- ============================================================================
-- Helper lemmas for transport
-- ============================================================================

/-- Helper: codeMat witness ∈ W and linear map sends it to target
    implies target ∈ W.map (linear map). -/
theorem codeMat_mem_actionW_of_witness
    {P Q : Mat3} [Invertible P] [Invertible Q]
    {W : Submodule F2 Mat3} {witness target : ℕ}
    (h_mem : codeMat witness ∈ W)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q W := by
  change ∃ X, X ∈ W ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Singleton span ≤ submodule when the generator is in the submodule. -/
theorem spanCodes_singleton_le
    {S : Submodule F2 Mat3} {n : ℕ}
    (h : codeMat n ∈ S) :
    spanCodes [n] ≤ S := by
  apply Submodule.span_le.mpr
  rintro M ⟨k, hk, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  subst hk; exact h

-- ============================================================================
-- lineRank2 lb≥19 from plane484
-- ============================================================================

/-- lineRank2 lb≥19 from plane484 lb≥19.
    Preimage: codeMat 25 ∈ plane484 (25 = 19 XOR 10).
    actionA(266,267)(codeMat 25) = codeMat 17.
    We resolve Q⁻¹ = codeMat 282 explicitly before decide. -/
theorem lineRank2_lb19_from_plane484
    (h484 : QuotientRankAtLeast plane484 19) :
    QuotientRankAtLeast lineRank2 19 := by
  have hP : Invertible (codeMat 266 : Mat3) :=
    Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 267 : Mat3) :=
    Matrix.invertibleOfIsUnitDet _ (by decide)
  -- Transport: plane484 lb19 → actionW(plane484) lb19
  have h_act : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 267) plane484) 19 :=
    @quotientRankAtLeast_action _ _ hP hQ _ _ h484
  -- Preimage witness
  have h_wit_mem : codeMat 25 ∈ (plane484 : Submodule F2 Mat3) :=
    spanContainsCode_implies_mem_spanCodes [19, 10] 25 (by decide)
  -- Resolve `(Qᵀ)⁻¹` explicitly, then compute the product.  This avoids
  -- asking the simplifier to normalize matrix inverse/transposition itself.
  have hQt_inv : (codeMat 267 : Mat3).transpose⁻¹ = (codeMat 282 : Mat3).transpose := by
    apply Matrix.inv_eq_right_inv
    show (codeMat 267 : Mat3).transpose * (codeMat 282 : Mat3).transpose = 1
    ext i j <;> fin_cases i <;> fin_cases j <;> decide
  have h_action : actionA (codeMat 266) (codeMat 267) (codeMat 25) = codeMat 17 := by
    unfold actionA
    rw [hQt_inv]
    show (codeMat 266 : Mat3).transpose * codeMat 25 * (codeMat 282 : Mat3).transpose = codeMat 17
    ext i j <;> fin_cases i <;> fin_cases j <;> decide
  -- Combine: codeMat 17 ∈ actionW, hence lineRank2 ≤ actionW
  have h17_mem := codeMat_mem_actionW_of_witness h_wit_mem h_action
  exact quotientRankAtLeast_mono' (spanCodes_singleton_le h17_mem) h_act

-- ============================================================================
-- lineRank3 lb≥19 from plane488
-- ============================================================================

/-- lineRank3 lb≥19 from plane488 lb≥19.
    Preimage: codeMat 106 ∈ plane488 (106 = 96 XOR 10).
    actionA(92,226)(codeMat 106) = codeMat 273.
    Q⁻¹ = codeMat 141, (Q⁻¹)ᵀ = codeMat 99. -/
theorem lineRank3_lb19_from_plane488
    (h488 : QuotientRankAtLeast plane488 19) :
    QuotientRankAtLeast lineRank3 19 := by
  have hP : Invertible (codeMat 92 : Mat3) :=
    Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) :=
    Matrix.invertibleOfIsUnitDet _ (by decide)
  have h_act : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 226) plane488) 19 :=
    @quotientRankAtLeast_action _ _ hP hQ _ _ h488
  -- Preimage: codeMat 106 = codeMat(96 XOR 10) ∈ plane488 = spanCodes [96, 10]
  have h_wit_mem : codeMat 106 ∈ (plane488 : Submodule F2 Mat3) :=
    spanContainsCode_implies_mem_spanCodes [96, 10] 106 (by decide)
  -- Resolve `(Qᵀ)⁻¹` explicitly.
  have hQt_inv : (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
    apply Matrix.inv_eq_right_inv
    show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
    ext i j <;> fin_cases i <;> fin_cases j <;> decide
  have h_action : actionA (codeMat 92) (codeMat 226) (codeMat 106) = codeMat 273 := by
    unfold actionA
    rw [hQt_inv]
    show (codeMat 92 : Mat3).transpose * codeMat 106 * (codeMat 141 : Mat3).transpose = codeMat 273
    ext i j <;> fin_cases i <;> fin_cases j <;> decide
  have h273_mem := codeMat_mem_actionW_of_witness h_wit_mem h_action
  exact quotientRankAtLeast_mono' (spanCodes_singleton_le h273_mem) h_act

-- ============================================================================
-- lineRank1 lb≥19 from plane479
-- ============================================================================

/-- lineRank1 lb≥19 from plane479 lb≥19. Direct containment, no transport. -/
theorem lineRank1_lb19_from_plane479
    (h479 : QuotientRankAtLeast plane479 19) :
    QuotientRankAtLeast lineRank1 19 :=
  quotientRankAtLeast_mono' lineRank1_le_plane479 h479

end QiushiMatmul
end
