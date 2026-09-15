import QiushiDefs
import QiushiOrbitTransport
import QiushiMatmulFinitePremises
import QiushiLineFromPlane
import QiushiCodeSpanBridgeCore
import QiushiOccupationAPI

/-!
# Twelve-orbit-theorem to FinitePremises reducer

The corrected reducer supplies FinitePremises from twelve named
quotient-rank hypotheses:
  - the rank-one line bound at 19
  - 8 plane bounds: plane484..plane491 at 19
  - 3 hyperplane orbit bounds: affineHyperplane0 (orbit 414),
    affineHyperplane1 (orbit 415), affineHyperplane2 (orbit 416) at 17

The rank-two and rank-three line bounds derive from planes via QiushiLineFromPlane.
Hyperplanes 3-13 derive from hyperplane 2 via GL(3,F2)^2 transport.
-/

open Matrix BigOperators

set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

noncomputable section

namespace QiushiMatmul

-- ============================================================
-- affineHyperplane3 from affineHyperplane2 via GL transport
-- ============================================================

private noncomputable def hp3_hP : Invertible (codeMat 281 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private noncomputable def hp3_hQ : Invertible (codeMat 273 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private theorem hp3_hQtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp3_wit0 :
    codeMat 272 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 272 (by decide)

private theorem hp3_act0 :
    actionA (codeMat 281) (codeMat 273) (codeMat 272) = codeMat 274 := by
  unfold actionA
  rw [hp3_hQtInv]
  show (codeMat 281 : Mat3).transpose * codeMat 272 * (codeMat 273 : Mat3).transpose = codeMat 274
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp3_wit1 :
    codeMat 4 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 4 (by decide)

private theorem hp3_act1 :
    actionA (codeMat 281) (codeMat 273) (codeMat 4) = codeMat 4 := by
  unfold actionA
  rw [hp3_hQtInv]
  show (codeMat 281 : Mat3).transpose * codeMat 4 * (codeMat 273 : Mat3).transpose = codeMat 4
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp3_wit2 :
    codeMat 1 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 1 (by decide)

private theorem hp3_act2 :
    actionA (codeMat 281) (codeMat 273) (codeMat 1) = codeMat 1 := by
  unfold actionA
  rw [hp3_hQtInv]
  show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp3_contain :
    affineHyperplane3 ≤ actionW (codeMat 281) (codeMat 273) affineHyperplane2 := by
  letI := hp3_hP
  letI := hp3_hQ
  apply Submodule.span_le.mpr
  rintro M ⟨k, hk, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with h | h | h
  · subst h
    exact codeMat_mem_actionW_of_witness hp3_wit0 hp3_act0
  · subst h
    exact codeMat_mem_actionW_of_witness hp3_wit1 hp3_act1
  · subst h
    exact codeMat_mem_actionW_of_witness hp3_wit2 hp3_act2

theorem affineHyperplane3_lb17_from_hp2
    (h416 : QuotientRankAtLeast affineHyperplane2 17) :
    QuotientRankAtLeast affineHyperplane3 17 := by
  letI := hp3_hP
  letI := hp3_hQ
  have h_act : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 273) affineHyperplane2) 17 :=
    @quotientRankAtLeast_action _ _ hp3_hP hp3_hQ _ _ h416
  exact quotientRankAtLeast_mono' hp3_contain h_act

-- ============================================================
-- affineHyperplane4 from affineHyperplane2 via GL transport
-- ============================================================

private noncomputable def hp4_hP : Invertible (codeMat 273 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private noncomputable def hp4_hQ : Invertible (codeMat 281 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private theorem hp4_hQtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp4_wit0 :
    codeMat 272 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 272 (by decide)

private theorem hp4_act0 :
    actionA (codeMat 273) (codeMat 281) (codeMat 272) = codeMat 272 := by
  unfold actionA
  rw [hp4_hQtInv]
  show (codeMat 273 : Mat3).transpose * codeMat 272 * (codeMat 281 : Mat3).transpose = codeMat 272
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp4_wit1 :
    codeMat 4 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 4 (by decide)

private theorem hp4_act1 :
    actionA (codeMat 273) (codeMat 281) (codeMat 4) = codeMat 4 := by
  unfold actionA
  rw [hp4_hQtInv]
  show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 281 : Mat3).transpose = codeMat 4
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp4_wit2 :
    codeMat 1 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 1 (by decide)

private theorem hp4_act2 :
    actionA (codeMat 273) (codeMat 281) (codeMat 1) = codeMat 3 := by
  unfold actionA
  rw [hp4_hQtInv]
  show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 281 : Mat3).transpose = codeMat 3
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp4_contain :
    affineHyperplane4 ≤ actionW (codeMat 273) (codeMat 281) affineHyperplane2 := by
  letI := hp4_hP
  letI := hp4_hQ
  apply Submodule.span_le.mpr
  rintro M ⟨k, hk, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with h | h | h
  · subst h
    exact codeMat_mem_actionW_of_witness hp4_wit0 hp4_act0
  · subst h
    exact codeMat_mem_actionW_of_witness hp4_wit1 hp4_act1
  · subst h
    exact codeMat_mem_actionW_of_witness hp4_wit2 hp4_act2

theorem affineHyperplane4_lb17_from_hp2
    (h416 : QuotientRankAtLeast affineHyperplane2 17) :
    QuotientRankAtLeast affineHyperplane4 17 := by
  letI := hp4_hP
  letI := hp4_hQ
  have h_act : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 281) affineHyperplane2) 17 :=
    @quotientRankAtLeast_action _ _ hp4_hP hp4_hQ _ _ h416
  exact quotientRankAtLeast_mono' hp4_contain h_act

-- ============================================================
-- affineHyperplane5 from affineHyperplane2 via GL transport
-- ============================================================

private noncomputable def hp5_hP : Invertible (codeMat 281 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private noncomputable def hp5_hQ : Invertible (codeMat 281 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private theorem hp5_hQtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp5_wit0 :
    codeMat 273 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 273 (by decide)

private theorem hp5_act0 :
    actionA (codeMat 281) (codeMat 281) (codeMat 273) = codeMat 273 := by
  unfold actionA
  rw [hp5_hQtInv]
  show (codeMat 281 : Mat3).transpose * codeMat 273 * (codeMat 281 : Mat3).transpose = codeMat 273
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp5_wit1 :
    codeMat 4 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 4 (by decide)

private theorem hp5_act1 :
    actionA (codeMat 281) (codeMat 281) (codeMat 4) = codeMat 4 := by
  unfold actionA
  rw [hp5_hQtInv]
  show (codeMat 281 : Mat3).transpose * codeMat 4 * (codeMat 281 : Mat3).transpose = codeMat 4
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp5_wit2 :
    codeMat 1 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 1 (by decide)

private theorem hp5_act2 :
    actionA (codeMat 281) (codeMat 281) (codeMat 1) = codeMat 3 := by
  unfold actionA
  rw [hp5_hQtInv]
  show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 281 : Mat3).transpose = codeMat 3
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp5_contain :
    affineHyperplane5 ≤ actionW (codeMat 281) (codeMat 281) affineHyperplane2 := by
  letI := hp5_hP
  letI := hp5_hQ
  apply Submodule.span_le.mpr
  rintro M ⟨k, hk, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with h | h | h
  · subst h
    exact codeMat_mem_actionW_of_witness hp5_wit0 hp5_act0
  · subst h
    exact codeMat_mem_actionW_of_witness hp5_wit1 hp5_act1
  · subst h
    exact codeMat_mem_actionW_of_witness hp5_wit2 hp5_act2

theorem affineHyperplane5_lb17_from_hp2
    (h416 : QuotientRankAtLeast affineHyperplane2 17) :
    QuotientRankAtLeast affineHyperplane5 17 := by
  letI := hp5_hP
  letI := hp5_hQ
  have h_act : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 281) affineHyperplane2) 17 :=
    @quotientRankAtLeast_action _ _ hp5_hP hp5_hQ _ _ h416
  exact quotientRankAtLeast_mono' hp5_contain h_act

-- ============================================================
-- affineHyperplane6 from affineHyperplane2 via GL transport
-- ============================================================

private noncomputable def hp6_hP : Invertible (codeMat 161 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private noncomputable def hp6_hQ : Invertible (codeMat 161 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private theorem hp6_hQtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp6_wit0 :
    codeMat 272 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 272 (by decide)

private theorem hp6_act0 :
    actionA (codeMat 161) (codeMat 161) (codeMat 272) = codeMat 272 := by
  unfold actionA
  rw [hp6_hQtInv]
  show (codeMat 161 : Mat3).transpose * codeMat 272 * (codeMat 161 : Mat3).transpose = codeMat 272
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp6_wit1 :
    codeMat 4 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 4 (by decide)

private theorem hp6_act1 :
    actionA (codeMat 161) (codeMat 161) (codeMat 4) = codeMat 2 := by
  unfold actionA
  rw [hp6_hQtInv]
  show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 161 : Mat3).transpose = codeMat 2
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp6_wit2 :
    codeMat 1 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 1 (by decide)

private theorem hp6_act2 :
    actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
  unfold actionA
  rw [hp6_hQtInv]
  show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp6_contain :
    affineHyperplane6 ≤ actionW (codeMat 161) (codeMat 161) affineHyperplane2 := by
  letI := hp6_hP
  letI := hp6_hQ
  apply Submodule.span_le.mpr
  rintro M ⟨k, hk, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with h | h | h
  · subst h
    exact codeMat_mem_actionW_of_witness hp6_wit0 hp6_act0
  · subst h
    exact codeMat_mem_actionW_of_witness hp6_wit1 hp6_act1
  · subst h
    exact codeMat_mem_actionW_of_witness hp6_wit2 hp6_act2

theorem affineHyperplane6_lb17_from_hp2
    (h416 : QuotientRankAtLeast affineHyperplane2 17) :
    QuotientRankAtLeast affineHyperplane6 17 := by
  letI := hp6_hP
  letI := hp6_hQ
  have h_act : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) affineHyperplane2) 17 :=
    @quotientRankAtLeast_action _ _ hp6_hP hp6_hQ _ _ h416
  exact quotientRankAtLeast_mono' hp6_contain h_act

-- ============================================================
-- affineHyperplane7 from affineHyperplane2 via GL transport
-- ============================================================

private noncomputable def hp7_hP : Invertible (codeMat 169 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private noncomputable def hp7_hQ : Invertible (codeMat 161 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private theorem hp7_hQtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp7_wit0 :
    codeMat 272 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 272 (by decide)

private theorem hp7_act0 :
    actionA (codeMat 169) (codeMat 161) (codeMat 272) = codeMat 276 := by
  unfold actionA
  rw [hp7_hQtInv]
  show (codeMat 169 : Mat3).transpose * codeMat 272 * (codeMat 161 : Mat3).transpose = codeMat 276
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp7_wit1 :
    codeMat 4 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 4 (by decide)

private theorem hp7_act1 :
    actionA (codeMat 169) (codeMat 161) (codeMat 4) = codeMat 2 := by
  unfold actionA
  rw [hp7_hQtInv]
  show (codeMat 169 : Mat3).transpose * codeMat 4 * (codeMat 161 : Mat3).transpose = codeMat 2
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp7_wit2 :
    codeMat 1 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 1 (by decide)

private theorem hp7_act2 :
    actionA (codeMat 169) (codeMat 161) (codeMat 1) = codeMat 1 := by
  unfold actionA
  rw [hp7_hQtInv]
  show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp7_contain :
    affineHyperplane7 ≤ actionW (codeMat 169) (codeMat 161) affineHyperplane2 := by
  letI := hp7_hP
  letI := hp7_hQ
  apply Submodule.span_le.mpr
  rintro M ⟨k, hk, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with h | h | h
  · subst h
    exact codeMat_mem_actionW_of_witness hp7_wit0 hp7_act0
  · subst h
    exact codeMat_mem_actionW_of_witness hp7_wit1 hp7_act1
  · subst h
    exact codeMat_mem_actionW_of_witness hp7_wit2 hp7_act2

theorem affineHyperplane7_lb17_from_hp2
    (h416 : QuotientRankAtLeast affineHyperplane2 17) :
    QuotientRankAtLeast affineHyperplane7 17 := by
  letI := hp7_hP
  letI := hp7_hQ
  have h_act : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 161) affineHyperplane2) 17 :=
    @quotientRankAtLeast_action _ _ hp7_hP hp7_hQ _ _ h416
  exact quotientRankAtLeast_mono' hp7_contain h_act

-- ============================================================
-- affineHyperplane8 from affineHyperplane2 via GL transport
-- ============================================================

private noncomputable def hp8_hP : Invertible (codeMat 161 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private noncomputable def hp8_hQ : Invertible (codeMat 169 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private theorem hp8_hQtInv :
    (codeMat 169 : Mat3).transpose⁻¹ = (codeMat 225 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 169 : Mat3).transpose * (codeMat 225 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp8_wit0 :
    codeMat 272 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 272 (by decide)

private theorem hp8_act0 :
    actionA (codeMat 161) (codeMat 169) (codeMat 272) = codeMat 272 := by
  unfold actionA
  rw [hp8_hQtInv]
  show (codeMat 161 : Mat3).transpose * codeMat 272 * (codeMat 225 : Mat3).transpose = codeMat 272
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp8_wit1 :
    codeMat 1 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 1 (by decide)

private theorem hp8_act1 :
    actionA (codeMat 161) (codeMat 169) (codeMat 1) = codeMat 5 := by
  unfold actionA
  rw [hp8_hQtInv]
  show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 225 : Mat3).transpose = codeMat 5
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp8_wit2 :
    codeMat 4 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 4 (by decide)

private theorem hp8_act2 :
    actionA (codeMat 161) (codeMat 169) (codeMat 4) = codeMat 2 := by
  unfold actionA
  rw [hp8_hQtInv]
  show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 225 : Mat3).transpose = codeMat 2
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp8_contain :
    affineHyperplane8 ≤ actionW (codeMat 161) (codeMat 169) affineHyperplane2 := by
  letI := hp8_hP
  letI := hp8_hQ
  apply Submodule.span_le.mpr
  rintro M ⟨k, hk, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with h | h | h
  · subst h
    exact codeMat_mem_actionW_of_witness hp8_wit0 hp8_act0
  · subst h
    exact codeMat_mem_actionW_of_witness hp8_wit1 hp8_act1
  · subst h
    exact codeMat_mem_actionW_of_witness hp8_wit2 hp8_act2

theorem affineHyperplane8_lb17_from_hp2
    (h416 : QuotientRankAtLeast affineHyperplane2 17) :
    QuotientRankAtLeast affineHyperplane8 17 := by
  letI := hp8_hP
  letI := hp8_hQ
  have h_act : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 169) affineHyperplane2) 17 :=
    @quotientRankAtLeast_action _ _ hp8_hP hp8_hQ _ _ h416
  exact quotientRankAtLeast_mono' hp8_contain h_act

-- ============================================================
-- affineHyperplane9 from affineHyperplane2 via GL transport
-- ============================================================

private noncomputable def hp9_hP : Invertible (codeMat 169 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private noncomputable def hp9_hQ : Invertible (codeMat 169 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private theorem hp9_hQtInv :
    (codeMat 169 : Mat3).transpose⁻¹ = (codeMat 225 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 169 : Mat3).transpose * (codeMat 225 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp9_wit0 :
    codeMat 273 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 273 (by decide)

private theorem hp9_act0 :
    actionA (codeMat 169) (codeMat 169) (codeMat 273) = codeMat 273 := by
  unfold actionA
  rw [hp9_hQtInv]
  show (codeMat 169 : Mat3).transpose * codeMat 273 * (codeMat 225 : Mat3).transpose = codeMat 273
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp9_wit1 :
    codeMat 1 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 1 (by decide)

private theorem hp9_act1 :
    actionA (codeMat 169) (codeMat 169) (codeMat 1) = codeMat 5 := by
  unfold actionA
  rw [hp9_hQtInv]
  show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 225 : Mat3).transpose = codeMat 5
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp9_wit2 :
    codeMat 4 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 4 (by decide)

private theorem hp9_act2 :
    actionA (codeMat 169) (codeMat 169) (codeMat 4) = codeMat 2 := by
  unfold actionA
  rw [hp9_hQtInv]
  show (codeMat 169 : Mat3).transpose * codeMat 4 * (codeMat 225 : Mat3).transpose = codeMat 2
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp9_contain :
    affineHyperplane9 ≤ actionW (codeMat 169) (codeMat 169) affineHyperplane2 := by
  letI := hp9_hP
  letI := hp9_hQ
  apply Submodule.span_le.mpr
  rintro M ⟨k, hk, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with h | h | h
  · subst h
    exact codeMat_mem_actionW_of_witness hp9_wit0 hp9_act0
  · subst h
    exact codeMat_mem_actionW_of_witness hp9_wit1 hp9_act1
  · subst h
    exact codeMat_mem_actionW_of_witness hp9_wit2 hp9_act2

theorem affineHyperplane9_lb17_from_hp2
    (h416 : QuotientRankAtLeast affineHyperplane2 17) :
    QuotientRankAtLeast affineHyperplane9 17 := by
  letI := hp9_hP
  letI := hp9_hQ
  have h_act : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 169) affineHyperplane2) 17 :=
    @quotientRankAtLeast_action _ _ hp9_hP hp9_hQ _ _ h416
  exact quotientRankAtLeast_mono' hp9_contain h_act

-- ============================================================
-- affineHyperplane10 from affineHyperplane2 via GL transport
-- ============================================================

private noncomputable def hp10_hP : Invertible (codeMat 177 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private noncomputable def hp10_hQ : Invertible (codeMat 177 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private theorem hp10_hQtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp10_wit0 :
    codeMat 272 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 272 (by decide)

private theorem hp10_act0 :
    actionA (codeMat 177) (codeMat 177) (codeMat 272) = codeMat 272 := by
  unfold actionA
  rw [hp10_hQtInv]
  show (codeMat 177 : Mat3).transpose * codeMat 272 * (codeMat 417 : Mat3).transpose = codeMat 272
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp10_wit1 :
    codeMat 4 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 4 (by decide)

private theorem hp10_act1 :
    actionA (codeMat 177) (codeMat 177) (codeMat 4) = codeMat 6 := by
  unfold actionA
  rw [hp10_hQtInv]
  show (codeMat 177 : Mat3).transpose * codeMat 4 * (codeMat 417 : Mat3).transpose = codeMat 6
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp10_wit2 :
    codeMat 1 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 1 (by decide)

private theorem hp10_act2 :
    actionA (codeMat 177) (codeMat 177) (codeMat 1) = codeMat 1 := by
  unfold actionA
  rw [hp10_hQtInv]
  show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 417 : Mat3).transpose = codeMat 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp10_contain :
    affineHyperplane10 ≤ actionW (codeMat 177) (codeMat 177) affineHyperplane2 := by
  letI := hp10_hP
  letI := hp10_hQ
  apply Submodule.span_le.mpr
  rintro M ⟨k, hk, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with h | h | h
  · subst h
    exact codeMat_mem_actionW_of_witness hp10_wit0 hp10_act0
  · subst h
    exact codeMat_mem_actionW_of_witness hp10_wit1 hp10_act1
  · subst h
    exact codeMat_mem_actionW_of_witness hp10_wit2 hp10_act2

theorem affineHyperplane10_lb17_from_hp2
    (h416 : QuotientRankAtLeast affineHyperplane2 17) :
    QuotientRankAtLeast affineHyperplane10 17 := by
  letI := hp10_hP
  letI := hp10_hQ
  have h_act : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 177) affineHyperplane2) 17 :=
    @quotientRankAtLeast_action _ _ hp10_hP hp10_hQ _ _ h416
  exact quotientRankAtLeast_mono' hp10_contain h_act

-- ============================================================
-- affineHyperplane11 from affineHyperplane2 via GL transport
-- ============================================================

private noncomputable def hp11_hP : Invertible (codeMat 185 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private noncomputable def hp11_hQ : Invertible (codeMat 177 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private theorem hp11_hQtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp11_wit0 :
    codeMat 276 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 276 (by decide)

private theorem hp11_act0 :
    actionA (codeMat 185) (codeMat 177) (codeMat 276) = codeMat 274 := by
  unfold actionA
  rw [hp11_hQtInv]
  show (codeMat 185 : Mat3).transpose * codeMat 276 * (codeMat 417 : Mat3).transpose = codeMat 274
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp11_wit1 :
    codeMat 4 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 4 (by decide)

private theorem hp11_act1 :
    actionA (codeMat 185) (codeMat 177) (codeMat 4) = codeMat 6 := by
  unfold actionA
  rw [hp11_hQtInv]
  show (codeMat 185 : Mat3).transpose * codeMat 4 * (codeMat 417 : Mat3).transpose = codeMat 6
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp11_wit2 :
    codeMat 1 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 1 (by decide)

private theorem hp11_act2 :
    actionA (codeMat 185) (codeMat 177) (codeMat 1) = codeMat 1 := by
  unfold actionA
  rw [hp11_hQtInv]
  show (codeMat 185 : Mat3).transpose * codeMat 1 * (codeMat 417 : Mat3).transpose = codeMat 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp11_contain :
    affineHyperplane11 ≤ actionW (codeMat 185) (codeMat 177) affineHyperplane2 := by
  letI := hp11_hP
  letI := hp11_hQ
  apply Submodule.span_le.mpr
  rintro M ⟨k, hk, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with h | h | h
  · subst h
    exact codeMat_mem_actionW_of_witness hp11_wit0 hp11_act0
  · subst h
    exact codeMat_mem_actionW_of_witness hp11_wit1 hp11_act1
  · subst h
    exact codeMat_mem_actionW_of_witness hp11_wit2 hp11_act2

theorem affineHyperplane11_lb17_from_hp2
    (h416 : QuotientRankAtLeast affineHyperplane2 17) :
    QuotientRankAtLeast affineHyperplane11 17 := by
  letI := hp11_hP
  letI := hp11_hQ
  have h_act : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 177) affineHyperplane2) 17 :=
    @quotientRankAtLeast_action _ _ hp11_hP hp11_hQ _ _ h416
  exact quotientRankAtLeast_mono' hp11_contain h_act

-- ============================================================
-- affineHyperplane12 from affineHyperplane2 via GL transport
-- ============================================================

private noncomputable def hp12_hP : Invertible (codeMat 177 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private noncomputable def hp12_hQ : Invertible (codeMat 185 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private theorem hp12_hQtInv :
    (codeMat 185 : Mat3).transpose⁻¹ = (codeMat 481 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 185 : Mat3).transpose * (codeMat 481 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp12_wit0 :
    codeMat 272 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 272 (by decide)

private theorem hp12_act0 :
    actionA (codeMat 177) (codeMat 185) (codeMat 272) = codeMat 272 := by
  unfold actionA
  rw [hp12_hQtInv]
  show (codeMat 177 : Mat3).transpose * codeMat 272 * (codeMat 481 : Mat3).transpose = codeMat 272
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp12_wit1 :
    codeMat 1 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 1 (by decide)

private theorem hp12_act1 :
    actionA (codeMat 177) (codeMat 185) (codeMat 1) = codeMat 5 := by
  unfold actionA
  rw [hp12_hQtInv]
  show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 481 : Mat3).transpose = codeMat 5
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp12_wit2 :
    codeMat 5 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 5 (by decide)

private theorem hp12_act2 :
    actionA (codeMat 177) (codeMat 185) (codeMat 5) = codeMat 3 := by
  unfold actionA
  rw [hp12_hQtInv]
  show (codeMat 177 : Mat3).transpose * codeMat 5 * (codeMat 481 : Mat3).transpose = codeMat 3
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp12_contain :
    affineHyperplane12 ≤ actionW (codeMat 177) (codeMat 185) affineHyperplane2 := by
  letI := hp12_hP
  letI := hp12_hQ
  apply Submodule.span_le.mpr
  rintro M ⟨k, hk, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with h | h | h
  · subst h
    exact codeMat_mem_actionW_of_witness hp12_wit0 hp12_act0
  · subst h
    exact codeMat_mem_actionW_of_witness hp12_wit1 hp12_act1
  · subst h
    exact codeMat_mem_actionW_of_witness hp12_wit2 hp12_act2

theorem affineHyperplane12_lb17_from_hp2
    (h416 : QuotientRankAtLeast affineHyperplane2 17) :
    QuotientRankAtLeast affineHyperplane12 17 := by
  letI := hp12_hP
  letI := hp12_hQ
  have h_act : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 185) affineHyperplane2) 17 :=
    @quotientRankAtLeast_action _ _ hp12_hP hp12_hQ _ _ h416
  exact quotientRankAtLeast_mono' hp12_contain h_act

-- ============================================================
-- affineHyperplane13 from affineHyperplane2 via GL transport
-- ============================================================

private noncomputable def hp13_hP : Invertible (codeMat 185 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private noncomputable def hp13_hQ : Invertible (codeMat 185 : Mat3) :=
  Matrix.invertibleOfIsUnitDet _ (by decide)

private theorem hp13_hQtInv :
    (codeMat 185 : Mat3).transpose⁻¹ = (codeMat 481 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 185 : Mat3).transpose * (codeMat 481 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp13_wit0 :
    codeMat 273 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 273 (by decide)

private theorem hp13_act0 :
    actionA (codeMat 185) (codeMat 185) (codeMat 273) = codeMat 273 := by
  unfold actionA
  rw [hp13_hQtInv]
  show (codeMat 185 : Mat3).transpose * codeMat 273 * (codeMat 481 : Mat3).transpose = codeMat 273
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp13_wit1 :
    codeMat 1 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 1 (by decide)

private theorem hp13_act1 :
    actionA (codeMat 185) (codeMat 185) (codeMat 1) = codeMat 5 := by
  unfold actionA
  rw [hp13_hQtInv]
  show (codeMat 185 : Mat3).transpose * codeMat 1 * (codeMat 481 : Mat3).transpose = codeMat 5
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp13_wit2 :
    codeMat 5 ∈ (affineHyperplane2 : Submodule F2 Mat3) :=
  spanContainsCode_implies_mem_spanCodes [272, 4, 1] 5 (by decide)

private theorem hp13_act2 :
    actionA (codeMat 185) (codeMat 185) (codeMat 5) = codeMat 3 := by
  unfold actionA
  rw [hp13_hQtInv]
  show (codeMat 185 : Mat3).transpose * codeMat 5 * (codeMat 481 : Mat3).transpose = codeMat 3
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem hp13_contain :
    affineHyperplane13 ≤ actionW (codeMat 185) (codeMat 185) affineHyperplane2 := by
  letI := hp13_hP
  letI := hp13_hQ
  apply Submodule.span_le.mpr
  rintro M ⟨k, hk, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with h | h | h
  · subst h
    exact codeMat_mem_actionW_of_witness hp13_wit0 hp13_act0
  · subst h
    exact codeMat_mem_actionW_of_witness hp13_wit1 hp13_act1
  · subst h
    exact codeMat_mem_actionW_of_witness hp13_wit2 hp13_act2

theorem affineHyperplane13_lb17_from_hp2
    (h416 : QuotientRankAtLeast affineHyperplane2 17) :
    QuotientRankAtLeast affineHyperplane13 17 := by
  letI := hp13_hP
  letI := hp13_hQ
  have h_act : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 185) affineHyperplane2) 17 :=
    @quotientRankAtLeast_action _ _ hp13_hP hp13_hQ _ _ h416
  exact quotientRankAtLeast_mono' hp13_contain h_act

-- ============================================================
-- Main reducer: twelve hypotheses → FinitePremises
-- ============================================================

private theorem affineHyperplane_lb17_all
    (h414 : QuotientRankAtLeast affineHyperplane0 17)
    (h415 : QuotientRankAtLeast affineHyperplane1 17)
    (h416 : QuotientRankAtLeast affineHyperplane2 17) :
    ∀ i : Fin 14, QuotientRankAtLeast (affineHyperplane i) 17 := by
  intro ⟨i, hi⟩
  interval_cases i
  · exact h414
  · exact h415
  · exact h416
  · exact affineHyperplane3_lb17_from_hp2 h416
  · exact affineHyperplane4_lb17_from_hp2 h416
  · exact affineHyperplane5_lb17_from_hp2 h416
  · exact affineHyperplane6_lb17_from_hp2 h416
  · exact affineHyperplane7_lb17_from_hp2 h416
  · exact affineHyperplane8_lb17_from_hp2 h416
  · exact affineHyperplane9_lb17_from_hp2 h416
  · exact affineHyperplane10_lb17_from_hp2 h416
  · exact affineHyperplane11_lb17_from_hp2 h416
  · exact affineHyperplane12_lb17_from_hp2 h416
  · exact affineHyperplane13_lb17_from_hp2 h416

/-- Legacy reducer kept for comparison: it derives the rank-one line bound from
    `plane479@19`.  This theorem is not the intended sink surface for the final
    finite formalization because `plane479@19` is not one of the certified
    all-high plane raises. -/
theorem FinitePremises_of_orbit_theorems_legacy
    (h479 : QuotientRankAtLeast plane479 19)
    (h484 : QuotientRankAtLeast plane484 19)
    (h485 : QuotientRankAtLeast plane485 19)
    (h486 : QuotientRankAtLeast plane486 19)
    (h487 : QuotientRankAtLeast plane487 19)
    (h488 : QuotientRankAtLeast plane488 19)
    (h489 : QuotientRankAtLeast plane489 19)
    (h490 : QuotientRankAtLeast plane490 19)
    (h491 : QuotientRankAtLeast plane491 19)
    (h414 : QuotientRankAtLeast affineHyperplane0 17)
    (h415 : QuotientRankAtLeast affineHyperplane1 17)
    (h416 : QuotientRankAtLeast affineHyperplane2 17) :
    FinitePremises := {
  line_rank1_lb19 := lineRank1_lb19_from_plane479 h479,
  line_rank2_lb19 := lineRank2_lb19_from_plane484 h484,
  line_rank3_lb19 := lineRank3_lb19_from_plane488 h488,
  plane484_lb19 := h484,
  plane485_lb19 := h485,
  plane486_lb19 := h486,
  plane487_lb19 := h487,
  plane488_lb19 := h488,
  plane489_lb19 := h489,
  plane490_lb19 := h490,
  plane491_lb19 := h491,
  affine_hyperplane_lb17 := affineHyperplane_lb17_all h414 h415 h416,
}

/-- Corrected finite reducer: the rank-one line lower bound is supplied directly,
    while the eight all-high plane sinks and three affine hyperplane sinks fill
    the remaining finite premises.  No `plane479@19` hypothesis is used here. -/
theorem FinitePremises_of_orbit_theorems
    (hLine1 : QuotientRankAtLeast lineRank1 19)
    (h484 : QuotientRankAtLeast plane484 19)
    (h485 : QuotientRankAtLeast plane485 19)
    (h486 : QuotientRankAtLeast plane486 19)
    (h487 : QuotientRankAtLeast plane487 19)
    (h488 : QuotientRankAtLeast plane488 19)
    (h489 : QuotientRankAtLeast plane489 19)
    (h490 : QuotientRankAtLeast plane490 19)
    (h491 : QuotientRankAtLeast plane491 19)
    (h414 : QuotientRankAtLeast affineHyperplane0 17)
    (h415 : QuotientRankAtLeast affineHyperplane1 17)
    (h416 : QuotientRankAtLeast affineHyperplane2 17) :
    FinitePremises := {
  line_rank1_lb19 := hLine1,
  line_rank2_lb19 := lineRank2_lb19_from_plane484 h484,
  line_rank3_lb19 := lineRank3_lb19_from_plane488 h488,
  plane484_lb19 := h484,
  plane485_lb19 := h485,
  plane486_lb19 := h486,
  plane487_lb19 := h487,
  plane488_lb19 := h488,
  plane489_lb19 := h489,
  plane490_lb19 := h490,
  plane491_lb19 := h491,
  affine_hyperplane_lb17 := affineHyperplane_lb17_all h414 h415 h416,
}

end QiushiMatmul
end
