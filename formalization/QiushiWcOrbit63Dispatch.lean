import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit63Consumer
import QiushiOrbit10FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc63_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc63_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc63s0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc63s0_contain :
    (o63SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 266) orbit10W := by
  change spanCodes [256, 160, 68, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 266) orbit10W
  apply step109wc63_spanCodes_le_of_gens [256, 160, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 266) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc63s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc63s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc63s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc63s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step109wc63s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc63s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc63s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact

theorem step109wc63s0Dispatch :
    QuotientRankAtLeast (o63SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc63s0_contain hAct


private theorem step109wc63s1_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc63s1_contain :
    (o63SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 140) (codeMat 140) orbit10W := by
  change spanCodes [256, 160, 64, 16, 10, 4, 1] ≤ actionW (codeMat 140) (codeMat 140) orbit10W
  apply step109wc63_spanCodes_le_of_gens [256, 160, 64, 16, 10, 4, 1]
    (actionW (codeMat 140) (codeMat 140) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc63s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc63s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 68 * (codeMat 98 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step109wc63s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step109wc63s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc63s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 8) = codeMat 4 := by
      unfold actionA
      rw [step109wc63s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc63s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact

theorem step109wc63s1Dispatch :
    QuotientRankAtLeast (o63SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 140) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 140) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc63s1_contain hAct


private theorem step109wc63s2_QtInv :
    (codeMat 396 : Mat3).transpose⁻¹ = (codeMat 106 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 396 : Mat3).transpose * (codeMat 106 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc63s2_contain :
    (o63SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 142) (codeMat 396) orbit10W := by
  change spanCodes [256, 160, 66, 16, 10, 6, 1] ≤ actionW (codeMat 142) (codeMat 396) orbit10W
  apply step109wc63_spanCodes_le_of_gens [256, 160, 66, 16, 10, 6, 1]
    (actionW (codeMat 142) (codeMat 396) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 325) = codeMat 256 := by
      unfold actionA
      rw [step109wc63s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 325 * (codeMat 106 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc63s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 68 * (codeMat 106 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 162 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 162 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 162) = codeMat 66 := by
      unfold actionA
      rw [step109wc63s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 162 * (codeMat 106 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step109wc63s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 256 * (codeMat 106 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc63s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 160 * (codeMat 106 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 8) = codeMat 6 := by
      unfold actionA
      rw [step109wc63s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 106 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc63s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 106 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact

theorem step109wc63s2Dispatch :
    QuotientRankAtLeast (o63SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 396) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 396) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc63s2_contain hAct


private theorem step109wc63s3_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc63s3_contain :
    (o63SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 84) (codeMat 84) orbit10W := by
  change spanCodes [256, 128, 68, 32, 16, 10, 1] ≤ actionW (codeMat 84) (codeMat 84) orbit10W
  apply step109wc63_spanCodes_le_of_gens [256, 128, 68, 32, 16, 10, 1]
    (actionW (codeMat 84) (codeMat 84) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc63s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc63s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc63s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc63s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc63s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc63s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc63s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact

theorem step109wc63s3Dispatch :
    QuotientRankAtLeast (o63SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc63s3_contain hAct


private theorem step109wc63s4_QtInv :
    (codeMat 340 : Mat3).transpose⁻¹ = (codeMat 85 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 340 : Mat3).transpose * (codeMat 85 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc63s4_contain :
    (o63SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 85) (codeMat 340) orbit10W := by
  change spanCodes [256, 130, 68, 34, 16, 10, 1] ≤ actionW (codeMat 85) (codeMat 340) orbit10W
  apply step109wc63_spanCodes_le_of_gens [256, 130, 68, 34, 16, 10, 1]
    (actionW (codeMat 85) (codeMat 340) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 85) (codeMat 340) (codeMat 325) = codeMat 256 := by
      unfold actionA
      rw [step109wc63s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 325 * (codeMat 85 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 85) (codeMat 340) (codeMat 2) = codeMat 130 := by
      unfold actionA
      rw [step109wc63s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 2 * (codeMat 85 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 85) (codeMat 340) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc63s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 68 * (codeMat 85 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 168 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 168 (by decide)
    have hact : actionA (codeMat 85) (codeMat 340) (codeMat 168) = codeMat 34 := by
      unfold actionA
      rw [step109wc63s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 168 * (codeMat 85 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 85) (codeMat 340) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc63s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 16 * (codeMat 85 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 85) (codeMat 340) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc63s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 160 * (codeMat 85 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 340) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc63s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 85 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact

theorem step109wc63s4Dispatch :
    QuotientRankAtLeast (o63SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 340 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 340) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 340) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc63s4_contain hAct


private theorem step109wc63s5_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc63s5_contain :
    (o63SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 92) (codeMat 212) orbit10W := by
  change spanCodes [256, 132, 68, 36, 16, 10, 1] ≤ actionW (codeMat 92) (codeMat 212) orbit10W
  apply step109wc63_spanCodes_le_of_gens [256, 132, 68, 36, 16, 10, 1]
    (actionW (codeMat 92) (codeMat 212) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc63s5_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 70 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 70) = codeMat 132 := by
      unfold actionA
      rw [step109wc63s5_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 70 * (codeMat 86 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc63s5_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 68 * (codeMat 86 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 8) = codeMat 36 := by
      unfold actionA
      rw [step109wc63s5_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 432) = codeMat 16 := by
      unfold actionA
      rw [step109wc63s5_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 432 * (codeMat 86 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc63s5_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 160 * (codeMat 86 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc63s5_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 256 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact

theorem step109wc63s5Dispatch :
    QuotientRankAtLeast (o63SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 212) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 212) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc63s5_contain hAct


private theorem step109wc63s6_QtInv :
    (codeMat 468 : Mat3).transpose⁻¹ = (codeMat 87 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 468 : Mat3).transpose * (codeMat 87 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc63s6_contain :
    (o63SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 93) (codeMat 468) orbit10W := by
  change spanCodes [256, 134, 68, 38, 16, 10, 1] ≤ actionW (codeMat 93) (codeMat 468) orbit10W
  apply step109wc63_spanCodes_le_of_gens [256, 134, 68, 38, 16, 10, 1]
    (actionW (codeMat 93) (codeMat 468) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 93) (codeMat 468) (codeMat 325) = codeMat 256 := by
      unfold actionA
      rw [step109wc63s6_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 325 * (codeMat 87 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 326 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 326 (by decide)
    have hact : actionA (codeMat 93) (codeMat 468) (codeMat 326) = codeMat 134 := by
      unfold actionA
      rw [step109wc63s6_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 326 * (codeMat 87 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 93) (codeMat 468) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc63s6_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 68 * (codeMat 87 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 424 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 424 (by decide)
    have hact : actionA (codeMat 93) (codeMat 468) (codeMat 424) = codeMat 38 := by
      unfold actionA
      rw [step109wc63s6_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 424 * (codeMat 87 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 93) (codeMat 468) (codeMat 432) = codeMat 16 := by
      unfold actionA
      rw [step109wc63s6_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 432 * (codeMat 87 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 93) (codeMat 468) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc63s6_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 160 * (codeMat 87 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 93) (codeMat 468) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc63s6_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 256 * (codeMat 87 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc63_codeMat_mem_actionW_of_witness hw hact

theorem step109wc63s6Dispatch :
    QuotientRankAtLeast (o63SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 468 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 468) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 468) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc63s6_contain hAct

theorem step109wc63_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o63SourceU_wc i) (o63SourceLb_wc i) := by
  fin_cases i
  · exact step109wc63s0Dispatch
  · exact step109wc63s1Dispatch
  · exact step109wc63s2Dispatch
  · exact step109wc63s3Dispatch
  · exact step109wc63s4Dispatch
  · exact step109wc63s5Dispatch
  · exact step109wc63s6Dispatch

theorem step109_orbit63_lb14_wc : QuotientRankAtLeast o63W_wc 14 :=
  o63Lb14_wc step109wc63_all_dispatch

end QiushiMatmul
